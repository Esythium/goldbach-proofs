import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
This reduction uses the uniform prime-sum estimate in Friedlander and Goldston,
Sums of Three or More Primes, p. 290, formula (1.15), as an explicit hypothesis.
-/

namespace DeepThreeQuarters

noncomputable def cutoff (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊

noncomputable def width (n : ℕ) : ℕ := 256 * cutoff n * (Nat.log 2 (n+2)) ^ 2

noncomputable def wideArcs (n : ℕ) : Set ℝ := {t | ∃ q a : ℕ,
  1 ≤ q ∧ q ≤ cutoff n ∧ a ≤ q ∧ a.Coprime q ∧
  |t - (a : ℝ) / q| ≤ (width n : ℝ) / ((q : ℝ) * n)}

noncomputable def B (n q : ℕ) (β : ℝ) : ℝ := max (q : ℝ) ((q : ℝ) * n * |β|)

/-- Dirichlet approximation at the exact real scale `sqrt n`, including the two
endpoint fractions of the unit interval. -/
theorem exists_dirichlet (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    ∃ a q : ℕ, 1 ≤ q ∧ a ≤ q ∧ a.Coprime q ∧ (q : ℝ) ≤ Real.sqrt n ∧
      |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * Real.sqrt n) := by
  let K := ⌊Real.sqrt n⌋₊
  have hs : 1 ≤ Real.sqrt n := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ n by exact_mod_cast hn)
  have hK : 1 ≤ K := Nat.le_floor (by simpa using hs)
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hfloor : Real.sqrt n ≤ (K : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  obtain ⟨r, happrox, hr⟩ := Real.exists_rat_abs_sub_le_and_den_le t hK
  have hd : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.den_pos
  have hscaled : |t * r.den - r.num| ≤ 1 / ((K : ℝ) + 1) := by
    rw [Rat.cast_def, ← div_div, le_div_iff₀ hd] at happrox
    rwa [← abs_of_pos hd, ← abs_mul, sub_mul, abs_of_pos hd, div_mul_cancel₀ _ hd.ne'] at happrox
  have hnear : |t * r.den - r.num| < 1 := hscaled.trans_lt <| by
    apply (div_lt_iff₀ (by positivity)).2
    linarith
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hnear
  have hreal₀ := mul_nonneg ht.1 hd.le
  have hreal₁ := mul_le_mul_of_nonneg_right ht.2 hd.le
  have hn₀ : -1 < r.num := by exact_mod_cast (show (-1:ℝ) < r.num by linarith)
  have hn₁ : r.num < (r.den : ℤ) + 1 := by
    exact_mod_cast (show (r.num:ℝ) < (r.den:ℝ) + 1 by linarith)
  have habs : (r.num.natAbs : ℤ) = r.num := Int.natAbs_of_nonneg (by omega)
  have ha : r.num.natAbs ≤ r.den := by omega
  refine ⟨r.num.natAbs, r.den, r.den_pos, ha, r.reduced, ?_, ?_⟩
  · exact (Nat.cast_le.mpr hr).trans (Nat.floor_le (Real.sqrt_nonneg _))
  · have hnR : (r.num.natAbs : ℝ) = r.num := by
      rw [Nat.cast_natAbs, abs_of_nonneg (show 0 ≤ r.num by omega)]
    rw [hnR, ← Rat.cast_def]
    apply happrox.trans
    apply one_div_le_one_div_of_le (mul_pos hd (by linarith))
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hfloor hd.le

/-- Effective heights of admissible approximants to points on the deep arcs. -/
theorem height_bounds {n q a : ℕ} {t : ℝ} (hn : 1 ≤ n) (hq : 1 ≤ q) (ha : a ≤ q)
    (hc : a.Coprime q) (hdeep : t ∉ wideArcs n) (hden : (q : ℝ) ≤ Real.sqrt n)
    (happrox : |t - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * Real.sqrt n)) :
    (n : ℝ) ^ (1/3 : ℝ) ≤ B n q (t - (a : ℝ) / q) ∧
      B n q (t - (a : ℝ) / q) ≤ Real.sqrt n := by
  have hq' : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
  constructor
  · by_cases hsmall : q ≤ cutoff n
    · have hout : (width n : ℝ) / ((q : ℝ) * n) < |t - (a : ℝ) / q| := by
        by_contra! hin
        exact hdeep ⟨q, a, hq, hsmall, ha, hc, hin⟩
      have hw : cutoff n + 1 ≤ width n := by
        have hQ : 1 ≤ (Nat.log 2 (n+2)) ^ 2 := by
          have h := Nat.log_pos (b:=2) (n:=n+2) (by decide) (by omega)
          exact Nat.one_le_pow _ _ h
        unfold width
        have := Nat.mul_le_mul_left (256 * cutoff n) hQ
        omega
      have hw' : (cutoff n : ℝ) + 1 ≤ width n := by exact_mod_cast hw
      apply le_trans ((Nat.lt_floor_add_one ((n : ℝ) ^ (1/3 : ℝ))).le.trans hw')
      exact (le_of_lt (by simpa [mul_comm] using (div_lt_iff₀ (mul_pos hq' hn')).mp hout)).trans
        (le_max_right _ _)
    · exact (Nat.lt_of_floor_lt (lt_of_not_ge hsmall)).le.trans (le_max_left _ _)
  · apply max_le hden
    have hmul := (le_div_iff₀ (mul_pos hq' hs)).mp happrox
    have hmul' := mul_le_mul_of_nonneg_right hmul hs.le
    calc
      (q : ℝ) * n * |t - (a : ℝ) / q| =
          (|t - (a : ℝ) / q| * ((q : ℝ) * Real.sqrt n)) * Real.sqrt n := by
        conv_lhs => rw [← Real.sq_sqrt hn'.le]
        ring
      _ ≤ Real.sqrt n := by simpa using hmul'

theorem exists_deep_approximation {n : ℕ} {t : ℝ} (hn : 1 ≤ n) (ht : t ∈ Set.Icc 0 1)
    (hdeep : t ∉ wideArcs n) : ∃ a q : ℕ, 1 ≤ q ∧ a ≤ q ∧ a.Coprime q ∧
      (q : ℝ) ≤ Real.sqrt n ∧ |t - (a : ℝ)/q| ≤ 1/((q : ℝ)*Real.sqrt n) ∧
      (n : ℝ) ^ (1/3 : ℝ) ≤ B n q (t - (a : ℝ)/q) ∧
      B n q (t - (a : ℝ)/q) ≤ Real.sqrt n := by
  obtain ⟨a,q,hq,ha,hc,hd,h⟩ := exists_dirichlet n hn t ht
  exact ⟨a,q,hq,ha,hc,hd,h,height_bounds hn hq ha hc hdeep hd h⟩

end DeepThreeQuarters

namespace DeepThreeQuarters

noncomputable def geometricPhase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

noncomputable def geometricSum (n : ℕ) (β : ℝ) : ℂ :=
  ∑ k ∈ Finset.range n, geometricPhase ((k : ℝ)*β)

noncomputable def positiveGeometricSum (n : ℕ) (β : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 n, geometricPhase ((k : ℝ)*β)

private theorem norm_geometricPhase (x : ℝ) : ‖geometricPhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem geometricPhase_pow (j : ℕ) (β : ℝ) :
    geometricPhase ((j : ℝ) * β) = geometricPhase β ^ j := by
  unfold geometricPhase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem norm_geometricSum_le (n : ℕ) (β : ℝ) : ‖geometricSum n β‖ ≤ n := by
  calc
    _ ≤ ∑ k ∈ Finset.range n, ‖geometricPhase ((k : ℝ)*β)‖ := norm_sum_le _ _
    _ = n := by simp [norm_geometricPhase]

/-- The chord bound and geometric-series argument specialize the proof of
`goldbach_geometric_sum_le_inv_twice_round_distance` in goldbach-proofs PR
2486 (revision f3613cf846dfb3e7fe7d04fe6ce51c6ee25e7d4f) to the central period.
The multiplicative estimate includes the offset zero. -/
theorem abs_mul_norm_geometricSum_le_half (n : ℕ) {β : ℝ} (hβ : |β| ≤ 1/2) :
    |β| * ‖geometricSum n β‖ ≤ 1/2 := by
  have harg : |Real.pi * β| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos, show Real.pi / 2 = Real.pi * (1 / 2) by ring]
    exact mul_le_mul_of_nonneg_left hβ Real.pi_pos.le
  have hsin : 2 * |β| ≤ |Real.sin (Real.pi * β)| := calc
    _ = 2 / Real.pi * |Real.pi * β| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp [Real.pi_pos.ne']
    _ ≤ _ := Real.mul_abs_le_abs_sin harg
  have hchord : 4 * |β| ≤ ‖geometricPhase β - 1‖ := by
    unfold geometricPhase
    rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one,
      show (2 * Real.pi * β) / 2 = Real.pi * β by ring, Real.norm_eq_abs, abs_mul]
    norm_num
    linarith
  have hprod : ‖geometricSum n β‖ * ‖geometricPhase β - 1‖ ≤ 2 := by
    unfold geometricSum
    simp_rw [geometricPhase_pow]
    rw [← norm_mul, geom_sum_mul]
    calc
      _ ≤ ‖geometricPhase β ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, norm_geometricPhase]
  linarith only [(mul_le_mul_of_nonneg_left hchord (norm_nonneg (geometricSum n β))).trans hprod]

theorem norm_positiveGeometricSum_eq (n : ℕ) (β : ℝ) :
    ‖positiveGeometricSum n β‖ = ‖geometricSum n β‖ := by
  have hshift : positiveGeometricSum n β = geometricSum n β * geometricPhase β := by
    unfold positiveGeometricSum geometricSum
    rw [Finset.sum_mul]
    symm
    refine Finset.sum_bij (fun j _ => j+1) ?_ ?_ ?_ ?_
    · intro j hj
      have := Finset.mem_range.mp hj
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i _ j _ hij
      omega
    · intro j hj
      obtain ⟨h₁,h₂⟩ := Finset.mem_Icc.mp hj
      exact ⟨j-1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro j _
      rw [geometricPhase_pow, geometricPhase_pow, pow_succ]
  rw [hshift, norm_mul, show ‖geometricPhase β‖ = 1 from Complex.norm_exp_ofReal_mul_I _, mul_one]

theorem geometricSum_mul_B_le {n q : ℕ} {β : ℝ} (hn : 4 ≤ n) (hq : 1 ≤ q)
    (hβ : |β| ≤ 1 / ((q : ℝ) * Real.sqrt n)) :
    ‖geometricSum n β‖ * B n q β ≤ (n : ℝ) * q := by
  have hs : 2 ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact_mod_cast hn
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : 2 ≤ (q : ℝ) * Real.sqrt n := by nlinarith [mul_nonneg (sub_nonneg.mpr hq') (Real.sqrt_nonneg n)]
  have hhalf := abs_mul_norm_geometricSum_le_half n
    (hβ.trans (one_div_le_one_div_of_le (by norm_num) hden))
  rw [B, mul_max_of_nonneg _ _ (norm_nonneg _)]
  refine max_le (mul_le_mul_of_nonneg_right (norm_geometricSum_le n β) (Nat.cast_nonneg q)) ?_
  have h := mul_le_mul_of_nonneg_left (hhalf.trans (by norm_num : (1/2:ℝ) ≤ 1))
    (show 0 ≤ (n:ℝ) * q by positivity)
  linarith only [h]

theorem positiveGeometricSum_mul_B_le {n q : ℕ} {β : ℝ} (hn : 4 ≤ n) (hq : 1 ≤ q)
    (hβ : |β| ≤ 1 / ((q : ℝ) * Real.sqrt n)) :
    ‖positiveGeometricSum n β‖ * B n q β ≤ (n : ℝ) * q := by
  rw [norm_positiveGeometricSum_eq]
  exact geometricSum_mul_B_le hn hq hβ

end DeepThreeQuarters

/-!
# Bounds for the reciprocal totient density

The finite-product argument and logarithmic bound below are the proof of the
private helpers `harm_prod` and `ratio_bound` from the accepted Goldbach Research
PR #1810 (TH-0073), https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/1810/files.
The logarithmic estimate is exposed here for reuse independently of that PR's
energy theorem. The power bounds are consequences for the deep minor arcs.
-/

namespace DeepThreeQuarters

private theorem harm_prod (s : Finset ℕ) :
    (∀ p ∈ s, 2 ≤ p) → ∏ p ∈ s, (p:ℝ) / ((p:ℝ) - 1) ≤ (s.card : ℝ) + 1 := by
  induction s using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s hlt ih =>
    intro h2
    have ha : a ∉ s := fun h => lt_irrefl _ (hlt a h)
    have ha2 : 2 ≤ a := h2 a (Finset.mem_insert_self _ _)
    have ih' := ih (fun p hp => h2 p (Finset.mem_insert_of_mem hp))
    have hsub : s ⊆ Finset.Ico 2 a := by
      intro x hx
      rw [Finset.mem_Ico]
      exact ⟨h2 x (Finset.mem_insert_of_mem hx), hlt x hx⟩
    have hk : s.card ≤ a - 2 := by
      have := Finset.card_le_card hsub
      simpa using this
    have hk' : (s.card : ℝ) + 2 ≤ a := by
      have : s.card + 2 ≤ a := by omega
      exact_mod_cast this
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    push_cast
    have ha' : (2:ℝ) ≤ a := by exact_mod_cast ha2
    have hpos : (0:ℝ) < (a:ℝ) - 1 := by linarith
    have hP : 0 ≤ ∏ p ∈ s, (p:ℝ) / ((p:ℝ) - 1) := by
      apply Finset.prod_nonneg
      intro p hp
      have : (2:ℝ) ≤ p := by exact_mod_cast h2 p (Finset.mem_insert_of_mem hp)
      apply div_nonneg <;> linarith
    have hfrac : (a:ℝ) / ((a:ℝ) - 1) * ((s.card : ℝ) + 1) ≤ (s.card : ℝ) + 1 + 1 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith [Nat.cast_nonneg (α := ℝ) s.card]
    calc (a:ℝ) / ((a:ℝ) - 1) * ∏ p ∈ s, (p:ℝ) / ((p:ℝ) - 1)
        ≤ (a:ℝ) / ((a:ℝ) - 1) * ((s.card : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left ih' (by positivity)
      _ ≤ _ := hfrac

theorem totient_ratio_le_four_log (q : ℕ) (hq : 0 < q) :
    (q:ℝ) / (q.totient : ℝ) ≤ 4 * Real.log ((q + 2 : ℕ) : ℝ) := by
  have hprime : ∀ p ∈ q.primeFactors, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hh := harm_prod q.primeFactors hprime
  have hid := Nat.totient_mul_prod_primeFactors q
  have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hP : (0:ℝ) < ∏ p ∈ q.primeFactors, (p:ℝ) := by
    apply Finset.prod_pos
    intro p hp
    have : (2:ℝ) ≤ p := by exact_mod_cast hprime p hp
    linarith
  have hP1 : (0:ℝ) < ∏ p ∈ q.primeFactors, ((p:ℝ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    have : (2:ℝ) ≤ p := by exact_mod_cast hprime p hp
    linarith
  have hid' : (q.totient : ℝ) * ∏ p ∈ q.primeFactors, (p:ℝ)
      = (q:ℝ) * ∏ p ∈ q.primeFactors, ((p:ℝ) - 1) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hid
    simp only [Nat.cast_mul, Nat.cast_prod] at this
    rw [this]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]
    simp
  have heq : (q:ℝ) / (q.totient : ℝ) = ∏ p ∈ q.primeFactors, (p:ℝ) / ((p:ℝ) - 1) := by
    rw [Finset.prod_div_distrib, div_eq_div_iff hφ.ne' hP1.ne']
    linarith
  have hpow : 2 ^ q.primeFactors.card ≤ q := by
    calc 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p :=
          Finset.pow_card_le_prod _ _ _ hprime
      _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hlog2 : (1:ℝ) / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    norm_num at this
    linarith
  have hk : (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log ((q + 2 : ℕ) : ℝ) := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    have : ((2 ^ q.primeFactors.card : ℕ) : ℝ) ≤ ((q + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 ^ q.primeFactors.card ≤ q + 2)
    simpa using this
  have hL : (1:ℝ) / 2 ≤ Real.log ((q + 2 : ℕ) : ℝ) := by
    refine hlog2.trans (Real.log_le_log (by norm_num) ?_)
    exact_mod_cast (by omega : 2 ≤ q + 2)
  have hc : (0:ℝ) ≤ q.primeFactors.card := Nat.cast_nonneg _
  rw [heq]
  have : (q.primeFactors.card : ℝ) * (1 / 2) ≤ q.primeFactors.card * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2 hc
  linarith

/-- A modulus-uniform bound for every positive exponent, with an explicit constant. -/
theorem totient_ratio_le_rpow {ε : ℝ} (hε : 0 < ε) (q : ℕ) (hq : 0 < q) :
    (q : ℝ) / (q.totient : ℝ) ≤ (8 + 4 / ε) * (q : ℝ) ^ ε := by
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpow : 1 ≤ (q : ℝ) ^ ε := Real.one_le_rpow hq₁ hε.le
  have hlog : Real.log ((q + 2 : ℕ) : ℝ) ≤ Real.log 3 + Real.log q := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  have hthree : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)]
  calc
    (q : ℝ) / (q.totient : ℝ) ≤ 4 * Real.log ((q + 2 : ℕ) : ℝ) :=
      totient_ratio_le_four_log q hq
    _ ≤ 8 + 4 * ((q : ℝ) ^ ε / ε) := by
      linarith [Real.log_natCast_le_rpow_div q hε]
    _ ≤ 8 * (q : ℝ) ^ ε + 4 * ((q : ℝ) ^ ε / ε) := by linarith
    _ = (8 + 4 / ε) * (q : ℝ) ^ ε := by ring

end DeepThreeQuarters

namespace DeepThreeQuarters

/-- Convert a geometric-sum estimate at a rational approximation into the
bound for its Möbius-weighted main term. -/
theorem rational_term_le {ε b : ℝ} {n q : ℕ} {z : ℂ} (hε : 0 < ε)
    (hq : 0 < q) (hqn : (q : ℝ) ≤ n) (hb : 0 < b)
    (hz : ‖z‖ * b ≤ (n : ℝ) * q) :
    ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * z‖ ≤
      (8 + 4/ε) * (n : ℝ) ^ ε * ((n : ℝ) / b) := by
  have hmu : ‖(ArithmeticFunction.moebius q : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hz' := (le_div_iff₀ hb).mpr hz
  have hratio := (totient_ratio_le_rpow hε q hq).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) hqn hε.le) (by positivity))
  calc
    _ = (‖(ArithmeticFunction.moebius q : ℂ)‖ / (q.totient : ℝ)) * ‖z‖ := by
      rw [norm_mul, norm_div, Complex.norm_natCast]
    _ ≤ (1 / (q.totient : ℝ)) * ((n : ℝ) * q / b) :=
      mul_le_mul (div_le_div_of_nonneg_right hmu hφ.le) hz' (norm_nonneg _) (by positivity)
    _ = ((q : ℝ) / (q.totient : ℝ)) * ((n : ℝ) / b) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hratio (by positivity)

end DeepThreeQuarters

open Filter

namespace DeepThreeQuarters

/-- Combine the rational main term with the error in its approximation. -/
theorem pointwise_budget {x B C ε : ℝ} (hx : 1 ≤ x) (hC : 0 ≤ C)
    (hlo : x ^ (1/3 : ℝ) ≤ B) (hhi : B ≤ Real.sqrt x)
    (P M : ℂ)
    (hmodel : ‖M‖ ≤ C * x ^ ε * (x / B))
    (herror : ‖P - M‖ ≤ C * x ^ ε * (Real.sqrt x * Real.sqrt B)) :
    ‖P‖ ≤ (2 * C) * x ^ (3/4 + ε) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hquarter : x / B ≤ x ^ (3/4 : ℝ) := by
    calc
      _ ≤ x / x ^ (1/3 : ℝ) :=
        div_le_div_of_nonneg_left hx0.le (Real.rpow_pos_of_pos hx0 _) hlo
      _ = x ^ (1 - 1/3 : ℝ) := by rw [Real.rpow_sub hx0, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have he : Real.sqrt x * Real.sqrt B ≤ x ^ (3/4 : ℝ) := by
    calc
      _ ≤ Real.sqrt x * Real.sqrt (Real.sqrt x) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hhi) (Real.sqrt_nonneg _)
      _ = _ := by
        simp only [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
        norm_num
  have hfac : 0 ≤ C * x ^ ε := mul_nonneg hC (Real.rpow_nonneg hx0.le _)
  have htriangle : ‖P‖ ≤ ‖P - M‖ + ‖M‖ := by
    calc
      ‖P‖ = ‖(P - M) + M‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hsum := htriangle.trans (add_le_add
    (herror.trans (mul_le_mul_of_nonneg_left he hfac))
    (hmodel.trans (mul_le_mul_of_nonneg_left hquarter hfac)))
  rw [Real.rpow_add hx0]
  linarith only [hsum]

/-- Absorb every fixed constant into the arbitrarily small power in the
registered conclusion. The threshold is uniform in the point on the arc. -/
theorem eventually_absorb (C η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ (3/4 + η/2) ≤ (n : ℝ) ^ (3/4 + η) := by
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (η/2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < η/2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop C, eventually_ge_atTop 1] with n hpow hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ (n : ℝ) ^ (η/2) * (n : ℝ) ^ (3/4 + η/2) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hn'.le _)
    _ = _ := by rw [← Real.rpow_add hn']; congr 1; ring

end DeepThreeQuarters

namespace DeepThreeQuarters

/-- Absorb the two logarithmic losses in the Friedlander–Goldston (1.15)
error term. The constant is independent of the modulus and frequency. -/
private theorem log_product_bound {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) :
    Real.log x * (Real.log x + 1) ≤ ((2 / ε)^2 + 1 / ε) * x ^ ε := by
  have hx' : 0 < x := zero_lt_one.trans_le hx
  have hlog := Real.log_nonneg hx
  have hhalf := Real.log_le_rpow_div hx'.le (half_pos hε)
  have hsq := mul_self_le_mul_self hlog hhalf
  have hp : x ^ (ε / 2) * x ^ (ε / 2) = x ^ ε := by
    rw [← Real.rpow_add hx', add_halves]
  have hsq' : Real.log x * Real.log x ≤ (2 / ε)^2 * x ^ ε := by
    calc
      _ ≤ (x ^ (ε / 2) / (ε/2)) * (x ^ (ε / 2) / (ε/2)) := hsq
      _ = (2 / ε)^2 * (x ^ (ε / 2) * x ^ (ε / 2)) := by ring
      _ = _ := by rw [hp]
  calc
    _ = Real.log x * Real.log x + Real.log x := by ring
    _ ≤ (2 / ε)^2 * x ^ ε + x ^ ε / ε := add_le_add hsq' (Real.log_le_rpow_div hx'.le hε)
    _ = _ := by ring

/-- Normalization of the numerical error term in Friedlander–Goldston (1.15).
This estimate holds for every frequency offset and modulus as soon as n ≥ 1.
The analytic assertion (1.15) itself is a separate input. -/
theorem friedlanderGoldston_error_normalize {ε : ℝ} (hε : 0 < ε)
    (n q : ℕ) (β : ℝ) (hn : 1 ≤ n) :
    Real.sqrt ((q : ℝ) * n) * Real.log n * (Real.log n + Real.sqrt (n * |β|)) ≤
      ((2 / ε)^2 + 1 / ε) * (n : ℝ)^ε * (Real.sqrt n * Real.sqrt (B n q β)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_nonneg hn'
  have hq : Real.sqrt q ≤ Real.sqrt (B n q β) := Real.sqrt_le_sqrt (le_max_left _ _)
  have hshift : Real.sqrt q * Real.sqrt (n * |β|) ≤ Real.sqrt (B n q β) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg q)]
    apply Real.sqrt_le_sqrt
    rw [← mul_assoc]
    exact le_max_right _ _
  have hsum :
      Real.sqrt q * (Real.log n + Real.sqrt (n * |β|)) ≤
        Real.sqrt (B n q β) * (Real.log n + 1) := by
    simp only [mul_add, mul_one]
    linarith only [mul_le_mul_of_nonneg_right hq hlog, hshift]
  calc
    _ = (Real.sqrt n * Real.log n) * (Real.sqrt q * (Real.log n + Real.sqrt (n * |β|))) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg q)]
      ring
    _ ≤ (Real.sqrt n * Real.log n) * (Real.sqrt (B n q β) * (Real.log n + 1)) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (Real.sqrt_nonneg _) hlog)
    _ = (Real.log n * (Real.log n + 1)) * (Real.sqrt n * Real.sqrt (B n q β)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (log_product_bound hn' hε)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end DeepThreeQuarters

namespace DeepThreeQuarters

noncomputable def primeWeight (k : ℕ) : ℝ := if k.Prime then Real.log k else 0

noncomputable def weightedSum (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (u k : ℂ) *
    Complex.exp (((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I)

end DeepThreeQuarters

open Filter

namespace DeepThreeQuarters

noncomputable def rationalModel (n q : ℕ) (β : ℝ) : ℂ :=
  (ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ) * positiveGeometricSum n β

/-- Friedlander and Goldston, formula (1.15), restricted to the approximation
scale needed here. The constant and threshold are independent of the fraction. -/
def FriedlanderGoldstonEstimate : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ a q : ℕ, 1 ≤ q → a ≤ q →
    a.Coprime q → (q : ℝ) ≤ Real.sqrt n → ∀ β : ℝ, |β| ≤ 1 / ((q : ℝ) * Real.sqrt n) →
    ‖weightedSum n primeWeight (a / (q : ℝ) + β) - rationalModel n q β‖ ≤
      K * (Real.sqrt ((q : ℝ) * n) * Real.log n * (Real.log n + Real.sqrt (n * |β|)))

/-- The published pointwise prime-sum estimate implies the precise quantifiers
and exponent in the registered deep-arc problem. -/
theorem target_of_friedlander_goldston (hFG : FriedlanderGoldstonEstimate) :
    ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ wideArcs n →
      ‖weightedSum n primeWeight t‖ ≤ (n : ℝ) ^ (3/4 + η) := by
  obtain ⟨K, hK, N₀, hraw⟩ := hFG
  intro η hη
  let ε := η / 2
  have hε : 0 < ε := half_pos hη
  let A := 8 + 4 / ε
  let D := (2 / ε)^2 + 1 / ε
  let C := max A (K * D)
  have hC : 0 ≤ C := (show 0 ≤ A by dsimp [A]; positivity).trans (le_max_left _ _)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (eventually_absorb (2 * C) η hη)
  refine ⟨max 4 (max N₀ N₁), ?_⟩
  intro n hn t ht hdeep
  have hn4 : 4 ≤ n := (le_max_left _ _).trans hn
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₁ : N₁ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  obtain ⟨a, q, hq, haq, hc, hqs, hβ, hlo, hhi⟩ :=
    exists_deep_approximation (by omega : 1 ≤ n) ht hdeep
  let β := t - (a : ℝ) / q
  have hqn : (q : ℝ) ≤ n := hqs.trans (Real.sqrt_le_self_iff.mpr (Or.inr hn'))
  have hb : 0 < B n q β :=
    (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hn') _).trans_le hlo
  have hmodel := rational_term_le hε hq hqn hb (positiveGeometricSum_mul_B_le hn4 hq hβ)
  have herror := hraw n hn₀ a q hq haq hc hqs β hβ
  have htβ : (a : ℝ) / q + β = t := by dsimp [β]; ring
  rw [htβ] at herror
  have herr := herror.trans (mul_le_mul_of_nonneg_left
    (friedlanderGoldston_error_normalize hε n q β (by omega)) hK.le)
  let P := weightedSum n primeWeight t
  have bound := pointwise_budget (ε := ε) hn' hC hlo hhi P (rationalModel n q β)
    (hmodel.trans (by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left A (K * D)) (by positivity)) (by positivity)))
    (herr.trans (by
      change K * (D * _ * _) ≤ C * _ * _
      rw [← mul_assoc K, ← mul_assoc K]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right A (K * D)) (by positivity)) (by positivity)))
  exact bound.trans (hN₁ n hn₁)

end DeepThreeQuarters

theorem PEqualNP.Outside.L_goldbach_deep_three_quarters_from_farey_error :
    DeepThreeQuarters.FriedlanderGoldstonEstimate →
    ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ DeepThreeQuarters.wideArcs n →
      ‖DeepThreeQuarters.weightedSum n DeepThreeQuarters.primeWeight t‖ ≤
        (n : ℝ) ^ (3 / 4 + η) := by
  exact DeepThreeQuarters.target_of_friedlander_goldston
