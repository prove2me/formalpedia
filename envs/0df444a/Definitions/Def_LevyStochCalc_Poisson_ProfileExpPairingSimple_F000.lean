-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairingSimple_F000
-- name    : LevyStochCalc_Poisson_ProfileExpPairingSimple_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:23:17.902046+00:00
-- url     : https://prove2.me/theorems/8e7f6715-3d6f-4e9a-9b8d-29108636df7d
-- title:
--   Source declarations: LevyStochCalc.Poisson.ProfileExpPairingSimple
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.ProfileExpPairingSimple. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedCountCharacter_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedProduct_F001
import Definitions.Def_LevyStochCalc_Probability_CharacterL2_F000
import Definitions.Def_LevyStochCalc_Probability_CharacterL2_F001
import Definitions.Def_LevyStochCalc_Probability_CharacterL2_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The character of a compensated step integral against first- and second-order elements

For a simple mark profile with pairwise disjoint mark sets `B_k` of finite intensity, the
compensated counts `Ñ_k` of the strips `(a, b] × B_k` are independent, so the character
`e^{iuJ_c}` of the compensated step integral `J_c = ∑_k c_k Ñ_k` carried by a coefficient vector
`c` factors over the strips. Each factor pairs with `Ñ_k` and `Ñ_k²` through the identities of
`Poisson/CompensatedCountCharacter.lean`, with `λ_k = (b − a) ν(B_k)`:
`E[e^{isÑ} Ñ] = λ (e^{is} − 1) E[e^{isÑ}]` and
`E[e^{isÑ} Ñ²] = (λ² (e^{is} − 1)² + λ e^{is}) E[e^{isÑ}]`. Summing over the strips gives, for
coefficient vectors `d, d'` on the same mark sets and `γ_k = e^{iuc_k} − 1`,

  `E[e^{iuJ_c} J_d] = (b − a) ∑_k ν(B_k) γ_k d_k · E[e^{iuJ_c}]`,

and the matching second-order identity for `E[e^{iuJ_c} J_d J_{d'}]`. On a common refinement of
finitely many simple profiles these become the pairings of the character of the compensated
integral of one simple profile `G` with the compensated integrals of others, with
`γ = e^{iuG} − 1`:

  `E[e^{iuJ(G)} J(F)] = (b − a) ∫ γ F dν · E[e^{iuJ(G)}]`,
  `E[e^{iuJ(G)} J(F) J(K)]`
  `  = ((b − a)² ∫ γ F dν ∫ γ K dν + (b − a) (∫ γ F K dν + ∫ F K dν)) · E[e^{iuJ(G)}]`.

## Main statements

* `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_stepIntegral_mul_stepIntegral`,
  `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_stepIntegral_mul_stepIntegral_mul` —
  the first- and second-order pairings on the mark sets of one simple profile.
* `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_compensatedProfile_mul`,
  `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_compensatedProfile_mul_mul` — the
  first- and second-order pairings at simple mark profiles.
* `LevyStochCalc.Poisson.SimpleProfile.abs_toFun_le` — the function of a simple profile is bounded
  by the sum of the absolute values of its coefficients.
-/

open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Strips of a simple profile -/

/-- For a Poisson count `N` of mean `lam`, `z = e^{is}` and `j ≤ 2`, the ratio
`E[e^{is(N − lam)} (N − lam) ^ j] / E[e^{is(N − lam)}]`. -/
private noncomputable def countMoment (lam : ℝ) (z : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => lam * (z - 1)
  | 2 => lam ^ 2 * (z - 1) ^ 2 + lam * z
  | _ => 0
/-- The pairing of the compensated count of a region of finite intensity with its character,
through the moments of order at most two. -/
private theorem integral_exp_mul_compensated_pow (N : PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (s : ℝ)
    {j : ℕ} (hj : j ≤ 2) :
    ∫ ω, Complex.exp (Complex.I * ((s * N.compensated B ω : ℝ) : ℂ))
        * ((N.compensated B ω : ℝ) : ℂ) ^ j ∂P
      = countMoment (referenceIntensity ν B).toReal (Complex.exp (Complex.I * s)) j
        * ∫ ω, Complex.exp (Complex.I * ((s * N.compensated B ω : ℝ) : ℂ)) ∂P := by
  interval_cases j
  · simp [countMoment]
  · simpa [countMoment] using integral_exp_I_mul_compensated_mul_compensated N hB hfin s
  · simpa [countMoment] using integral_exp_I_mul_compensated_mul_compensated_sq N hB hfin s
omit [SigmaFinite ν] in
/-- The strips over the mark sets of a simple profile are pairwise disjoint. -/
private theorem pairwise_disjoint_strip (H : SimpleProfile E ν) (a b : ℝ) :
    Pairwise fun k l => Disjoint (Set.Ioc a b ×ˢ H.B k) (Set.Ioc a b ×ˢ H.B l) :=
  fun _ _ hkl => Set.disjoint_left.2 fun _ hx hx' =>
    Set.disjoint_left.1 (H.B_disjoint hkl) hx.2 hx'.2
/-- The character of a compensated step integral of a simple profile factors over the strips of
the profile. -/
private theorem exp_stepIntegral_withCoeff (N : PoissonRandomMeasure P ν) (H : SimpleProfile E ν)
    (c : Fin H.K → ℝ) (a b u : ℝ) (ω : Ω) :
    Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
      = ∏ k, Complex.exp (Complex.I
          * (((u * c k) * N.compensated (Set.Ioc a b ×ˢ H.B k) ω : ℝ) : ℂ)) := by
  rw [← Complex.exp_sum, SimpleProfile.stepIntegral_withCoeff, Finset.mul_sum]
  push_cast
  rw [Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  ring
/-- **The pairing of the character of a compensated step integral with a monomial in the
compensated counts of its strips.** For a simple profile with mark sets `B_k`, coefficients `c`,
compensated counts `Ñ_k` of the strips `(a, b] × B_k` and exponents `n_k ≤ 2`,
`E[e^{iu J} ∏ Ñ_k ^ n_k] = ∏ M_k(n_k) E[e^{iu J}]`. -/
private theorem integral_exp_stepIntegral_mul_prod_pow (N : PoissonRandomMeasure P ν)
    (H : SimpleProfile E ν) (c : Fin H.K → ℝ) {a b : ℝ} (ha : 0 ≤ a) (u : ℝ)
    (n : Fin H.K → ℕ) (hn : ∀ k, n k ≤ 2) :
    ∫ ω, Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
        * ∏ k, ((N.compensated (Set.Ioc a b ×ˢ H.B k) ω : ℝ) : ℂ) ^ n k ∂P
      = (∏ k, countMoment (referenceIntensity ν (Set.Ioc a b ×ˢ H.B k)).toReal
            (Complex.exp (Complex.I * ((u * c k : ℝ) : ℂ))) (n k))
        * ∫ ω, Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
          ∂P := by
  set R : Fin H.K → Set (ℝ × E) := fun k => Set.Ioc a b ×ˢ H.B k with hRdef
  have hR : ∀ k, MeasurableSet (R k) := fun k => measurableSet_Ioc.prod (H.B_measurable k)
  have hfin : ∀ k, referenceIntensity ν (R k) ≠ ⊤ :=
    fun k => referenceIntensity_strip_ne_top ha (H.B_finite k)
  have hind := iIndepFun_count_fin N R hR (pairwise_disjoint_strip H a b)
  set F : Fin H.K → ℕ → ℝ≥0∞ → ℂ := fun k i x =>
    Complex.exp (Complex.I * (((u * c k) * (x.toReal - (referenceIntensity ν (R k)).toReal) : ℝ)
      : ℂ)) * (((x.toReal - (referenceIntensity ν (R k)).toReal : ℝ)) : ℂ) ^ i with hFdef
  have hFm : ∀ k i, Measurable (F k i) := fun k i => by
    simp only [hFdef]
    fun_prop
  have hprod : ∀ i : Fin H.K → ℕ, ∫ ω, ∏ k, F k (i k) (N.N ω (R k)) ∂P
      = ∏ k, ∫ ω, F k (i k) (N.N ω (R k)) ∂P := fun i =>
    hind.integral_fun_prod_comp (f := fun k => F k (i k))
      (fun k => (N.measurable_eval (hR k)).aemeasurable)
      (fun k => (hFm k (i k)).aestronglyMeasurable)
  have hpt : ∀ (i : Fin H.K → ℕ) (ω : Ω),
      Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
        * ∏ k, ((N.compensated (R k) ω : ℝ) : ℂ) ^ i k = ∏ k, F k (i k) (N.N ω (R k)) := by
    intro i ω
    rw [exp_stepIntegral_withCoeff, ← Finset.prod_mul_distrib]
    rfl
  have hsingle : ∀ k (i : ℕ), i ≤ 2 → ∫ ω, F k i (N.N ω (R k)) ∂P
      = countMoment (referenceIntensity ν (R k)).toReal
          (Complex.exp (Complex.I * ((u * c k : ℝ) : ℂ))) i * ∫ ω, F k 0 (N.N ω (R k)) ∂P := by
    intro k i hi
    have hFeq : ∀ (i : ℕ) (ω : Ω), F k i (N.N ω (R k))
        = Complex.exp (Complex.I * (((u * c k) * N.compensated (R k) ω : ℝ) : ℂ))
          * ((N.compensated (R k) ω : ℝ) : ℂ) ^ i := fun _ _ => rfl
    simp_rw [hFeq, pow_zero, mul_one]
    exact integral_exp_mul_compensated_pow N (hR k) (hfin k) (u * c k) hi
  have h0 : ∫ ω, Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
      ∂P = ∏ k, ∫ ω, F k 0 (N.N ω (R k)) ∂P := by
    rw [← hprod (fun _ => 0)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    dsimp only
    rw [← hpt (fun _ => 0) ω]
    simp
  calc _ = ∫ ω, ∏ k, F k (n k) (N.N ω (R k)) ∂P :=
        integral_congr_ae (Eventually.of_forall fun ω => hpt n ω)
    _ = ∏ k, (countMoment (referenceIntensity ν (R k)).toReal
          (Complex.exp (Complex.I * ((u * c k : ℝ) : ℂ))) (n k)
          * ∫ ω, F k 0 (N.N ω (R k)) ∂P) := by
        rw [hprod n]
        exact Finset.prod_congr rfl fun k _ => hsingle k (n k) (hn k)
    _ = _ := by rw [Finset.prod_mul_distrib, h0]
/-- A product over the indices of a function taking the value one at exponent zero, evaluated
along the multi-index of a single index, is the value at that index. -/
private theorem prod_pi_single {K : ℕ} (f : Fin K → ℕ → ℂ) (hf : ∀ k, f k 0 = 1) (m : Fin K)
    (j : ℕ) : ∏ k, f k ((Pi.single m j : Fin K → ℕ) k) = f m j := by
  rw [Finset.prod_eq_single m (fun k _ hk => by rw [Pi.single_eq_of_ne hk, hf])
    (fun h => absurd (Finset.mem_univ m) h), Pi.single_eq_same]
/-- The pairing of the character of a compensated step integral with the compensated count of a
strip of its simple profile. -/
private theorem integral_exp_stepIntegral_mul_compensated (N : PoissonRandomMeasure P ν)
    (H : SimpleProfile E ν) (c : Fin H.K → ℝ) {a b : ℝ} (ha : 0 ≤ a) (u : ℝ) (m : Fin H.K) :
    ∫ ω, Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
        * ((N.compensated (Set.Ioc a b ×ˢ H.B m) ω : ℝ) : ℂ) ∂P
      = ((referenceIntensity ν (Set.Ioc a b ×ˢ H.B m)).toReal : ℂ)
          * (Complex.exp (Complex.I * ((u * c m : ℝ) : ℂ)) - 1)
        * ∫ ω, Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
          ∂P := by
  have h := integral_exp_stepIntegral_mul_prod_pow N H c (b := b) ha u (Pi.single m 1) fun k => by
    by_cases hk : k = m
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]
  have hpow : ∀ ω, ∏ k, ((N.compensated (Set.Ioc a b ×ˢ H.B k) ω : ℝ) : ℂ)
      ^ ((Pi.single m 1 : Fin H.K → ℕ) k) = ((N.compensated (Set.Ioc a b ×ˢ H.B m) ω : ℝ) : ℂ) :=
    fun ω => by
      rw [prod_pi_single (fun k i => ((N.compensated (Set.Ioc a b ×ˢ H.B k) ω : ℝ) : ℂ) ^ i)
        (fun k => pow_zero _), pow_one]
  rw [prod_pi_single _ (fun k => rfl)] at h
  simp only [hpow] at h
  exact h
/-- The pairing of the character of a compensated step integral with the product of the
compensated counts of two strips of its simple profile. -/
private theorem integral_exp_stepIntegral_mul_compensated_mul (N : PoissonRandomMeasure P ν)
    (H : SimpleProfile E ν) (c : Fin H.K → ℝ) {a b : ℝ} (ha : 0 ≤ a) (u : ℝ) (m l : Fin H.K) :
    ∫ ω, Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
        * ((N.compensated (Set.Ioc a b ×ˢ H.B m) ω : ℝ) : ℂ)
        * ((N.compensated (Set.Ioc a b ×ˢ H.B l) ω : ℝ) : ℂ) ∂P
      = (((referenceIntensity ν (Set.Ioc a b ×ˢ H.B m)).toReal : ℂ)
            * (Complex.exp (Complex.I * ((u * c m : ℝ) : ℂ)) - 1)
          * (((referenceIntensity ν (Set.Ioc a b ×ˢ H.B l)).toReal : ℂ)
            * (Complex.exp (Complex.I * ((u * c l : ℝ) : ℂ)) - 1))
          + if m = l then ((referenceIntensity ν (Set.Ioc a b ×ˢ H.B m)).toReal : ℂ)
            * Complex.exp (Complex.I * ((u * c m : ℝ) : ℂ)) else 0)
        * ∫ ω, Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
          ∂P := by
  by_cases hml : m = l
  · subst hml
    have h := integral_exp_stepIntegral_mul_prod_pow N H c (b := b) ha u (Pi.single m 2) fun k => by
      by_cases hk : k = m
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    have hpow : ∀ ω, ∏ k, ((N.compensated (Set.Ioc a b ×ˢ H.B k) ω : ℝ) : ℂ)
        ^ ((Pi.single m 2 : Fin H.K → ℕ) k)
        = ((N.compensated (Set.Ioc a b ×ˢ H.B m) ω : ℝ) : ℂ) ^ 2 :=
      fun ω => prod_pi_single (fun k i => ((N.compensated (Set.Ioc a b ×ˢ H.B k) ω : ℝ) : ℂ) ^ i)
        (fun k => pow_zero _) m 2
    rw [prod_pi_single _ (fun k => rfl)] at h
    simp only [hpow] at h
    rw [if_pos rfl]
    simp_rw [mul_assoc, ← sq]
    rw [← mul_assoc, h]
    simp only [countMoment]
    ring
  · have hn : ∀ k, (Pi.single m 1 + Pi.single l 1 : Fin H.K → ℕ) k ≤ 2 := fun k => by
      by_cases hkm : k = m
      · subst hkm; simp [Pi.single_eq_of_ne hml]
      · by_cases hkl : k = l
        · subst hkl; simp [Pi.single_eq_of_ne hkm]
        · simp [Pi.single_eq_of_ne hkm, Pi.single_eq_of_ne hkl]
    have h := integral_exp_stepIntegral_mul_prod_pow N H c (b := b) ha u
      (Pi.single m 1 + Pi.single l 1) hn
    have hsplit : ∀ (lam : ℝ) (z : ℂ) (k : Fin H.K),
        countMoment lam z ((Pi.single m 1 + Pi.single l 1 : Fin H.K → ℕ) k)
          = countMoment lam z ((Pi.single m 1 : Fin H.K → ℕ) k)
            * countMoment lam z ((Pi.single l 1 : Fin H.K → ℕ) k) := fun lam z k => by
      by_cases hkm : k = m
      · subst hkm; simp [Pi.single_eq_of_ne hml, countMoment]
      · by_cases hkl : k = l
        · subst hkl; simp [Pi.single_eq_of_ne hkm, countMoment]
        · simp [Pi.single_eq_of_ne hkm, Pi.single_eq_of_ne hkl, countMoment]
    simp only [hsplit] at h
    rw [Finset.prod_mul_distrib, prod_pi_single _ (fun k => rfl),
      prod_pi_single _ (fun k => rfl)] at h
    have hpow : ∀ ω, ∏ k, ((N.compensated (Set.Ioc a b ×ˢ H.B k) ω : ℝ) : ℂ)
        ^ ((Pi.single m 1 + Pi.single l 1 : Fin H.K → ℕ) k)
        = ((N.compensated (Set.Ioc a b ×ˢ H.B m) ω : ℝ) : ℂ)
          * ((N.compensated (Set.Ioc a b ×ˢ H.B l) ω : ℝ) : ℂ) := fun ω => by
      simp_rw [Pi.add_apply, pow_add]
      rw [Finset.prod_mul_distrib,
        prod_pi_single (fun k i => ((N.compensated (Set.Ioc a b ×ˢ H.B k) ω : ℝ) : ℂ) ^ i)
          (fun k => pow_zero _),
        prod_pi_single (fun k i => ((N.compensated (Set.Ioc a b ×ˢ H.B k) ω : ℝ) : ℂ) ^ i)
          (fun k => pow_zero _), pow_one, pow_one]
    simp only [hpow] at h
    rw [if_neg hml, add_zero]
    simp_rw [mul_assoc]
    rw [h]
    simp only [countMoment]
    ring
omit [SigmaFinite ν] in
/-- The integral of a function of the functions carried by three coefficient vectors on the mark
sets of a simple profile, vanishing where all three vanish. -/
private theorem integral_withCoeff_three (H : SimpleProfile E ν) (c d d' : Fin H.K → ℝ)
    (Ψ : ℝ → ℝ → ℝ → ℂ) (hΨ : Ψ 0 0 0 = 0) :
    ∫ e, Ψ ((H.withCoeff c).toFun e) ((H.withCoeff d).toFun e) ((H.withCoeff d').toFun e) ∂ν
      = ∑ k, ((ν (H.B k)).toReal : ℂ) * Ψ (c k) (d k) (d' k) := by
  classical
  have hpt : ∀ e, Ψ ((H.withCoeff c).toFun e) ((H.withCoeff d).toFun e)
      ((H.withCoeff d').toFun e) = ∑ k, (H.B k).indicator (fun _ => Ψ (c k) (d k) (d' k)) e := by
    intro e
    by_cases h : ∃ k, e ∈ H.B k
    · obtain ⟨k, hk⟩ := h
      rw [SimpleProfile.toFun_of_mem (H.withCoeff c) (k := k) hk,
        SimpleProfile.toFun_of_mem (H.withCoeff d) (k := k) hk,
        SimpleProfile.toFun_of_mem (H.withCoeff d') (k := k) hk,
        Finset.sum_eq_single_of_mem k (Finset.mem_univ k) (fun l _ hl => Set.indicator_of_notMem
          (fun hmem => (Set.disjoint_left.1 (H.B_disjoint hl) hmem) hk) _),
        Set.indicator_of_mem hk]
      rfl
    · simp only [not_exists] at h
      rw [SimpleProfile.toFun_of_notMem (H.withCoeff c) h,
        SimpleProfile.toFun_of_notMem (H.withCoeff d) h,
        SimpleProfile.toFun_of_notMem (H.withCoeff d') h, hΨ]
      exact (Finset.sum_eq_zero fun k _ => Set.indicator_of_notMem (h k) _).symm
  have hint : ∀ k, Integrable (fun e => (H.B k).indicator (fun _ => Ψ (c k) (d k) (d' k)) e)
      ν := fun k =>
    memLp_one_iff_integrable.1 (memLp_indicator_const 1 (H.B_measurable k) _
      (Or.inr (H.B_finite k)))
  simp_rw [hpt]
  rw [integral_finsetSum _ fun k _ => hint k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_indicator_const _ (H.B_measurable k), Complex.real_smul, measureReal_def]
namespace SimpleProfile

/-! ### Pairings on the mark sets of one simple profile -/

/-- The pairing of the character of the compensated step integral carried by a coefficient
vector `c` on the mark sets `B_k` of a simple profile with the compensated step integral carried
by a second coefficient vector `d` on the same mark sets: with `ν_k = ν(B_k)`,
`E[e^{iuJ_c} J_d] = (b − a) ∑_k ν_k (e^{iuc_k} − 1) d_k · E[e^{iuJ_c}]`. -/
theorem integral_exp_I_mul_stepIntegral_mul_stepIntegral (N : PoissonRandomMeasure P ν)
    (H : SimpleProfile E ν) (c d : Fin H.K → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
        * (((H.withCoeff d).stepIntegral N a b ω : ℝ) : ℂ) ∂P
      = ((b - a : ℝ) : ℂ) * (∑ k, ((ν (H.B k)).toReal : ℂ)
          * ((Complex.exp (Complex.I * ((u * c k : ℝ) : ℂ)) - 1) * (d k : ℂ)))
        * ∫ ω, Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
          ∂P := by
  have hS := ((H.withCoeff c).memLp_stepIntegral N ha b).aestronglyMeasurable
  have hint : ∀ k, Integrable (fun ω =>
      Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
        * ((N.compensated (Set.Ioc a b ×ˢ H.B k) ω : ℝ) : ℂ)) P := fun k =>
    integrable_exp_I_mul_mul u hS
      ((H.memLp_compensated_step N ha b k).integrable one_le_two).ofReal
  have hpt : ∀ ω, Complex.exp (Complex.I * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
      * (((H.withCoeff d).stepIntegral N a b ω : ℝ) : ℂ)
      = ∑ k, (d k : ℂ) * (Complex.exp (Complex.I
        * ((u * (H.withCoeff c).stepIntegral N a b ω : ℝ) : ℂ))
          * ((N.compensated (Set.Ioc a b ×ˢ H.B k) ω : ℝ) : ℂ)) := fun ω => by
    rw [SimpleProfile.stepIntegral_withCoeff N H d]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun k _ => (hint k).const_mul _]
  simp_rw [integral_const_mul, integral_exp_stepIntegral_mul_compensated N H c ha u,
    referenceIntensity_strip_toReal ha hab]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring
/-- The double sum of `x_m y_l ((α_m α_l + δ_ml β_m) χ)`. -/
private theorem sum_sum_pairing {K : ℕ} (x y α β : Fin K → ℂ) (χ : ℂ) :
    ∑ m, ∑ l, x m * y l * ((α m * α l + if m = l then β m else 0) * χ)
      = ((∑ m, x m * α m) * (∑ l, y l * α l) + ∑ m, x m * y m * β m) * χ := by
  have key : ∀ m l, x m * y l * ((α m * α l + if m = l then β m else 0) * χ)
      = x m * α m * (y l * α l) * χ + if m = l then x m * y m * β m * χ else 0 := fun m l => by
    split_ifs with h
    · subst h; ring
    · ring
  simp_rw [key, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_mul_sum, add_mul, Finset.sum_mul, Finset.sum_mul]
  simp_rw [Finset.sum_mul]
/-! ### Simple mark profiles -/

end SimpleProfile

end LevyStochCalc.Poisson


