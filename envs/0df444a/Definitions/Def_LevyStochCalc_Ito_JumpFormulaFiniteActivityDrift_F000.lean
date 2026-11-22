-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityDrift_F000
-- name    : LevyStochCalc_Ito_JumpFormulaFiniteActivityDrift_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:56:01.824904+00:00
-- url     : https://prove2.me/theorems/c5277143-e2a0-4559-840f-e8d67ee159fc
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaFiniteActivityDrift
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaFiniteActivityDrift. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaExhaustion_F000
import Definitions.Def_LevyStochCalc_Ito_JumpEndpointLeftLim_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaAssembly_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaAssembly_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaDictionary_F000
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingAllTimes_F000
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingAllTimes_F001
import Definitions.Def_LevyStochCalc_Ito_JumpSplittingAllTimes_F002
import Definitions.Def_LevyStochCalc_Ito_JumpSumIdentity_F000
import Definitions.Def_LevyStochCalc_Ito_JumpSumIdentity_F001
import Definitions.Def_LevyStochCalc_Poisson_JumpTimesComplete_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Reconciling the two drifts of the finite-activity Itô–Lévy formula

Splitting a finite-activity jump diffusion into a continuous Itô part and a pathwise jump sum
replaces the drift `μ` by `μ` minus the compensator `∫_A γ dν` of the jumps, while the pathwise
jump sum contributes the intensity integral of the jump increment `u(x + γ) − u(x)`. The
Itô–Lévy formula instead carries the drift `μ` itself and the compensator-drift integrand
`u(x + γ) − u(x) − ∑ᵢ γᵢ ∂ᵢu`. The two presentations differ by the first-order term
`∑ᵢ ∂ᵢu ∫_A γᵢ dν`, which the compensator subtracted from the drift supplies exactly, so the
split-drift identity and the jump-sum identity together give the Itô–Lévy identity in the
vocabulary of `driftIntegrand` and `compensatorDriftIntegrand`.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.5, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section DriftReconciliation

variable {n : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)}

/-- The mark integral of the first-order term of the compensator-drift integrand is the gradient
contracted with the mark integrals of the components of the jump coefficient. -/
theorem setIntegral_firstOrder_eq (A : Set E) (s : ℝ) (x : Fin n → ℝ)
    (hγ : ∀ i : Fin n, IntegrableOn (fun e => γ s x e i) A ν) :
    ∫ e in A, (∑ i : Fin n, γ s x e i * gradient u s x i) ∂ν
      = ∑ i : Fin n, gradient u s x i * ∫ e in A, γ s x e i ∂ν := by
  rw [integral_finsetSum _ fun i _ => (hγ i).mul_const (gradient u s x i)]
  exact Finset.sum_congr rfl fun i _ => by rw [integral_mul_const]; ring
/-- The mark integral of the compensator-drift integrand is the mark integral of the jump
increment minus the gradient contracted with the mark integrals of the jump coefficient. -/
theorem setIntegral_compensatorDriftIntegrand_eq_sub (A : Set E) (s : ℝ) (x : Fin n → ℝ)
    (hγ : ∀ i : Fin n, IntegrableOn (fun e => γ s x e i) A ν)
    (hΔ : IntegrableOn (fun e => u s (x + γ s x e) - u s x) A ν) :
    ∫ e in A, compensatorDriftIntegrand u γ s x e ∂ν
      = (∫ e in A, (u s (x + γ s x e) - u s x) ∂ν)
        - ∑ i : Fin n, gradient u s x i * ∫ e in A, γ s x e i ∂ν := by
  have hfo : IntegrableOn (fun e => ∑ i : Fin n, γ s x e i * gradient u s x i) A ν :=
    integrable_finsetSum _ fun i _ => (hγ i).mul_const _
  simp only [compensatorDriftIntegrand]
  rw [← setIntegral_firstOrder_eq (u := u) A s x hγ, ← integral_sub hΔ hfo]
omit [MeasurableSpace E] in
/-- The compensator-drift integrand vanishes at marks off the carrier of the jump
coefficient. -/
theorem compensatorDriftIntegrand_eq_zero_of_notMem {A : Set E}
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → γ s x e = 0)
    (s : ℝ) (x : Fin n → ℝ) {e : E} (he : e ∉ A) :
    compensatorDriftIntegrand u γ s x e = 0 := by
  simp [compensatorDriftIntegrand, hsupp s x e he]
/-- The compensator-drift integral over the mark space is its integral over the carrier of the
jump coefficient. -/
theorem integral_compensatorDriftIntegrand_eq_setIntegral {A : Set E}
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → γ s x e = 0)
    (s : ℝ) (x : Fin n → ℝ) :
    ∫ e, compensatorDriftIntegrand u γ s x e ∂ν
      = ∫ e in A, compensatorDriftIntegrand u γ s x e ∂ν :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero fun _ he =>
    compensatorDriftIntegrand_eq_zero_of_notMem hsupp s x he).symm
/-- Along a path the compensator-drift integral over a time window is the intensity integral of
the jump increment minus the first-order term. -/
theorem setIntegral_compensatorDrift_eq_sub (A : Set E) (x : ℝ → Fin n → ℝ) (T : ℝ)
    (hγ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i : Fin n, IntegrableOn (fun e => γ s (x s) e i) A ν)
    (hΔ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun e => u s (x s + γ s (x s) e) - u s (x s)) A ν)
    (hΔt : IntegrableOn (fun s => ∫ e in A, (u s (x s + γ s (x s) e) - u s (x s)) ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (x s) i * ∫ e in A, γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume) :
    (∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, compensatorDriftIntegrand u γ s (x s) e ∂ν)
      = (∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, (u s (x s + γ s (x s) e) - u s (x s)) ∂ν)
        - ∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
            gradient u s (x s) i * ∫ e in A, γ s (x s) e i ∂ν := by
  rw [← integral_sub hΔt hgt]
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  exact setIntegral_compensatorDriftIntegrand_eq_sub A s (x s) (hγ s hs) (hΔ s hs)
/-- **The drift reconciliation.** The first-order term that subtracting the jump compensator
removes from the drift is exactly the gap between the intensity integral of the jump increment
and the compensator-drift integral of the Itô–Lévy formula. -/
theorem setIntegral_firstOrder_add_compensatorDrift (A : Set E) (x : ℝ → Fin n → ℝ) (T : ℝ)
    (hγ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i : Fin n, IntegrableOn (fun e => γ s (x s) e i) A ν)
    (hΔ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun e => u s (x s + γ s (x s) e) - u s (x s)) A ν)
    (hΔt : IntegrableOn (fun s => ∫ e in A, (u s (x s + γ s (x s) e) - u s (x s)) ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (x s) i * ∫ e in A, γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume) :
    (∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
          gradient u s (x s) i * ∫ e in A, γ s (x s) e i ∂ν)
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, compensatorDriftIntegrand u γ s (x s) e ∂ν
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, (u s (x s + γ s (x s) e) - u s (x s)) ∂ν := by
  have h := setIntegral_compensatorDrift_eq_sub (u := u) (γ := γ) A x T hγ hΔ hΔt hgt
  linarith
end DriftReconciliation

section SplitDrift

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {f : (Fin (n + 1) → ℝ) → ℝ}
  {f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℝ}

omit [MeasurableSpace E] ν in
/-- A double sum over the coordinates with a time coordinate prepended, weighted by a diffusion
matrix whose zeroth row vanishes, reduces to the double sum over the original coordinates. -/
theorem sum_succ_succ_of_row_zero (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (H : Fin (n + 1) → Fin d → ℝ) (h0 : ∀ j : Fin d, H 0 j = 0) :
    (∑ p : Fin (n + 1), ∑ q : Fin (n + 1), c p q * ∑ j : Fin d, H p j * H q j)
      = ∑ p : Fin n, ∑ q : Fin n,
          c p.succ q.succ * ∑ j : Fin d, H p.succ j * H q.succ j := by
  rw [Fin.sum_univ_succ]
  have hzero : (∑ q : Fin (n + 1), c 0 q * ∑ j : Fin d, H 0 j * H q j) = 0 :=
    Finset.sum_eq_zero fun q _ => by simp [h0]
  rw [hzero, zero_add]
  exact Finset.sum_congr rfl fun p _ => by rw [Fin.sum_univ_succ]; simp [h0]
/-- The non-stochastic integrands of Itô's formula in the prepended coordinates, taken against
the drift with the jump compensator subtracted, make up the drift integrand of the Itô–Lévy
formula minus the first-order term of the compensator drift. -/
theorem splitDriftIntegrand_dictionary (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) (A : Set E) (s : ℝ)
    (y : Fin n → ℝ) :
    (coordDeriv f' 0 (Fin.cons s y) * 1
          + ∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y)
              * (coeffs.μ s y q - ∫ e in A, coeffs.γ s y e q ∂ν))
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
            coordDeriv₂ f'' p.succ q.succ (Fin.cons s y)
              * ∑ k : Fin d, coeffs.σ s y p k * coeffs.σ s y q k
      = driftIntegrand u coeffs s y
        - ∑ i : Fin n, gradient u s y i * ∫ e in A, coeffs.γ s y e i ∂ν := by
  have hdict := driftIntegrand_dictionary (u := u) hfu hf hf' coeffs s y
  have hsplit : (∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y)
        * (coeffs.μ s y q - ∫ e in A, coeffs.γ s y e q ∂ν))
      = (∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y) * coeffs.μ s y q)
        - ∑ q : Fin n, gradient u s y q * ∫ e in A, coeffs.γ s y e q ∂ν := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [coordDeriv_succ_cons_eq_gradient hfu hf s y q]
    ring
  rw [mul_one, hsplit]
  linarith
/-- The `coordDeriv₂` weights of a diffusion matrix whose zeroth row vanishes are carried by the
original coordinates only. -/
theorem sum_succ_succ_coordDeriv₂_of_row_zero (z : Fin (n + 1) → ℝ)
    (K : Fin (n + 1) → Fin d → ℝ) (h0 : ∀ j : Fin d, K 0 j = 0) :
    (∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
        coordDeriv₂ f'' p q z * ∑ j : Fin d, K p j * K q j)
      = ∑ p : Fin n, ∑ q : Fin n,
          coordDeriv₂ f'' p.succ q.succ z * ∑ j : Fin d, K p.succ j * K q.succ j :=
  sum_succ_succ_of_row_zero (fun p q => coordDeriv₂ f'' p q z) K h0
/-- The non-stochastic integrands of Itô's formula at a point of a path split at its jumps: with
a unit time drift, the drift with the jump compensator subtracted and a diffusion matrix whose
time row vanishes, they make up the drift integrand of the Itô–Lévy formula minus the
first-order term of the compensator drift. -/
theorem splitDrift_pointwise (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) (A : Set E) (s : ℝ)
    (y : Fin n → ℝ) (b : Fin (n + 1) → ℝ) (K : Fin (n + 1) → Fin d → ℝ) (hb0 : b 0 = 1)
    (hbs : ∀ q : Fin n, b q.succ = coeffs.μ s y q - ∫ e in A, coeffs.γ s y e q ∂ν)
    (hK0 : ∀ j : Fin d, K 0 j = 0)
    (hKs : ∀ (p : Fin n) (j : Fin d), K p.succ j = coeffs.σ s y p j) :
    (∑ p : Fin (n + 1), coordDeriv f' p (Fin.cons s y) * b p)
        + 1 / 2 * ∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
            coordDeriv₂ f'' p q (Fin.cons s y) * ∑ j : Fin d, K p j * K q j
      = driftIntegrand u coeffs s y
        - ∑ i : Fin n, gradient u s y i * ∫ e in A, coeffs.γ s y e i ∂ν := by
  have h1 : (∑ p : Fin (n + 1), coordDeriv f' p (Fin.cons s y) * b p)
      = coordDeriv f' 0 (Fin.cons s y) * 1
        + ∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y)
            * (coeffs.μ s y q - ∫ e in A, coeffs.γ s y e q ∂ν) := by
    rw [Fin.sum_univ_succ, hb0]
    exact congrArg _ (Finset.sum_congr rfl fun q _ => by rw [hbs q])
  have h2 : (∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
        coordDeriv₂ f'' p q (Fin.cons s y) * ∑ j : Fin d, K p j * K q j)
      = ∑ p : Fin n, ∑ q : Fin n, coordDeriv₂ f'' p.succ q.succ (Fin.cons s y)
          * ∑ k : Fin d, coeffs.σ s y p k * coeffs.σ s y q k := by
    rw [sum_succ_succ_coordDeriv₂_of_row_zero (Fin.cons s y) K hK0]
    exact Finset.sum_congr rfl fun p _ =>
      Finset.sum_congr rfl fun q _ => by simp only [hKs]
  have h3 := splitDriftIntegrand_dictionary (ν := ν) hfu hf hf' coeffs A s y
  rw [h1, h2]
  linarith
/-- Along a path the non-stochastic terms of Itô's formula in the prepended coordinates, taken
against the drift with the jump compensator subtracted, integrate over a window to the drift
integral of the Itô–Lévy formula minus the first-order term of the compensator drift. -/
theorem setIntegral_splitDrift_dictionary (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) (A : Set E) (T : ℝ)
    (x : ℝ → Fin n → ℝ) (b : Fin (n + 1) → ℝ → ℝ) (K : Fin (n + 1) → Fin d → ℝ → ℝ)
    (hb0 : ∀ s : ℝ, b 0 s = 1)
    (hbs : ∀ (q : Fin n) (s : ℝ),
      b q.succ s = coeffs.μ s (x s) q - ∫ e in A, coeffs.γ s (x s) e q ∂ν)
    (hK0 : ∀ (j : Fin d) (s : ℝ), K 0 j s = 0)
    (hKs : ∀ (p : Fin n) (j : Fin d) (s : ℝ), K p.succ j s = coeffs.σ s (x s) p j)
    (hD : ∀ p : Fin (n + 1), IntegrableOn
      (fun s => coordDeriv f' p (Fin.cons s (x s)) * b p s) (Set.Ioc (0 : ℝ) T) volume)
    (hQ : ∀ p q : Fin (n + 1), IntegrableOn
      (fun s => coordDeriv₂ f'' p q (Fin.cons s (x s)) * ∑ j : Fin d, K p j s * K q j s)
      (Set.Ioc (0 : ℝ) T) volume) :
    (∑ p : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (Fin.cons s (x s)) * b p s ∂volume)
        + 1 / 2 * ∑ p : Fin (n + 1), ∑ q : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (Fin.cons s (x s))
              * ∑ j : Fin d, K p j s * K q j s ∂volume
      = ∫ s in Set.Ioc (0 : ℝ) T,
          (driftIntegrand u coeffs s (x s)
            - ∑ i : Fin n, gradient u s (x s) i
                * ∫ e in A, coeffs.γ s (x s) e i ∂ν) ∂volume := by
  have hQint : ∀ p : Fin (n + 1), IntegrableOn
      (fun s => ∑ q : Fin (n + 1),
        coordDeriv₂ f'' p q (Fin.cons s (x s)) * ∑ j : Fin d, K p j s * K q j s)
      (Set.Ioc (0 : ℝ) T) volume :=
    fun p => integrable_finsetSum _ fun q _ => hQ p q
  have hDsum : (∑ p : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv f' p (Fin.cons s (x s)) * b p s ∂volume)
      = ∫ s in Set.Ioc (0 : ℝ) T,
          (∑ p : Fin (n + 1), coordDeriv f' p (Fin.cons s (x s)) * b p s) ∂volume :=
    (integral_finsetSum _ fun p _ => hD p).symm
  have hQsum : (∑ p : Fin (n + 1), ∑ q : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv₂ f'' p q (Fin.cons s (x s))
          * ∑ j : Fin d, K p j s * K q j s ∂volume)
      = ∫ s in Set.Ioc (0 : ℝ) T, (∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
          coordDeriv₂ f'' p q (Fin.cons s (x s))
            * ∑ j : Fin d, K p j s * K q j s) ∂volume := by
    have hstep : (∑ p : Fin (n + 1), ∑ q : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv₂ f'' p q (Fin.cons s (x s))
            * ∑ j : Fin d, K p j s * K q j s ∂volume)
        = ∑ p : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T, (∑ q : Fin (n + 1),
            coordDeriv₂ f'' p q (Fin.cons s (x s))
              * ∑ j : Fin d, K p j s * K q j s) ∂volume :=
      Finset.sum_congr rfl fun p _ => (integral_finsetSum _ fun q _ => hQ p q).symm
    rw [hstep]
    exact (integral_finsetSum _ fun p _ => hQint p).symm
  have hDint : IntegrableOn (fun s => ∑ p : Fin (n + 1),
      coordDeriv f' p (Fin.cons s (x s)) * b p s) (Set.Ioc (0 : ℝ) T) volume :=
    integrable_finsetSum _ fun p _ => hD p
  have hQtot : IntegrableOn (fun s => 1 / 2 * ∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
      coordDeriv₂ f'' p q (Fin.cons s (x s)) * ∑ j : Fin d, K p j s * K q j s)
      (Set.Ioc (0 : ℝ) T) volume :=
    (integrable_finsetSum _ fun p _ => hQint p).const_mul _
  rw [hDsum, hQsum, ← integral_const_mul, ← integral_add hDint hQtot]
  refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
  exact splitDrift_pointwise hfu hf hf' coeffs A s (x s) (fun p => b p s)
    (fun p j => K p j s) (hb0 s) (fun q => hbs q s) (fun j => hK0 j s)
    (fun p j => hKs p j s)
end SplitDrift

section Assembly

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E}

/-- **The Itô–Lévy formula in its own vocabulary from the split-drift form.** If along a path the
increment of `u` splits into the drift integral taken against the drift with the jump compensator
subtracted, a diffusion term `Dm` and a jump term `Js`, and if the jump term is a compensated
term `Cm` plus the intensity integral of the jump increment, then the increment of `u` is the
drift integral of `driftIntegrand`, `Dm`, `Cm` and the integral of
`compensatorDriftIntegrand`. -/
theorem itoLevy_of_splitDrift_and_jumpSum {A : Set E} {x : ℝ → Fin n → ℝ} {T : ℝ}
    {Dm Cm Js : ℝ}
    (hsupp : ∀ (s : ℝ) (y : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s y e = 0)
    (hγ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i : Fin n,
      IntegrableOn (fun e => coeffs.γ s (x s) e i) A ν)
    (hΔ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun e => u s (x s + coeffs.γ s (x s) e) - u s (x s)) A ν)
    (hΔt : IntegrableOn (fun s => ∫ e in A, (u s (x s + coeffs.γ s (x s) e) - u s (x s)) ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (x s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume)
    (hdt : IntegrableOn (fun s => driftIntegrand u coeffs s (x s)) (Set.Icc (0 : ℝ) T) volume)
    (hsplit : u T (x T) - u 0 (x 0)
      = (∫ s in Set.Icc (0 : ℝ) T, (driftIntegrand u coeffs s (x s)
            - ∑ i : Fin n, gradient u s (x s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν))
        + Dm + Js)
    (hjump : Js = Cm + ∫ s in Set.Icc (0 : ℝ) T,
      ∫ e in A, (u s (x s + coeffs.γ s (x s) e) - u s (x s)) ∂ν) :
    u T (x T) - u 0 (x 0)
      = (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (x s)) + Dm + Cm
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e, compensatorDriftIntegrand u coeffs.γ s (x s) e ∂ν := by
  have hE : (∫ s in Set.Icc (0 : ℝ) T,
        ∫ e, compensatorDriftIntegrand u coeffs.γ s (x s) e ∂ν)
      = ∫ s in Set.Icc (0 : ℝ) T,
          ∫ e in A, compensatorDriftIntegrand u coeffs.γ s (x s) e ∂ν :=
    setIntegral_congr_fun measurableSet_Icc fun s _ =>
      integral_compensatorDriftIntegrand_eq_setIntegral hsupp s (x s)
  have hcancel := setIntegral_firstOrder_add_compensatorDrift (u := u) (γ := coeffs.γ)
    A x T hγ hΔ hΔt hgt
  have hdsplit : (∫ s in Set.Icc (0 : ℝ) T, (driftIntegrand u coeffs s (x s)
        - ∑ i : Fin n, gradient u s (x s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν))
      = (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (x s))
        - ∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
            gradient u s (x s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν :=
    integral_sub hdt hgt
  rw [hE]
  rw [hdsplit] at hsplit
  rw [hjump] at hsplit
  linarith
end Assembly

end LevyStochCalc.Ito.JumpFormula


