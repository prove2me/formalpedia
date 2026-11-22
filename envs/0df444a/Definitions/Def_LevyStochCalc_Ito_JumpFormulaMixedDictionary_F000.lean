-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaMixedDictionary_F000
-- name    : LevyStochCalc_Ito_JumpFormulaMixedDictionary_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:36:02.332656+00:00
-- url     : https://prove2.me/theorems/fe5fc0c8-6040-4e8c-81d0-18d6fc5c34f2
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaMixedDictionary
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaMixedDictionary. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityExhaustion_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityExhaustion_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityExhaustion_F002
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityJumpSide_F002
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaMixed_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The split-drift dictionary for the mixed integrands

Splitting a finite-activity jump diffusion into a continuous Itô part and a pathwise jump sum
replaces the drift `μ` by `μ` minus the compensator `∫_A γ dν` of the jumps, while the pathwise
jump sum contributes the intensity integral of the jump increment. Read with the derivatives of
the state function at a state `y` and the coefficients at a state `x`, the two presentations of
the drift differ by the first-order term `∑ᵢ ∂ᵢu(s, y) ∫_A γᵢ(s, x) dν`, which the compensator
subtracted from the drift supplies exactly.

The statements below are the mixed forms of the drift reconciliation, of the split-drift
dictionary in the coordinates with a time coordinate prepended, and of the Itô–Lévy identity
assembled from them; the assembled identity carries the compensator-drift term over the mark set
carrying the jump coefficient. At `y = x` they are the statements of
`LevyStochCalc.Ito.JumpFormulaFiniteActivity`.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.setIntegral_mixedFirstOrder_eq`,
  `LevyStochCalc.Ito.JumpFormula.setIntegral_mixedCompensatorDriftIntegrand_eq_sub` — the mark
  integral of the mixed compensator-drift integrand as the mark integral of the mixed jump
  increment minus the first-order term.
* `LevyStochCalc.Ito.JumpFormula.setIntegral_mixedCompensatorDrift_eq_sub`,
  `LevyStochCalc.Ito.JumpFormula.setIntegral_firstOrder_add_mixedCompensatorDrift` — the drift
  reconciliation over a time window for the mixed integrands.
* `LevyStochCalc.Ito.JumpFormula.mixedDriftIntegrand_dictionary`,
  `LevyStochCalc.Ito.JumpFormula.splitDriftIntegrand_dictionary_mixed` — the non-stochastic
  integrands of Itô's formula in the prepended coordinates, with the derivatives at one state
  and the coefficients at another, as the mixed drift integrand and as the mixed drift integrand
  minus the first-order term.
* `LevyStochCalc.Ito.JumpFormula.splitDrift_pointwise_mixed`,
  `LevyStochCalc.Ito.JumpFormula.setIntegral_splitDrift_dictionary_mixed` — the same taken
  against a unit time drift, the drift with the jump compensator subtracted and a diffusion
  matrix whose time row vanishes, pointwise and integrated over a window.
* `LevyStochCalc.Ito.JumpFormula.itoLevy_of_splitDrift_and_jumpSum_mixed`,
  `LevyStochCalc.Ito.JumpFormula.itoLevy_of_splitDrift_and_jumpSum_mixed_of_support` — the
  Itô–Lévy identity for the mixed integrands from the split-drift identity and the jump-sum
  identity, with the compensator-drift term over the mark set and, for a jump coefficient
  carried by that set, over the whole mark space.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.5, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe v

section MixedDriftReconciliation

variable {n : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)}

/-- The mark integral of the first-order term of the mixed compensator-drift integrand is the
gradient at one state contracted with the mark integrals of the components of the jump
coefficient at the other. -/
theorem setIntegral_mixedFirstOrder_eq (A : Set E) (s : ℝ) (y x : Fin n → ℝ)
    (hγ : ∀ i : Fin n, IntegrableOn (fun e => γ s x e i) A ν) :
    ∫ e in A, (∑ i : Fin n, γ s x e i * gradient u s y i) ∂ν
      = ∑ i : Fin n, gradient u s y i * ∫ e in A, γ s x e i ∂ν := by
  rw [integral_finsetSum _ fun i _ => (hγ i).mul_const (gradient u s y i)]
  exact Finset.sum_congr rfl fun i _ => by rw [integral_mul_const]; ring
/-- The mark integral of the mixed compensator-drift integrand is the mark integral of the mixed
jump increment minus the gradient contracted with the mark integrals of the jump coefficient. -/
theorem setIntegral_mixedCompensatorDriftIntegrand_eq_sub (A : Set E) (s : ℝ)
    (y x : Fin n → ℝ) (hγ : ∀ i : Fin n, IntegrableOn (fun e => γ s x e i) A ν)
    (hΔ : IntegrableOn (fun e => mixedJumpIncrement u γ s y x e) A ν) :
    ∫ e in A, mixedCompensatorDriftIntegrand u γ s y x e ∂ν
      = (∫ e in A, mixedJumpIncrement u γ s y x e ∂ν)
        - ∑ i : Fin n, gradient u s y i * ∫ e in A, γ s x e i ∂ν := by
  have hfo : IntegrableOn (fun e => ∑ i : Fin n, γ s x e i * gradient u s y i) A ν :=
    integrable_finsetSum _ fun i _ => (hγ i).mul_const _
  simp only [mixedCompensatorDriftIntegrand, mixedJumpIncrement] at hΔ ⊢
  rw [← setIntegral_mixedFirstOrder_eq (u := u) A s y x hγ, ← integral_sub hΔ hfo]
omit [MeasurableSpace E] in
/-- The mixed compensator-drift integrand vanishes at marks off the carrier of the jump
coefficient. -/
theorem mixedCompensatorDriftIntegrand_eq_zero_of_notMem {A : Set E}
    (hsupp : ∀ (s : ℝ) (z : Fin n → ℝ) (e : E), e ∉ A → γ s z e = 0)
    (s : ℝ) (y x : Fin n → ℝ) {e : E} (he : e ∉ A) :
    mixedCompensatorDriftIntegrand u γ s y x e = 0 := by
  simp [mixedCompensatorDriftIntegrand, hsupp s x e he]
/-- The mixed compensator-drift integral over the mark space is its integral over the carrier of
the jump coefficient. -/
theorem integral_mixedCompensatorDriftIntegrand_eq_setIntegral {A : Set E}
    (hsupp : ∀ (s : ℝ) (z : Fin n → ℝ) (e : E), e ∉ A → γ s z e = 0)
    (s : ℝ) (y x : Fin n → ℝ) :
    ∫ e, mixedCompensatorDriftIntegrand u γ s y x e ∂ν
      = ∫ e in A, mixedCompensatorDriftIntegrand u γ s y x e ∂ν :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero fun _ he =>
    mixedCompensatorDriftIntegrand_eq_zero_of_notMem hsupp s y x he).symm
/-- Along a pair of paths the mixed compensator-drift integral over a time window is the
intensity integral of the mixed jump increment minus the first-order term. -/
theorem setIntegral_mixedCompensatorDrift_eq_sub (A : Set E) (y x : ℝ → Fin n → ℝ) (T : ℝ)
    (hγ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i : Fin n, IntegrableOn (fun e => γ s (x s) e i) A ν)
    (hΔ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun e => mixedJumpIncrement u γ s (y s) (x s) e) A ν)
    (hΔt : IntegrableOn (fun s => ∫ e in A, mixedJumpIncrement u γ s (y s) (x s) e ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (y s) i * ∫ e in A, γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume) :
    (∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, mixedCompensatorDriftIntegrand u γ s (y s) (x s) e ∂ν)
      = (∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, mixedJumpIncrement u γ s (y s) (x s) e ∂ν)
        - ∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
            gradient u s (y s) i * ∫ e in A, γ s (x s) e i ∂ν := by
  rw [← integral_sub hΔt hgt]
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  exact setIntegral_mixedCompensatorDriftIntegrand_eq_sub A s (y s) (x s) (hγ s hs) (hΔ s hs)
/-- **The drift reconciliation for the mixed integrands.** The first-order term that subtracting
the jump compensator removes from the drift is exactly the gap between the intensity integral of
the mixed jump increment and the mixed compensator-drift integral. -/
theorem setIntegral_firstOrder_add_mixedCompensatorDrift (A : Set E) (y x : ℝ → Fin n → ℝ)
    (T : ℝ)
    (hγ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i : Fin n, IntegrableOn (fun e => γ s (x s) e i) A ν)
    (hΔ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun e => mixedJumpIncrement u γ s (y s) (x s) e) A ν)
    (hΔt : IntegrableOn (fun s => ∫ e in A, mixedJumpIncrement u γ s (y s) (x s) e ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (y s) i * ∫ e in A, γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume) :
    (∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
          gradient u s (y s) i * ∫ e in A, γ s (x s) e i ∂ν)
        + ∫ s in Set.Icc (0 : ℝ) T,
            ∫ e in A, mixedCompensatorDriftIntegrand u γ s (y s) (x s) e ∂ν
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, mixedJumpIncrement u γ s (y s) (x s) e ∂ν := by
  have h := setIntegral_mixedCompensatorDrift_eq_sub (u := u) (γ := γ) A y x T hγ hΔ hΔt hgt
  linarith
end MixedDriftReconciliation

section MixedSplitDrift

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {f : (Fin (n + 1) → ℝ) → ℝ}
  {f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℝ}

omit [MeasurableSpace E] in
/-- The three non-stochastic terms of Itô's formula in the prepended coordinates, with the
derivatives of the representative at one state and the coefficients at another, make up the
mixed drift integrand. -/
theorem mixedDriftIntegrand_dictionary (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) (s : ℝ)
    (y x : Fin n → ℝ) :
    coordDeriv f' 0 (Fin.cons s y)
        + (∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y) * coeffs.μ s x q)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
            coordDeriv₂ f'' p.succ q.succ (Fin.cons s y)
              * ∑ k : Fin d, coeffs.σ s x p k * coeffs.σ s x q k
      = mixedDriftIntegrand u coeffs s y x := by
  have h1 : (∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y) * coeffs.μ s x q)
      = ∑ i : Fin n, coeffs.μ s x i * gradient u s y i :=
    Finset.sum_congr rfl fun q _ => by
      rw [coordDeriv_succ_cons_eq_gradient hfu hf s y q, mul_comm]
  have h2 : (∑ p : Fin n, ∑ q : Fin n, coordDeriv₂ f'' p.succ q.succ (Fin.cons s y)
        * ∑ k : Fin d, coeffs.σ s x p k * coeffs.σ s x q k)
      = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin d,
          coeffs.σ s x i k * coeffs.σ s x j k * hessian u s y i j := by
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [coordDeriv₂_succ_succ_cons_eq_hessian hfu hf hf' s y p q, ← Finset.sum_mul]
    ring
  simp only [mixedDriftIntegrand]
  rw [coordDeriv_zero_cons_eq_timeDeriv hfu hf s y, h1, h2]
  ring
/-- The non-stochastic integrands of Itô's formula in the prepended coordinates, with the
derivatives of the representative at one state and the coefficients at another, taken against
the drift with the jump compensator subtracted, make up the mixed drift integrand minus the
first-order term of the mixed compensator drift. -/
theorem splitDriftIntegrand_dictionary_mixed (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) (A : Set E) (s : ℝ)
    (y x : Fin n → ℝ) :
    (coordDeriv f' 0 (Fin.cons s y) * 1
          + ∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y)
              * (coeffs.μ s x q - ∫ e in A, coeffs.γ s x e q ∂ν))
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
            coordDeriv₂ f'' p.succ q.succ (Fin.cons s y)
              * ∑ k : Fin d, coeffs.σ s x p k * coeffs.σ s x q k
      = mixedDriftIntegrand u coeffs s y x
        - ∑ i : Fin n, gradient u s y i * ∫ e in A, coeffs.γ s x e i ∂ν := by
  have hdict := mixedDriftIntegrand_dictionary (u := u) hfu hf hf' coeffs s y x
  have hsplit : (∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y)
        * (coeffs.μ s x q - ∫ e in A, coeffs.γ s x e q ∂ν))
      = (∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y) * coeffs.μ s x q)
        - ∑ q : Fin n, gradient u s y q * ∫ e in A, coeffs.γ s x e q ∂ν := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [coordDeriv_succ_cons_eq_gradient hfu hf s y q]
    ring
  rw [mul_one, hsplit]
  linarith
/-- The non-stochastic integrands of Itô's formula at a pair of states, with the derivatives of
the representative at one and the coefficients at the other: with a unit time drift, the drift
with the jump compensator subtracted and a diffusion matrix whose time row vanishes, they make
up the mixed drift integrand minus the first-order term of the mixed compensator drift. -/
theorem splitDrift_pointwise_mixed (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) (A : Set E) (s : ℝ)
    (y x : Fin n → ℝ) (b : Fin (n + 1) → ℝ) (K : Fin (n + 1) → Fin d → ℝ) (hb0 : b 0 = 1)
    (hbs : ∀ q : Fin n, b q.succ = coeffs.μ s x q - ∫ e in A, coeffs.γ s x e q ∂ν)
    (hK0 : ∀ j : Fin d, K 0 j = 0)
    (hKs : ∀ (p : Fin n) (j : Fin d), K p.succ j = coeffs.σ s x p j) :
    (∑ p : Fin (n + 1), coordDeriv f' p (Fin.cons s y) * b p)
        + 1 / 2 * ∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
            coordDeriv₂ f'' p q (Fin.cons s y) * ∑ j : Fin d, K p j * K q j
      = mixedDriftIntegrand u coeffs s y x
        - ∑ i : Fin n, gradient u s y i * ∫ e in A, coeffs.γ s x e i ∂ν := by
  have h1 : (∑ p : Fin (n + 1), coordDeriv f' p (Fin.cons s y) * b p)
      = coordDeriv f' 0 (Fin.cons s y) * 1
        + ∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y)
            * (coeffs.μ s x q - ∫ e in A, coeffs.γ s x e q ∂ν) := by
    rw [Fin.sum_univ_succ, hb0]
    exact congrArg _ (Finset.sum_congr rfl fun q _ => by rw [hbs q])
  have h2 : (∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
        coordDeriv₂ f'' p q (Fin.cons s y) * ∑ j : Fin d, K p j * K q j)
      = ∑ p : Fin n, ∑ q : Fin n, coordDeriv₂ f'' p.succ q.succ (Fin.cons s y)
          * ∑ k : Fin d, coeffs.σ s x p k * coeffs.σ s x q k := by
    rw [sum_succ_succ_coordDeriv₂_of_row_zero (Fin.cons s y) K hK0]
    exact Finset.sum_congr rfl fun p _ =>
      Finset.sum_congr rfl fun q _ => by simp only [hKs]
  have h3 := splitDriftIntegrand_dictionary_mixed (ν := ν) hfu hf hf' coeffs A s y x
  rw [h1, h2]
  linarith
end MixedSplitDrift

section MixedAssembly

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E}

end MixedAssembly

end LevyStochCalc.Ito.JumpFormula


