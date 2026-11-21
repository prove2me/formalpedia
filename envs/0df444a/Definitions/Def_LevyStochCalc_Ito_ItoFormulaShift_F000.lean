-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaShift_F000
-- name    : LevyStochCalc_Ito_ItoFormulaShift_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:18:25.915391+00:00
-- url     : https://prove2.me/theorems/65afc071-86c4-4822-bf34-bec9be241f13
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaShift
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaShift. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CoordDerivative_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaStopped_F000
import Definitions.Def_SourceProof_01c4756fd1800d9271415e88

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a translated function

Translating the argument of a twice continuously differentiable function by a fixed vector
translates its Fréchet derivatives and its partial derivatives by the same vector, so Itô's
formula along a stopped path holds for the translate with every derivative read at the
translated path.

A weight that is known at a deterministic time and vanishes off the event that a stopping time
equals that time passes inside the Itô integral of an integrand that vanishes up to that
stopping time: the integrand is then carried by the window between that time and the horizon,
and the increment removed by the window is invisible on the event.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoFormula_stopped_shift` — Itô's formula along a stopped path for
  a function translated by a fixed vector.
* `LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_hitInd` — a bounded weight known at
  a deterministic time, cut to the event that a stopping time equals it, passes inside the Itô
  integral of an integrand vanishing up to that stopping time.
* `LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_hitInd_stopped_sub` — the same for
  the increment of an integrand between two stopping times.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Translate

variable {n : ℕ}

/-- The translate of a twice continuously differentiable function is twice continuously
differentiable. -/
theorem contDiff_shiftArg {f : (Fin n → ℝ) → ℝ} (hfC : ContDiff ℝ 2 f) (c : Fin n → ℝ) :
    ContDiff ℝ 2 fun z => f (z + c) := by
  have hin : ContDiff ℝ 2 fun z : Fin n → ℝ => z + c := contDiff_id.add contDiff_const
  exact hfC.comp hin
/-- The Fréchet derivative of a translate is the derivative read at the translated point. -/
theorem hasFDerivAt_shiftArg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : (Fin n → ℝ) → F} {g' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] F}
    (hg : ∀ z, HasFDerivAt g (g' z) z) (c z : Fin n → ℝ) :
    HasFDerivAt (fun w => g (w + c)) (g' (z + c)) z := by
  have hin : HasFDerivAt (fun w : Fin n → ℝ => w + c)
      (ContinuousLinearMap.id ℝ (Fin n → ℝ)) z := (hasFDerivAt_id z).add_const c
  have hcomp : HasFDerivAt (g ∘ fun w : Fin n → ℝ => w + c)
      ((g' (z + c)).comp (ContinuousLinearMap.id ℝ (Fin n → ℝ))) z := (hg (z + c)).comp z hin
  rw [ContinuousLinearMap.comp_id] at hcomp
  exact hcomp
/-- A partial derivative of a translated first derivative is the partial derivative read at the
translated point. -/
theorem coordDeriv_shiftArg (f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ) (c : Fin n → ℝ)
    (p : Fin n) (z : Fin n → ℝ) :
    coordDeriv (fun w => f' (w + c)) p z = coordDeriv f' p (z + c) := rfl
/-- A second partial derivative of a translated second derivative is the second partial
derivative read at the translated point. -/
theorem coordDeriv₂_shiftArg (f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)
    (c : Fin n → ℝ) (p q : Fin n) (z : Fin n → ℝ) :
    coordDeriv₂ (fun w => f'' (w + c)) p q z = coordDeriv₂ f'' p q (z + c) := rfl
end Translate

section ShiftedFormula

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

include hcoord in
/-- **Itô's formula along a stopped path, for a function translated by a fixed vector.** -/
theorem itoFormula_stopped_shift
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ' (bdrift p))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {τ : Ω → WithTop ℝ} (hτ : MeasureTheory.IsStoppingTime ℱ' τ)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω)
    (J : Finset ℝ) (hJ0 : ∀ c ∈ J, 0 ≤ c)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ τ ω = ⊤)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (c : Fin n → ℝ)
    (hmg : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω + c) * H p k ω s)))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω + c) * H p k ω s))
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c) * H p k ω s) ω s‖₊
        : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X (clipTime τ T ω) ω + c) - f (X 0 ω + c)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          Probability.stopped τ
            (fun ω s => coordDeriv f' p (X s ω + c) * bdrift p ω s) ω s ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω + c) * H p k ω s)
            (hmg p k) (hpg p k) (hqg p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + c)
              * ∑ k : Fin d, H p k ω s * H q k ω s) ω s ∂volume :=
  _root_.Prove2MeSourceProof.h_01c4756fd1800d9271415e88 W ℱ' hcoord h hℱ0 hnull hX₀ hbm hbp hbq hτ hτ0 J hJ0 hτJ
    (f := fun z => f (z + c)) (f' := fun z => f' (z + c)) (f'' := fun z => f'' (z + c))
    (contDiff_shiftArg hfC c) (fun z => hasFDerivAt_shiftArg hf c z)
    (fun z => hasFDerivAt_shiftArg hf' c z) hmg hpg hqg hT
end ShiftedFormula

section StoppedIncrement

variable {Ω : Type u}

/-- The increment, over an integrand cut off at a stopping time, of the same integrand cut off at
a later stopping time vanishes up to the earlier time. -/
theorem stopped_sub_stopped_eq_zero {σ τ : Ω → WithTop ℝ} (hστ : ∀ ω, σ ω ≤ τ ω)
    (K : Ω → ℝ → ℝ) (ω : Ω) {s : ℝ} (hs : ((s : ℝ) : WithTop ℝ) ≤ σ ω) :
    Probability.stopped τ K ω s - Probability.stopped σ K ω s = 0 := by
  unfold LevyStochCalc.Probability.stopped
  rw [if_pos hs, if_pos (le_trans hs (hστ ω)), sub_self]
end StoppedIncrement

section HitIndPullOut

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end HitIndPullOut

end LevyStochCalc.Brownian.Ito


