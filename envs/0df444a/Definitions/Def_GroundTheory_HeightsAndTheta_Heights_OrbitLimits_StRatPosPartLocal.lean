-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatPosPartLocal
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatPosPartLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:04.468797+00:00
-- url     : https://prove2.me/theorems/aadd84f1-c1f8-44d8-911b-2e7ef7d3bd47
-- title:
--   St Rat Pos Part Local
-- statement:
--   Definitions and structural lemmas for St Rat Pos Part Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StRatPosPartLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RatChartObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPosPartIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory
def RatChart.ratPosDens {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  RatChart.ratSheetSum J p q (fun x s => max (f x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y
def RatPosPartLocal.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (x : Fin n → ℂ),
    Measurable f → (∀ k, SmoothNear (ComplexSets.zeroSet J) (φ k)) →
    (∃ s, IsSheetAt J A x s) → (∃ s', RatChart.IsRatSheetAt J p q x s') →
      ∃ W : Set (Fin n → ℂ), IsOpen W ∧ x ∈ W ∧
        ∀ E : Set (Fin n → ℂ), MeasurableSet E → E ⊆ W →
          ∫⁻ y, ENNReal.ofReal (chartPosDens J A (E.indicator f) φ y) =
            ∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q (E.indicator f) φ y)
end GroundTheory.Heights₂.Heights


