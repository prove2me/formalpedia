-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicFibreSumInt
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicFibreSumInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:43.660405+00:00
-- url     : https://prove2.me/theorems/bfac791a-3689-4660-afeb-fe62c7beac49
-- title:
--   St Holomorphic Fibre Sum Int
-- statement:
--   Definitions and structural lemmas for St Holomorphic Fibre Sum Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StHolomorphicFibreSumInt.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MeasureTheory ReciprocityTheory.AnForm.A
noncomputable section
def HolomorphicFibreSumInt.Statement : Prop :=
  ∀ (d : ℕ) (Ω : Set (Fin d → ℂ)) (τ : (Fin d → ℂ) → Fin d → ℂ) (H : (Fin d → ℂ) → ℝ),
    IsOpen Ω → DifferentiableOn ℂ τ Ω → (∀ y, {t | t ∈ Ω ∧ τ t = y}.Finite) →
    IntegrableOn (fun t => Complex.normSq (jacC τ t).det * H t) Ω →
      Integrable (fun y => ∑ᶠ t ∈ {t | t ∈ Ω ∧ τ t = y}, H t) ∧
        ∫ y, (∑ᶠ t ∈ {t | t ∈ Ω ∧ τ t = y}, H t) =
          ∫ t in Ω, Complex.normSq (jacC τ t).det * H t
end
end GroundTheory.Heights₂.Heights


