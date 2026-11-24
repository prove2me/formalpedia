-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadical
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadical
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:10.370749+00:00
-- url     : https://prove2.me/theorems/922e427c-b821-464f-bb49-99f5d8570841
-- title:
--   St Generic Fibre Radical
-- statement:
--   Definitions and structural lemmas for St Generic Fibre Radical, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StGenericFibreRadical.lean

import Mathlib
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
open MvPolynomial
noncomputable section
def GenericFibreRadical.Statement : Prop :=
  ∀ (σ : Type) [Finite σ] (ι : Type) [Finite ι] (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))),
    K.IsRadical → ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
      (K.map (MvPolynomial.map (eval t))).IsRadical
end
end GroundTheory.Heights₂.Heights


