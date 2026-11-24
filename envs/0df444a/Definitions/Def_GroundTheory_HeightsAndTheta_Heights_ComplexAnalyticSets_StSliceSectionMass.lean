-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:32.863214+00:00
-- url     : https://prove2.me/theorems/34e71af9-2260-4760-9623-2f9d027fa0a3
-- title:
--   St Slice Section Mass
-- statement:
--   Definitions and structural lemmas for St Slice Section Mass, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceSectionMass.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
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
def SliceSectionMass.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u ℓ : Fin n → ℂ),
    IsProjPrime J → IsChowForm J (e + 2) F → linForm u ∉ J → linForm ℓ ∉ J →
    (∀ W ∈ (divCycle J u).support, linForm ℓ ∉ W) →
      varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun _ => 1)
          (fun _ x => Real.log (h.dualNorm x)) =
        ∑ W ∈ (divCycle J u).support, ((divCycle J u W : ℕ) : ℝ) *
          varInt (W ⊔ Ideal.span {linForm ℓ - 1}) e (fun _ => 1)
            (fun _ x => Real.log (h.dualNorm x))
end
end GroundTheory.Heights₂.Heights


