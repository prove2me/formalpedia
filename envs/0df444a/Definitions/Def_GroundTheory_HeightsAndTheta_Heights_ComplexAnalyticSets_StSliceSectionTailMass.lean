-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionTailMass
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionTailMass
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:17.952285+00:00
-- url     : https://prove2.me/theorems/dbbb1451-423e-47e0-a1e9-9a3808b8f4ee
-- title:
--   St Slice Section Tail Mass
-- statement:
--   Definitions and structural lemmas for St Slice Section Tail Mass, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceSectionTailMass.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
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
open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
def SliceSectionTailMass.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm u' ∉ W → linForm ℓ ∉ W →
    (∀ P ∈ (divCycle W u').support, linForm ℓ ∉ P) →
      ∀ P ∈ (divCycle W u').support,
        Tendsto (fun k => varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e (fun x => 1 - sliceCut h k x)
          (fun _ x => Real.log (h.dualNorm x))) atTop (𝓝 0)
end
end GroundTheory.Heights₂.Heights


