-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegMassContinuous
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceRegMassContinuous
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:02.371939+00:00
-- url     : https://prove2.me/theorems/e7b2ead9-174a-4909-85e2-aefbeac5f692
-- title:
--   St Slice Reg Mass Continuous
-- statement:
--   Definitions and structural lemmas for St Slice Reg Mass Continuous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceRegMassContinuous.lean

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
def SliceRegMassContinuous.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ) (w : (Fin n → ℂ) → ℝ) (C : ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm ℓ ∉ W → Measurable w → (∀ x, |w x| ≤ C) →
      ContinuousOn (fun ε => varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) w
        (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x))) (Set.Ioi 0)
end
end GroundTheory.Heights₂.Heights


