-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBandAbsEnergy
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBandAbsEnergy
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:54.082955+00:00
-- url     : https://prove2.me/theorems/5d87e689-eb11-4149-abf2-59ecd2a7e9b1
-- title:
--   St Slice Band Abs Energy
-- statement:
--   Definitions and structural lemmas for St Slice Band Abs Energy, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceBandAbsEnergy.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
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
open MvPolynomial Matrix
noncomputable section
def SliceBandAbsEnergy.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u ℓ : Fin n → ℂ),
    IsProjPrime J → IsChowForm J (e + 2) F → linForm u ∉ J → linForm ℓ ∉ J →
    (∀ W ∈ (divCycle J u).support, linForm ℓ ∉ W) →
      ∃ C : ℝ, ∀ a b : ℝ, a ≤ b →
        varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1)
              (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
                {y | a ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b}.indicator (fun _ => 1) x)
              (vecCons (fun x => Real.log (h.dualNorm x) ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) -
            varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1)
              (fun x => |Real.log (h.dualNorm x) - Real.log ‖linEval u x‖| *
                {y | a ≤ Real.log (h.dualNorm y) ∧ Real.log (h.dualNorm y) ≤ b}.indicator (fun _ => 1) x *
                  Real.log (h.dualNorm x))
              (fun _ x => Real.log (h.dualNorm x)) ≤ C * (b - a + 1)
end
end GroundTheory.Heights₂.Heights


