-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelGoodPointGeneric
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelGoodPointGeneric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:57:26.267827+00:00
-- url     : https://prove2.me/theorems/ee70d7bb-8b1d-433a-943f-f9a967a5071c
-- title:
--   St Normal Model Good Point Generic
-- statement:
--   Definitions and structural lemmas for St Normal Model Good Point Generic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalModelGoodPointGeneric.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelDivisorGoodPoint
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
open MvPolynomial ComplexSets
noncomputable section
def NormalModelGoodPointGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ B : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ),
        M.ideal ⊔ Ideal.span {rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m) (linForm u)} ≤ B ∧
        ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) < (d : ℕ) ∧
        ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) = 0 →
          w ∉ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn B → NormalModelDivisorGoodPoint M u d w
end
end GroundTheory.Heights₂.Heights


