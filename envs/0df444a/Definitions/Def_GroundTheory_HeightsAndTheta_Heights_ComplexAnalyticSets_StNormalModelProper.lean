-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelProper
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelProper
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:08.602073+00:00
-- url     : https://prove2.me/theorems/3cb83eff-34b7-4266-9320-5eaf1b3a1681
-- title:
--   St Normal Model Proper
-- statement:
--   Definitions and structural lemmas for St Normal Model Proper, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalModelProper.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
def NormalModelProper.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : NormalModel J) (K : Set (Fin n → ℂ)),
    Bornology.IsBounded K →
      Bornology.IsBounded {w : Fin n ⊕ Fin M.m → ℂ | w ∈ zeroSetIn M.ideal ∧ firstCoords w ∈ K}
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


