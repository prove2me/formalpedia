-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConjIntNum
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConjIntNum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:07.35812+00:00
-- url     : https://prove2.me/theorems/275d5be7-687e-4b3b-98d5-9c79f345b490
-- title:
--   Statements Conj Int Num
-- statement:
--   Definitions and structural lemmas for Statements Conj Int Num, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsConjIntNum.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial
noncomputable section
def ConjIntNum.Statement : Prop :=
  ∀ (K : Type) [DecidableEq K] (ι : K → Type) (F : Type) [Field F] (τ : F ≃+* F)
    (J : Ideal (MvPolynomial (Σ k, ι k) F)) (n : ℕ) (bs : Fin n → K → ℤ),
    NumbersDVR.intNum F (J.map (MvPolynomial.map (τ : F →+* F))) bs = NumbersDVR.intNum F J bs
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


