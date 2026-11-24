-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StatementsBasicOpen
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StatementsBasicOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:23.939058+00:00
-- url     : https://prove2.me/theorems/0c2b787b-cdd1-456c-abc2-607333d54379
-- title:
--   Statements Basic Open
-- statement:
--   Definitions and structural lemmas for Statements Basic Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/StatementsBasicOpen.lean

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
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial
def IrreducibleBasicOpenConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (W : Ideal (MvPolynomial σ ℂ)) (g : MvPolynomial σ ℂ), W.IsPrime → g ∉ W →
    IsPreconnected (zeroLocus ℂ W \ {x : σ → ℂ | eval x g = 0})
end GroundTheory.Heights₂.Heights.HilbertSamuel


