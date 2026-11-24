-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsIrreducibleConnected
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsIrreducibleConnected
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:39.082804+00:00
-- url     : https://prove2.me/theorems/a0ac7d66-5255-42e5-976f-d800550bac74
-- title:
--   Statements Irreducible Connected
-- statement:
--   Definitions and structural lemmas for Statements Irreducible Connected, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsIrreducibleConnected.lean

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
def IrreducibleConnected.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (W J : Ideal (MvPolynomial σ ℂ)), W.IsPrime →
    IsPreconnected (zeroLocus ℂ W \ zeroLocus ℂ J)
end GroundTheory.Heights₂.Heights.HilbertSamuel


