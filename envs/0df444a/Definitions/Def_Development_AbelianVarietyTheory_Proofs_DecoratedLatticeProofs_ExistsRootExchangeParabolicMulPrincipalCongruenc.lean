-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsRootExchangeParabolicMulPrincipalCongruenc
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsRootExchangeParabolicMulPrincipalCongruenc
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T11:03:55.157808+00:00
-- url     : https://prove2.me/theorems/41ba2c07-2d0b-5310-8c24-3d21564d5b0a
-- title:
--   Exists Root Exchange Parabolic Mul Principal Congruenc
-- statement:
--   Definitions and structural lemmas for Exists Root Exchange Parabolic Mul Principal Congruenc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsRootExchangeParabolicMulPrincipalCongruenc.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
namespace GlobalTheory.SymChain.ResidueLift
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
def blockIx (p : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * p) (fun i => 2 * (i.val + 1) + 1)
end GlobalTheory.SymChain.ResidueLift
namespace GlobalTheory.SymChain.ResidueLift
end GlobalTheory.SymChain.ResidueLift


