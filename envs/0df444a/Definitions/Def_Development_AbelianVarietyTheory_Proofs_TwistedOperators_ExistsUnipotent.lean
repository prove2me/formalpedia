-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsUnipotent
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsUnipotent
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T10:34:36.781848+00:00
-- url     : https://prove2.me/theorems/4df01dbe-6e7f-4bdb-a348-36501850edaf
-- title:
--   Exists Unipotent
-- statement:
--   Definitions and structural lemmas for Exists Unipotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsUnipotent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
noncomputable section
namespace GlobalTheory.RootEx.UnfoldFlag
variable {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
def flagMat (y : Fin c → (n ⊕ Fin c → k)) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
  Matrix.of fun r s =>
    Sum.elim (fun s => (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (Sum.inl s)) (fun i => y i r) s
end GlobalTheory.RootEx.UnfoldFlag


