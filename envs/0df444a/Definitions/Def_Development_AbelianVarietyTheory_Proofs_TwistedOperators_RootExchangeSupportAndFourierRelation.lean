-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:13.912846+00:00
-- url     : https://prove2.me/theorems/48acc89c-4ed5-42bc-8714-9e634513da07
-- title:
--   Root Exchange Support And Fourier Relation
-- statement:
--   Definitions and structural lemmas for Root Exchange Support And Fourier Relation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeSupportAndFourierRelation.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
namespace GlobalTheory.RootEx.ExchangeSupport
section Algebra
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
def rowM (c p : ℕ) (u : n → k) : Matrix (Fin c) n k :=
  Matrix.of fun l s => if l.val + 1 = p then u s else 0
def colM (c p : ℕ) (β : n → k) : Matrix n (Fin c) k :=
  Matrix.of fun r i => if i.val + 1 = p then β r else 0
end Algebra
section Top
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
end Top
end GlobalTheory.RootEx.ExchangeSupport


