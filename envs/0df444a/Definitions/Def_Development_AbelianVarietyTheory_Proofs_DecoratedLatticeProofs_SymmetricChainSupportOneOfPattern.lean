-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T10:34:41.244138+00:00
-- url     : https://prove2.me/theorems/2a54a0a7-15d8-5b79-a086-0b8be549655d
-- title:
--   Symmetric Chain Support One Of Pattern
-- statement:
--   Definitions and structural lemmas for Symmetric Chain Support One Of Pattern, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainSupportOneOfPattern.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
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
namespace GlobalTheory.SymSupport
section Plain
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
def InR (g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) : Prop :=
  (∀ l s, g (.inr l) (.inl s) = 0) ∧
    ∀ r i, lev 1 (Sum.inr i : n ⊕ Fin c) ≤ lev 1 r → g r (.inr i) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i)
end Plain
section Local
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
end Local
section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Main
end GlobalTheory.SymSupport


