-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLength
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:57.035082+00:00
-- url     : https://prove2.me/theorems/c6cd923a-4777-40ff-af0b-308a89cbacff
-- title:
--   Induction Finite Length
-- statement:
--   Definitions and structural lemmas for Induction Finite Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InductionFiniteLength.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
namespace GlobalTheory.JacquetBlocks
section General
variable {F G H V W : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]
end General
section Blocks
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
end Blocks
section Transport
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β n n' : Type} {m : α → Type} {m' : β → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype β] [LinearOrder β]
  [∀ b, Fintype (m' b)] [∀ b, DecidableEq (m' b)] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {V : Type} [AddCommGroup V] [Module ℂ V]
end Transport
section Stages
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β n n' : Type} {m : α → Type} {m' : β → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype β] [LinearOrder β]
  [∀ b, Fintype (m' b)] [∀ b, DecidableEq (m' b)] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {V : Type} [AddCommGroup V] [Module ℂ V]
end Stages
end GlobalTheory.JacquetBlocks
end


