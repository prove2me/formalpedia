-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemVarLat
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemVarLat
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:16:24.743661+00:00
-- url     : https://prove2.me/theorems/9a7ee25d-0d96-4cee-b35d-4e927e858101
-- title:
--   Mem Var Lat
-- statement:
--   Definitions and structural lemmas for Mem Var Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemVarLat.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
noncomputable section
namespace GlobalTheory.UnfoldLoss
open GlobalTheory.SplitFlip GlobalTheory.FunObj
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def varLat (G : Grid k) (ϖ : kˣ) (n : ℕ) : AddSubgroup (Vars G) where
  carrier := {e | ∀ j r, valuation k (e j r) ≤ valuation k ((ϖ ^ n : kˣ) : k)}
  zero_mem' := fun j r => by
    show valuation k 0 ≤ _
    simp
  add_mem' := fun {a b} ha hb j r => (Valuation.map_add _ _ _).trans (max_le (ha j r) (hb j r))
  neg_mem' := fun {a} ha j r => by
    show valuation k (-(a j r)) ≤ _
    rw [Valuation.map_neg]
    exact ha j r
def varCount (G : Grid k) : ℕ :=
  ∑ j : Fin (G.m - 1), Nat.card (StepVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j)))
end GlobalTheory.UnfoldLoss


