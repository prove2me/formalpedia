-- Prove2me | Definitions.Def_GroupTheoreticShannonCapacity_Main
-- name    : GroupTheoreticShannonCapacity_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T07:27:37.44004+00:00
-- url     : https://prove2.me/theorems/1e4db1fe-3971-4ffb-bee6-7f0b3c24f333
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from jzuiddam/GroupTheoreticShannonCapacity contributors (see pinned LICENSE and source headers)'s pinned Shannon capacity limits from lattice packings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Main.lean

import Definitions.Def_GroupTheoreticShannonCapacity_MainProofs
import Mathlib.Tactic.Recall
set_option autoImplicit true
namespace GroupTheoreticShannonCapacity.Main
open GroupTheoreticShannonCapacity MainProofs Lattice
section Definitions
variable {V : Type*}
example {G : Type*} [AddGroup G] [Fintype G] (Γ : SimpleGraph G) :
    addSubgroupIndependenceNumber Γ =
    sSup {n | ∃ H : AddSubgroup G, Γ.IsIndepSet (H : Set G) ∧ Nat.card H = n} := rfl
example {G : Type*} [AddGroup G] [Fintype G] (Γ : SimpleGraph G) :
    addSubgroupShannonCapacity Γ =
    ⨆ n : ℕ, (addSubgroupIndependenceNumber (strongPower Γ (n + 1)) : ℝ) ^ (1 / (n + 1 : ℝ)) := rfl
end Definitions
end GroupTheoreticShannonCapacity.Main


