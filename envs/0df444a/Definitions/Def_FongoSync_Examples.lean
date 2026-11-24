-- Prove2me | Definitions.Def_FongoSync_Examples
-- name    : FongoSync_Examples
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:58:37.272255+00:00
-- url     : https://prove2.me/theorems/a95b99a7-c92f-4e81-b10d-78e3877245f0
-- title:
--   Examples
-- statement:
--   Definitions and structural lemmas for Examples, from bongofongo (bongofongo/fongo-sync; see pinned Apache-2.0 LICENSE-APACHE)'s pinned FongoSync local-first CRDT replication convergence laws development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Examples.lean

import Definitions.Def_FongoSync_View
set_option autoImplicit false
namespace FongoSync
example :
    let clock (wall : Nat) : Hlc := ⟨wall, 0, 1⟩
    let change (field : String) (value : Int) (wall : Nat) : Change Value :=
      ⟨"things", 0, field, .int value, clock wall⟩
    let σ : String → String → Strategy := fun _ f => if f = "high" then .max else .lww
    let state := merged σ
      [change "title" 9 1, change "title" 2 5, change "high" 9 1, change "high" 2 5]
    (state ("things", 0, "title")).map (·.value) = some (.int 2) ∧
      (state ("things", 0, "high")).map (·.value) = some (.int 9) := by
  decide
example :
    let σ : String → String → Strategy := fun _ _ => .max
    let state := merged σ
      [⟨"things", 0, DELETED, .int 1, ⟨1, 0, 1⟩⟩, ⟨"things", 0, DELETED, Value.int 0, ⟨2, 0, 1⟩⟩]
    (state ("things", 0, DELETED)).map (·.value) = some (.int 0) := by
  decide
example :
    let c₀ : Clock := ⟨⟨0, 0, 1⟩⟩
    let (a, c₁) := c₀.tick 1000
    let (b, c₂) := c₁.tick 900
    let (c, c₃) := c₂.tick 1000
    let (d, _) := c₃.tick 1001
    a < b ∧ b < c ∧ c < d ∧ d.counter = 0 := by
  decide
example : (((⟨⟨5, COUNTER_MAX, 1⟩⟩ : Clock).tick 5).1.wall, ((⟨⟨5, COUNTER_MAX, 1⟩⟩ : Clock).tick 5).1.counter) = (6, 0) := by
  decide
example :
    let c : Clock := ⟨⟨WALL_MAX, 5, 1⟩⟩
    c.observe ⟨WALL_MAX + 1, 0, 2⟩ = c ∧ c.last < ((c.observe ⟨WALL_MAX + 1, 0, 2⟩).tick 0).1 := by
  decide
example :
    let E : List Edge := [(5, 3), (9, 7), (3, 9), (12, 11)]
    canonical E 7 = 3 ∧ canonical E 5 = 3 ∧ canonical E 12 = 11 ∧ canonical E 4 = 4 := by
  decide
end FongoSync


