-- Prove2me | Definitions.Def_C6BipartiteDomination_Corona
-- name    : C6BipartiteDomination_Corona
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:40:21.52089+00:00
-- url     : https://prove2.me/theorems/ff04780b-ea3b-4612-9bda-f1539ac48172
-- title:
--   Corona
-- statement:
--   Definitions and structural lemmas for Corona, from shouanrenhechun and contributors (shouanrenhechun/Myproofone; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bipartite domination constant c_6 = 8/15 for graphs of maximum degree at most six development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/Corona.lean

import Definitions.Def_C6BipartiteDomination_Basic
import Mathlib.Tactic.FinCases
set_option autoImplicit true
namespace C6BipartiteDomination
abbrev CoronaVertex := Fin 5 ⊕ (Fin 5 × Fin 2)
def coronaAdj : CoronaVertex → CoronaVertex → Prop
  | .inl i, .inl j => i ≠ j
  | .inl i, .inr (j, _) => i = j
  | .inr (i, _), .inl j => i = j
  | .inr _, .inr _ => False
instance : DecidableRel coronaAdj := by
  intro u v
  cases u <;> cases v <;> simp [coronaAdj] <;> infer_instance
instance : DecidableEq CoronaVertex := inferInstance
def coronaGraph : SimpleGraph CoronaVertex where
  Adj := coronaAdj
  symm := by
    constructor
    intro u v h
    cases u with
    | inl i => cases v with
      | inl j => exact (ne_comm.mp h)
      | inr p => exact h.symm
    | inr p => cases v with
      | inl j => exact h.symm
      | inr q => exact h.elim
  loopless := by
    constructor
    intro u h
    cases u with
    | inl i => simp [coronaAdj] at h
    | inr p => simp [coronaAdj] at h
def coronaWitness : Finset CoronaVertex :=
  {Sum.inl 0, Sum.inl 1,
   Sum.inr (2, 0), Sum.inr (2, 1),
   Sum.inr (3, 0), Sum.inr (3, 1),
   Sum.inr (4, 0), Sum.inr (4, 1)}
end C6BipartiteDomination


