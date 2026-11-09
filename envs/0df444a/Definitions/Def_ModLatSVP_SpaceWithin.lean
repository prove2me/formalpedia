-- Prove2me | Definitions.Def_ModLatSVP_SpaceWithin
-- name    : ModLatSVP_SpaceWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:42.585315+00:00
-- url     : https://prove2.me/theorems/b80bf44f-89be-4a79-8f6b-94da40ddb022
-- title:
--   Working space of a Turing-machine run, with a write-only output stream
-- statement:
--   A multi-stack Turing machine (Mathlib's TM2) runs in **working space at most $S$** on an input if, along every configuration reachable from the initial configuration on that input,
--
--   1. the total length of all stacks other than the output stack is at most $S$, and
--   2. every step only appends to the output stack: the old output stack is a suffix of the new one.
--
--   The output stack is thus a write-only output stream that does not count toward working space, which is how the paper can enumerate all closest vectors, possibly exponentially many, in polynomial space.
--
--   **Formalization Note** Mathlib has no space measure for TM2, so this one is local. Stack length counts cells faithfully up to a constant, since a TM2 pushes values computed from its finite internal state. The input stack counts toward the budget; the budgets used are polynomial in the input length, so this costs nothing. Without the append-only clause the output stack could serve as unbounded scratch space.
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), §2.1, p.11 (PDF p.11); Lemma 3.3, p.18

import Mathlib

namespace ModLatSVP

/-- Working space of a TM2 run, with a write-only output stream. Kim, Lee, Son, *Exact SVP and CVP in
Structured Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript
sha256 e7151fad…), §2.1, p.11 (PDF p.11): "all algorithms use polynomial working space … A write-only
output stream is excluded from working space, allowing all closest vectors to be enumerated without
storing the entire list."

`SpaceWithin M inp S` says that along every configuration reachable from the initial configuration on
input `inp`:
1. the total length of all stacks other than the output stack is at most `S`;
2. every step leaves the old output stack a suffix of the new one (the output is append-only).

**Formalization Note.** Mathlib has no space measure for TM2, so this one is local. Stack length counts
cells faithfully up to a constant: a TM2 pushes values computed from its finite internal state, so only
finitely many symbols ever occur. The input stack counts toward the budget, which costs nothing since
the budgets are at least the input length. Without the append-only clause the output stack could be
used as unbounded scratch space. -/
def SpaceWithin (M : Turing.TM2ComputableAux Bool Bool) (inp : List Bool) (S : ℕ) : Prop :=
  ∀ c : M.tm.Cfg, Relation.ReflTransGen (fun a b => M.tm.step a = some b)
      (Turing.initList M.tm (inp.map M.inputAlphabet.invFun)) c →
    (∑ k ∈ (@Finset.univ M.tm.K M.tm.kFin).erase M.tm.k₁, (c.stk k).length) ≤ S ∧
    ∀ c', M.tm.step c = some c' → c.stk M.tm.k₁ <:+ c'.stk M.tm.k₁

end ModLatSVP


