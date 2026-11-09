-- Prove2me | Definitions.Def_HypRecov_SpaceWithin
-- name    : HypRecov_SpaceWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:49.867603+00:00
-- url     : https://prove2.me/theorems/50125173-65a6-46ff-8a59-71696d5197dd
-- title:
--   Working space of a Turing machine run
-- statement:
--   $\mathrm{SpaceWithin}(M,\mathit{inp},S)$ says that in every configuration reachable from the initial configuration of $M$ on input $\mathit{inp}$, the total length of all stacks, the input and output stacks included, is at most $S$ bits.
--
--   Theorem 1.1 bounds "its total working space, including random descriptions and decoding workspace". Counting the input stack charges the random description read by the initializer and the state read by the decoder; counting the output stack charges the decoder's output.
--
--   **Formalization Note** Mathlib has no space measure for TM2, so this one is local. A TM2 machine has finitely many internal states, so the stack contents measure its memory up to a constant.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem 1.1, p.2 (PDF p.3)

import Mathlib

namespace HypRecov

/-- **Working space of a machine run.** Zhang, Chen, Shen, *Hypergraph Recovery from Anonymous
Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Theorem 1.1, p.2 (PDF p.3):
"Its total working space, including random descriptions and decoding workspace, is
O(nrk polylog(nrk/η)) bits."

`SpaceWithin M inp S`: in every configuration reachable from the initial configuration of `M` on
input `inp`, the total length of **all** stacks, input and output stacks included, is at most `S`.

**Formalization Note.** Mathlib has no space measure for TM2, so this one is local. All stacks count,
so the input (for the initializer: the random description) and the output are charged to the budget.
A TM2 has finitely many internal states, so stack length measures space up to a constant. -/
def SpaceWithin (M : Turing.TM2ComputableAux Bool Bool) (inp : List Bool) (S : ℕ) : Prop :=
  ∀ c : M.tm.Cfg, Relation.ReflTransGen (fun a b => M.tm.step a = some b)
      (Turing.initList M.tm (inp.map M.inputAlphabet.invFun)) c →
    (∑ k ∈ @Finset.univ M.tm.K M.tm.kFin, (c.stk k).length) ≤ S

end HypRecov


