-- Prove2me | Definitions.Def_AJGames_Tensor
-- name    : AJGames_Tensor
-- status  : Definition
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:26:21.862791+00:00
-- url     : https://prove2.me/theorems/605ecab9-2400-40a7-868e-01596583a50b
-- title:
--   Tensor $A\otimes B$, implication and par of AJ games
-- statement:
--   The **tensor** $A\otimes B$ has moves $M_A\sqcup M_B$ with the inherited labels. A sequence $s$ is a position of $A\otimes B$ when three conditions hold:
--
--   1. its restriction $s{\restriction}A$ is a position of $A$, and $s{\restriction}B$ is a position of $B$;
--   2. consecutive moves have different labels;
--   3. whenever two consecutive moves lie in different components, the second is an Opponent move (only Opponent switches component).
--
--   **Linear implication** is $A\multimap B=(A\otimes B^\perp)^\perp$, and **par** is $A\mathbin{⅋}B=(A^\perp\otimes B^\perp)^\perp$.
--
--   The switching rule (3) is what distinguishes the AJ tensor from Conway's sum of games.
-- source:
--   S. Abramsky, R. Jagadeesan, Games and full completeness for multiplicative linear logic, J. Symbolic Logic 59(2) (1994) 543-574, https://arxiv.org/abs/1311.6057, §3.2 (tensor product, linear implication, par)

import Mathlib
import Definitions.Def_AJGames_Game

namespace AJGames

section Tensor

universe u
variable {α β : Type u}

/-- **Tensor transition relation** (Abramsky and Jagadeesan, *Games and Full Completeness for Multiplicative Linear Logic*, J. Symbolic Logic 59(2) (1994), 543–574, §3.2, tensor product; axioms T1 (alternation) and T2 (only Opponent switches component)). Consecutive moves `m, m'` of the tensor: alternately labelled, and *if they lie in different components,
`m'` is an Opponent move* (only Opponent may switch component). -/
def TR (la : α → Pl) (lb : β → Pl) (m m' : α ⊕ β) : Prop :=
  Sum.elim la lb m ≠ Sum.elim la lb m' ∧ (m.isLeft = m'.isLeft ∨ Sum.elim la lb m' = Pl.O)

/-- The restriction to the left component. -/
def projL (s : List (α ⊕ β)) : List α := s.filterMap Sum.getLeft?
/-- The restriction to the right component. -/
def projR (s : List (α ⊕ β)) : List β := s.filterMap Sum.getRight?

end Tensor

namespace Game


/-- **Tensor product** `A ⊗ B` (Abramsky and Jagadeesan, *Games and Full Completeness for Multiplicative Linear Logic*, J. Symbolic Logic 59(2) (1994), 543–574, §3.2).  disjoint union of moves; positions are alternately labelled interleavings whose
restrictions are positions of `A` and `B`, in which **only Opponent may switch component**. -/
@[reducible] def tensor (A B : Game) : Game where
  M := A.M ⊕ B.M
  lab := Sum.elim A.lab B.lab
  pos := {s | List.IsChain (TR A.lab B.lab) s ∧ projL s ∈ A.pos ∧ projR s ∈ B.pos}
  nil_mem := ⟨List.isChain_nil, A.nil_mem, B.nil_mem⟩
  prefix_closed := by
    rintro s t hst ⟨h1, h2, h3⟩
    refine ⟨h1.infix hst.isInfix, A.prefix_closed _ _ ?_ h2, B.prefix_closed _ _ ?_ h3⟩
    · exact hst.filterMap Sum.getLeft?
    · exact hst.filterMap Sum.getRight?
  alt := fun s hs => hs.1.imp fun a b h => h.1

/-- Linear implication `A ⊸ B := (A ⊗ B⊥)⊥`. -/
@[reducible] def imp (A B : Game) : Game := (tensor A B.dual).dual

/-- Par `A ⅋ B := (A⊥ ⊗ B⊥)⊥`. -/
@[reducible] def par (A B : Game) : Game := (tensor A.dual B.dual).dual

end Game

end AJGames


