-- Prove2me | Definitions.Def_ArcKayles192_PSPACE_Supplement_Misere
-- name    : ArcKayles192_PSPACE_Supplement_Misere
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:18:11.71347+00:00
-- url     : https://prove2.me/theorems/2b9c4f2d-139f-4a85-a07d-27f41a910ec0
-- title:
--   Arc Kayles under misère play: outcome and the decision problem MISÈRE ARC KAYLES
-- statement:
--   **Misère Arc Kayles** is played like Arc Kayles: on a finite simple graph, two players alternate, and a move picks an edge $uv$ of the current graph and deletes both endpoints $u$ and $v$. Under **misère play** the first player without a legal move (the current graph is edgeless) **wins**.
--
--   1. **Positions.** As in the published normal-play game layer, fix an ambient simple graph $G$ on a vertex type with decidable equality. A position is a finite set $S$ of remaining vertices, the current graph is $G[S]$, a legal move from $S$ is a pair $u,v\in S$ with $uv\in E(G)$, and it leads to $S\setminus\{u,v\}$. Isolated vertices stay in $S$ and carry no move.
--   2. **Misère outcome.** $\mathrm{FirstPlayerWinsMisere}(G,S)$ is defined by backward induction on $|S|$:
--   $$\mathrm{FirstPlayerWinsMisere}(G,S)\iff \bigl(G[S]\ \text{has no edge}\bigr)\ \lor\ \exists\,u,v\in S,\ uv\in E(G),\ \neg\,\mathrm{FirstPlayerWinsMisere}(G,S\setminus\{u,v\}).$$
--   It says that the player to move has a winning strategy under misère play.
--   3. **The decision problem.** MISÈRE ARC KAYLES asks, for a graph instance $I$ (the published adjacency-matrix instances with their published encoding), whether $\mathrm{FirstPlayerWinsMisere}(G_I,V(G_I))$ holds.
--
--   The misère outcome is not the negation of the normal-play outcome, and it is not a function of the Sprague–Grundy value; it is defined directly by its own recursion.
--
--   **Formalization Note** The recursion terminates by the published lemma that removing an endpoint lying in $S$ strictly shrinks $S$. Instances, their graph and their encoding are imported from the published definition `ArcKayles192_PSPACE_Game`, so Theorem 1 and Theorem 11 are stated over the same inputs.
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), source.pdf SHA-256 f8b3a1c14347452b03dab2f19656aa6d2b17ba3956fefe2abc190b98ce44fc53, p.9 (misère variant: "the first player without a legal move wins"), p.1 and p.3 (game, isolated vertices)

import Mathlib
import Definitions.Def_ArcKayles192_PSPACE_Game

namespace ArcKayles192.PSPACE.Supplement

/-! # Arc Kayles under misère play

Same positions and moves as the published normal-play game layer
(`ArcKayles192.PSPACE.FirstPlayerWins`): a position on an ambient simple graph `G` is the finite
set `S` of remaining vertices, and a move picks an edge `uv` of `G` with `u, v ∈ S` and leads to
`S \ {u, v}`. Only the end-of-play convention changes: under misère play the first player without
a legal move **wins**. -/

section Game

variable {V : Type*} [DecidableEq V]

/-- **Misère play outcome.** `FirstPlayerWinsMisere G S` holds when the player to move at the
position `S` (current graph `G[S]`) has a winning strategy in Arc Kayles under misère play (the
first player without a legal move wins). Defined by backward induction on `|S|`: the player to
move wins iff either there is no legal move at `S` (no edge of `G` with both ends in `S`), or some
legal move `uv` leads to a position from which the opponent, then to move, does not win under
misère play. -/
def FirstPlayerWinsMisere (G : SimpleGraph V) (S : Finset V) : Prop :=
  (∀ u v, u ∈ S → v ∈ S → ¬ G.Adj u v) ∨
    ∃ u v, ∃ _ : u ∈ S ∧ v ∈ S ∧ G.Adj u v, ¬ FirstPlayerWinsMisere G (S \ {u, v})
termination_by S.card
decreasing_by all_goals (rename_i h; exact card_sdiff_pair_lt _ h.1)

end Game

/-- The decision problem MISÈRE ARC KAYLES: does the player to move (the first player) win Arc
Kayles under misère play on the whole graph of the instance? Instances and their encoding are the
published `GraphInstance` and `GraphInstance.enc`. -/
def misereArcKayles (I : GraphInstance) : Prop :=
  FirstPlayerWinsMisere I.graph Finset.univ

end ArcKayles192.PSPACE.Supplement


