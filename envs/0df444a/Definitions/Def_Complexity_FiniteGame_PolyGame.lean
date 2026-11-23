-- Prove2me | Definitions.Def_Complexity_FiniteGame_PolyGame
-- name    : Complexity_FiniteGame_PolyGame
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:37:39.033969+00:00
-- url     : https://prove2.me/theorems/cdc04f51-c9d3-4a71-be15-386519799b94
-- title:
--   Polynomially presented finite impartial games: binary positions, recursive outcomes, and resource bounds
-- statement:
--   This defines a reusable model for evaluating finite impartial games under normal play. An instance of type $\alpha$ has a binary encoding and an initial position. Positions are binary words, `next` lists legal successors, and a natural-number rank strictly decreases along every move. The recursive winning predicate is
--   $$
--   W(s)\quad\Longleftrightarrow\quad \exists t\in\operatorname{next}(s)\text{ such that }\neg W(t),
--   $$
--   with the recursion justified by the decreasing rank.
--
--   A **polynomially presented game** additionally has polynomials $B,D$ such that every valid position $s$ satisfies $|s|\le B(|x|)$ and $\operatorname{rank}(s)\le D(|x|)$, where $x$ is the encoded instance. One fixed multi-stack Turing machine, running in polynomial time, computes the complete successor list from $x$ and $s$. Both input and output use explicit self-delimiting binary codes. This is the data needed by depth-first game-tree evaluation: only the current root-to-leaf branch and its remaining successor lists need be retained.
--
--   The source application is Édouard Bonnet's Arc Kayles proof: a play has at most $N/2$ moves and a position can be described by $O(N^2)$ bits, yielding an $O(N^3)$-space DFS. The present interface abstracts exactly those depth, position-size, and move-generation requirements; it is not tied to graphs.
-- source:
--   Édouard Bonnet, Arc Kayles is PSPACE-complete, STOC 2027 submission #192 (October 2026), p.2 (positions and normal-play outcomes) and p.5, proof of Theorem 1 (DFS game-tree evaluation; position and depth bounds). The generic finite-game interface abstracts this argument.

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete

namespace Complexity.FiniteGame

open OptimalQueuingComplexity.Restless

/-- Self-delimiting binary code of a binary word: every bit `b` is written `1b`, and the word
ends with `00`. -/
def tagBits (w : List Bool) : List Bool :=
  w.flatMap (fun b => [true, b]) ++ [false, false]

/-- A list of binary words, encoded by concatenating their self-delimiting codes. -/
def encWords (ws : List (List Bool)) : List Bool := ws.flatMap tagBits

/-- An impartial finite game in normal play, on positions represented by binary words. The
predicate `valid` contains the initial position and is preserved by moves. Every move strictly
decreases `rank`, so there is no infinite play. -/
structure Game (α : Type) where
  enc : α → List Bool
  start : α → List Bool
  next : α → List Bool → List (List Bool)
  rank : α → List Bool → ℕ
  valid : α → List Bool → Prop
  start_valid : ∀ a, valid a (start a)
  next_valid : ∀ a s t, valid a s → t ∈ next a s → valid a t
  rank_next : ∀ a s t, t ∈ next a s → rank a t < rank a s

namespace Game

variable {α : Type}

/-- The player to move wins iff some legal move leads to a position from which the opponent does
not win. -/
def wins (G : Game α) (a : α) (s : List Bool) : Prop :=
  ∃ t, ∃ _ : t ∈ G.next a s, ¬ G.wins a t
termination_by G.rank a s
decreasing_by all_goals (rename_i h; exact G.rank_next a s t h)

end Game

/-- A polynomially presented finite game. Valid positions have length bounded by a polynomial in
the instance length and ranks bounded by another polynomial. A single polynomial-time machine,
given the self-delimiting instance code followed by a position, lists all its legal successors. -/
structure PolyGame (α : Type) extends Game α where
  positionBound : Polynomial ℕ
  depthBound : Polynomial ℕ
  start_length : ∀ a, (toGame.start a).length ≤
    Polynomial.eval (toGame.enc a).length positionBound
  next_length : ∀ a s t, toGame.valid a s → t ∈ toGame.next a s →
    t.length ≤ Polynomial.eval (toGame.enc a).length positionBound
  rank_bound : ∀ a s, toGame.valid a s →
    toGame.rank a s ≤ Polynomial.eval (toGame.enc a).length depthBound
  next_computable : Nonempty (Turing.TM2ComputableInPolyTime
    (fun x : α × List Bool => tagBits (toGame.enc x.1) ++ x.2)
    encWords
    (fun x => toGame.next x.1 x.2))

end Complexity.FiniteGame


