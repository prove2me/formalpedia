-- Prove2me | Definitions.Def_AJGames_Game
-- name    : AJGames_Game
-- status  : Definition
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:25:37.059105+00:00
-- url     : https://prove2.me/theorems/c9ea9c0a-045a-4a1c-8e81-c11fbd1f68f0
-- title:
--   Abramsky–Jagadeesan games (finite plays) and duality
-- statement:
--   A **game** $A=(M_A,\lambda_A,P_A)$ consists of a type of moves $M_A$, a labelling $\lambda_A:M_A\to\{P,O\}$ of each move as a Player or an Opponent move, and a set $P_A$ of finite sequences of moves (the **positions**). The positions satisfy three conditions:
--
--   1. the empty sequence is a position;
--   2. every prefix of a position is a position;
--   3. in every position, consecutive moves have different labels (alternation).
--
--   The **dual** $A^\perp$ has the same moves and positions, with every label swapped.
--
--   These are the arenas on which every strategy, tensor and online problem of the mission is built.
--
--   **Formalization Note** Only finite plays are represented: the set of infinite plays won by Player in the source is omitted, so this is the safety fragment of AJ games.
-- source:
--   S. Abramsky, R. Jagadeesan, Games and full completeness for multiplicative linear logic, J. Symbolic Logic 59(2) (1994) 543-574, https://arxiv.org/abs/1311.6057, §3.1 Definition 2 (without the set W of infinite winning plays), and §3.2 (linear negation)

import Mathlib

universe u

namespace AJGames

/-- Player or Opponent. -/
inductive Pl
  | P
  | O
  deriving DecidableEq

namespace Pl

/-- Swap the roles. -/
def flip : Pl → Pl
  | P => O
  | O => P

@[simp] theorem flip_flip (p : Pl) : p.flip.flip = p := by cases p <;> rfl

theorem flip_ne (p : Pl) : p.flip ≠ p := by cases p <;> decide

theorem ne_iff_flip_eq {p q : Pl} : p ≠ q ↔ p.flip = q := by cases p <;> cases q <;> decide

theorem flip_ne_flip {p q : Pl} : p.flip ≠ q.flip ↔ p ≠ q := by cases p <;> cases q <;> decide

end Pl

/-- `s` is an *alternately labelled* sequence of moves. -/
def Alt {α : Type u} (lab : α → Pl) (s : List α) : Prop :=
  List.IsChain (fun a b => lab a ≠ lab b) s

/-- **Game** (Abramsky and Jagadeesan, *Games and Full Completeness for Multiplicative Linear Logic*, J. Symbolic Logic 59(2) (1994), 543–574, §3.1, Definition 2, without the infinite-play set `W`; axioms G1, G2, G3 are the three fields `nil_mem`, `prefix_closed`, `alt`): moves `M`, a labelling `λ : M → {P,O}`, and a
non-empty prefix-closed set `P` of alternately labelled finite sequences. -/
structure Game where
  M : Type u
  lab : M → Pl
  pos : Set (List M)
  nil_mem : [] ∈ pos
  prefix_closed : ∀ s t : List M, s <+: t → t ∈ pos → s ∈ pos
  alt : ∀ s ∈ pos, Alt lab s

namespace Game

/-- Linear negation `A⊥`: swap the labelling, keep the positions. -/
@[reducible] def dual (A : Game) : Game where
  M := A.M
  lab := fun m => (A.lab m).flip
  pos := A.pos
  nil_mem := A.nil_mem
  prefix_closed := A.prefix_closed
  alt := fun s hs => (A.alt s hs).imp fun a b h => Pl.flip_ne_flip.2 h


end Game

end AJGames


