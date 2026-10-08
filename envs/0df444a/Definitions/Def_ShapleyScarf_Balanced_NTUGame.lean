-- Prove2me | Definitions.Def_ShapleyScarf_Balanced_NTUGame
-- name    : ShapleyScarf_Balanced_NTUGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:52.147977+00:00
-- url     : https://prove2.me/theorems/5902832e-85cd-44bf-9f73-a89536f19c4a
-- title:
--   Section 3 — games without side payments
-- statement:
--   Let $N$ be a finite trader set and let $V(S)\subseteq\mathbb R^N$ be the payoff set for each coalition $S\subseteq N$. The coordinate subspace $E^S$ consists of vectors whose coordinates outside $S$ vanish. The individual-interior union for $S$ is the union of the interiors of $V(\{i\})$ over $i\in S$.
--
--   A **game without side payments** satisfies, for every nonempty $S$,
--
--   $$
--   V(S)\text{ is closed},\qquad
--   x\in V(S),\ y_i\le x_i\ (i\in S)\ \Longrightarrow\ y\in V(S),
--   $$
--   and the set $\bigl[V(S)\setminus\bigcup_{i\in S}\operatorname{int}V(\{i\})\bigr]\cap E^S$ is bounded and nonempty.
--
--   This definition is the general game object used to state the paper's market theorem. The set $E^S$ is represented by zeroing coordinates outside $S$; interiors are taken in $\mathbb R^N$.
-- source:
--   Shapley and Scarf, On cores and indivisibility, J. Math. Econ. 1 (1974), DOI 10.1016/0304-4068(74)90033-0; p. 107 of the source printing, Section 3, conditions (a)–(c)

import Mathlib

namespace ShapleyScarf.Balanced

def coordinateSlice {N : Type*} [Fintype N] (S : Finset N) : Set (N → ℝ) :=
  {x | ∀ j, j ∉ S → x j = 0}

def singletonInteriorUnion {N : Type*} [Fintype N] [DecidableEq N]
    (V : Finset N → Set (N → ℝ)) (S : Finset N) : Set (N → ℝ) :=
  ⋃ i ∈ (S : Set N), interior (V {i})

def IsNTUGame {N : Type*} [Fintype N] [DecidableEq N]
    (V : Finset N → Set (N → ℝ)) : Prop :=
  ∀ S : Finset N, S.Nonempty →
    IsClosed (V S) ∧
    (∀ x y : N → ℝ, x ∈ V S → (∀ i ∈ S, y i ≤ x i) → y ∈ V S) ∧
    Bornology.IsBounded ((V S \ singletonInteriorUnion V S) ∩ coordinateSlice S) ∧
    ((V S \ singletonInteriorUnion V S) ∩ coordinateSlice S).Nonempty

end ShapleyScarf.Balanced


