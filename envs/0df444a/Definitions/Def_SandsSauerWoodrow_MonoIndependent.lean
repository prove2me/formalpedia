-- Prove2me | Definitions.Def_SandsSauerWoodrow_MonoIndependent
-- name    : SandsSauerWoodrow_MonoIndependent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-17T01:04:00.244608+00:00
-- url     : https://prove2.me/theorems/4dfe3ea3-927f-4c20-bce4-4ffdcd3baa7c
-- title:
--   Monochromatic independence and infinite outward paths
-- statement:
--   Two notions are introduced, both for a digraph $D$ on a set $V$ of vertices whose arcs are coloured with values in $\{0,1,2\}$.
--
--   **Monochromatic independence.** A set $S$ of vertices is *monochromatically independent* when no two distinct vertices $x, y \in S$ are connected by a monochromatic directed path in either direction: there is neither a directed path from $x$ to $y$ nor one from $y$ to $x$ all of whose arcs carry one common colour. This is the notion of independence used by Sands, Sauer and Woodrow (J. Combin. Theory Ser. B **33** (1982), 271–275, p. 271). It is weaker than graph independence — it forbids monochromatic paths, not arcs — but in a tournament every two distinct vertices are joined by an arc, so a tournament's monochromatically independent sets have at most one element. That is why the tournament corollary of the same paper concludes with a single vertex.
--
--   **No monochromatic infinite outward path.** A digraph has *no monochromatic infinite outward path* when there is no colour $k$ and no injective sequence $x_0, x_1, x_2, \dots$ of vertices such that every consecutive arc $x_n \to x_{n+1}$ has colour $k$. Injectivity is what makes the sequence a path rather than a walk: in the source a path has pairwise distinct vertices. This is the hypothesis of the paper's Theorem 1; it is vacuous when the vertex set is finite.
--
--   **Formalization Note.** Both notions are stated for an arbitrary vertex type and refer to the platform definitions `Digraph`, `ArcColoring` and `MonochromaticallyReaches`, the last being reachability along arcs of a single colour.
-- source:
--   B. Sands, N. Sauer, R. Woodrow, On monochromatic paths in edge-coloured digraphs, J. Combin. Theory Ser. B 33 (1982), no. 3, 271-275. Theorem 1 (pp. 271-273); Corollary 2 (p. 273); Theorem 3 (pp. 274-275); PROBLEM (p. 275).

import Definitions.Def_opg1808_colored_tournaments

/-! Monochromatic independence and infinite outward paths for arc-coloured digraphs,
following B. Sands, N. Sauer and R. Woodrow, *On monochromatic paths in edge-coloured
digraphs*, J. Combin. Theory Ser. B 33 (1982), 271-275. -/

universe u

namespace SandsSauerWoodrow

open OPG1808

/-- A set of vertices is monochromatically independent when no two of its distinct
members are connected by a monochromatic directed path in either direction. This is
the notion of independence used in the source; it is not graph independence. -/
def MonoIndependent {V : Type u} (D : Digraph V) (color : ArcColoring V) (S : Set V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
    ¬ MonochromaticallyReaches D color x y ∧ ¬ MonochromaticallyReaches D color y x

/-- A digraph has no monochromatic infinite outward path when there is no injective
sequence of vertices whose consecutive arcs all carry one common colour. -/
def NoMonoInfiniteOutwardPath {V : Type u} (D : Digraph V) (color : ArcColoring V) : Prop :=
  ¬ ∃ (x : ℕ → V) (k : Fin 3), Function.Injective x ∧
      ∀ n : ℕ, D (x n) (x (n + 1)) ∧ color (x n) (x (n + 1)) = k

end SandsSauerWoodrow


