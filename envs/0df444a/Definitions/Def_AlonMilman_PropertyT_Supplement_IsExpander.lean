-- Prove2me | Definitions.Def_AlonMilman_PropertyT_Supplement_IsExpander
-- name    : AlonMilman_PropertyT_Supplement_IsExpander
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T03:27:18.287986+00:00
-- url     : https://prove2.me/theorems/90cca64e-a121-4fb9-8e56-07668222f49f
-- title:
--   $(n,k,c)$-expander
-- statement:
--   Let $H$ be a bipartite graph with a set $X$ of inputs and a set $Y$ of outputs, every edge joining an input to an output. For $A \subseteq X$ let $N(A) \subseteq Y$ be the set of all neighbours of vertices of $A$. Following Gabber and Galil, $H$ is an **$(n, k, c)$-expander** if
--
--   1. $|X| = |Y| = n$;
--   2. $H$ has at most $k n$ edges;
--   3. every subset $A$ of inputs satisfies
--   $$|N(A)| \ \ge\ \Big(1 + c\Big(1 - \frac{|A|}{n}\Big)\Big) \cdot |A|.$$
--
--   Families of $(n_i, k, c)$-expanders with fixed $k$, $c > 0$ and $n_i \to \infty$ ("linear expanders") are the building block of linear superconcentrators.
--
--   **Formalization Note** The bipartite graph is given by its edge set $E \subseteq X \times Y$, so edges are counted without multiplicity and $N(A)$ is a set of distinct outputs. The condition is required for every $A \subseteq X$, including $A = \emptyset$ and $A = X$.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 82, Section 4 ((n, k, c)-expander)

import Mathlib

namespace AlonMilman.PropertyT.Supplement

/-- The set `N(A)` of all neighbours of a set `A` of inputs in a bipartite graph with inputs `X`
and outputs `Y`, given by its edge set `E ⊆ X × Y`. -/
def bipNeighbors {X Y : Type} [DecidableEq X] [DecidableEq Y] (E : Finset (X × Y))
    (A : Finset X) : Finset Y :=
  (E.filter (fun p => p.1 ∈ A)).image Prod.snd

/-- An `(n, k, c)`-expander (Alon–Milman 1985, Section 4, p. 82, following Gabber–Galil): a
bipartite graph with `n` inputs `X`, `n` outputs `Y` and at most `k n` edges, such that every
subset `A` of inputs satisfies `|N(A)| ≥ (1 + c (1 − |A|/n)) · |A|`. The bipartite graph is given
by its edge set `E ⊆ X × Y`. -/
def IsExpander {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (n k : ℕ) (c : ℝ) (E : Finset (X × Y)) : Prop :=
  Fintype.card X = n ∧ Fintype.card Y = n ∧ E.card ≤ k * n ∧
    ∀ A : Finset X,
      (1 + c * (1 - (A.card : ℝ) / (n : ℝ))) * (A.card : ℝ) ≤ ((bipNeighbors E A).card : ℝ)

end AlonMilman.PropertyT.Supplement


