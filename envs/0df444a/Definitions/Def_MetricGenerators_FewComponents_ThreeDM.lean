-- Prove2me | Definitions.Def_MetricGenerators_FewComponents_ThreeDM
-- name    : MetricGenerators_FewComponents_ThreeDM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:00:32.097931+00:00
-- url     : https://prove2.me/theorems/d5aa64cb-e59c-428c-9520-9f18e0ca436e
-- title:
--   Three-dimensional matching (§3.1, p. 390): M ⊆ W × X × Y in which every element of W ∪ X ∪ Y occurs exactly once
-- statement:
--   An instance of **THREE-DIMENSIONAL MATCHING (3DM)** consists of three finite pairwise disjoint sets $W$, $X$, $Y$, each of cardinality $q$, and a set of triples $H\subseteq W\times X\times Y$. A **matching** is a subset $M\subseteq H$ such that
--
--   $$\text{every } w\in W\cup X\cup Y \text{ occurs in exactly one element of } M.$$
--
--   Because $W$, $X$, $Y$ are disjoint, an element $w\in W$ occurs in a triple $(w',x,y)$ exactly when $w=w'$, and similarly for $X$ and $Y$. So $M$ is a matching when each $w\in W$ is the first coordinate of exactly one triple of $M$, each $x\in X$ the second coordinate of exactly one triple, and each $y\in Y$ the third coordinate of exactly one triple.
--
--   3DM is the NP-complete problem from which Sebő and Tannier reduce the problem MTSC (minimum $T$-joins with few components).
--
--   **Formalization Note.** $W$, $X$, $Y$ are three copies of $\{0,\dots,q-1\}$ (`Fin q`), so disjointness holds by construction, and triples are elements of `Fin q × Fin q × Fin q`. The predicate `IsMatching q M` is the "exactly one" condition; the condition $M\subseteq H$ is stated where the predicate is used.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 390, §3.1, proof of Theorem 5 (problem 3DM)

import Mathlib

namespace MetricGenerators.FewComponents

/-- A matching of an instance of THREE-DIMENSIONAL MATCHING (3DM) (Sebő and Tannier, On Metric
Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), §3.1, proof of Theorem 5, p. 390):
"Instance. Three finite and disjoint sets W, X, and Y of cardinality q, and H ⊆ W × X × Y.
Question. Is there a matching, that is, M ⊆ H, so that every w ∈ W ∪ X ∪ Y occurs in exactly one
element of M?"

**Formalization Note.** The three disjoint sets `W`, `X`, `Y` of cardinality `q` are relabeled as
three copies of `Fin q` (an element of `W` is a first coordinate, of `X` a second, of `Y` a third),
so their disjointness holds by construction and `H, M : Finset (Fin q × Fin q × Fin q)`. Because
the sets are disjoint, "`w ∈ W` occurs in the triple `m`" means that `w` is the first coordinate of
`m`, and similarly for `X` and `Y`. This predicate is the "exactly one" condition; the condition
`M ⊆ H` is stated separately where it is used. -/
def IsMatching (q : ℕ) (M : Finset (Fin q × Fin q × Fin q)) : Prop :=
  (∀ w : Fin q, (M.filter (fun m => m.1 = w)).card = 1) ∧
  (∀ x : Fin q, (M.filter (fun m => m.2.1 = x)).card = 1) ∧
  (∀ y : Fin q, (M.filter (fun m => m.2.2 = y)).card = 1)

end MetricGenerators.FewComponents


