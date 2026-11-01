-- Prove2me | Definitions.Def_MaxEntCont_IsStable
-- name    : MaxEntCont_IsStable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:25.757455+00:00
-- url     : https://prove2.me/theorems/0c640250-bb91-4c87-ae66-3b64f8e30727
-- title:
--   Stable convex set (the mid-point map is open)
-- statement:
--   Let $C$ be a subset of a real normed space $X$, carrying the subspace topology. $C$ is **stable** if the mid-point map
--   $$
--   C\times C\to C,\qquad (x,y)\mapsto \tfrac12(x+y)
--   $$
--   is open, that is, it maps open subsets of $C\times C$ (product of the subspace topologies) to open subsets of $C$.
--
--   Stability is a regularity property of convex bodies: by Papadopoulou's theorem a convex body is stable exactly when its face function is lower semicontinuous. Every polytope and the quantum state space $\mathcal M_d$ are stable.
--
--   **Formalization Note** The definition is stated on sets, without proof terms: for all open $U,V\subseteq X$ there is an open $W\subseteq X$ with
--   $$
--   \{\tfrac12(x+y) : x\in U\cap C,\ y\in V\cap C\} = W\cap C .
--   $$
--   For a convex $C$ this is equivalent to the mid-point map $C\times C\to C$ being open: the sets $(U\cap C)\times(V\cap C)$ form a basis of the topology of $C\times C$, images commute with unions, and the open subsets of $C$ are exactly the traces $W\cap C$ of open subsets of $X$.
-- source:
--   Rodman, Spitkovsky, Szkoła, Weis, Continuity of the maximum-entropy inference, arXiv:1502.02018v1, (5.2), p. 13 (subspace topology, p. 5)

import Mathlib

namespace MaxEntCont

/-- **Stable convex set** (Rodman, Spitkovsky, Szkoła, Weis, *Continuity of the maximum-entropy inference*, arXiv:1502.02018v1, (5.2), p. 13): "A convex body `C` is stable if the mid-point
map `C × C → C, (x, y) ↦ ½(x + y)` is open", with the subspace topology on `C` and the product
topology on `C × C` (p. 5).

`IsStable C` says: for all open sets `U, V` of the ambient space there is an open set `W` with
`{½(x + y) : x ∈ U ∩ C, y ∈ V ∩ C} = W ∩ C`, i.e. the mid-point image of every basic open set
`(U ∩ C) × (V ∩ C)` of `C × C` is relatively open in `C`.

**Formalization Note** For convex `C` this is equivalent to the mid-point map `C × C → C` being
an open map: the sets `(U ∩ C) × (V ∩ C)` form a basis of the topology of `C × C`, images commute
with unions, and the relatively open subsets of `C` are exactly the traces `W ∩ C` of open `W`.
The set-level form avoids carrying a convexity proof in the definition. -/
def IsStable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] (C : Set X) : Prop :=
  ∀ U V : Set X, IsOpen U → IsOpen V →
    ∃ W : Set X, IsOpen W ∧
      (fun p : X × X => midpoint ℝ p.1 p.2) '' ((U ∩ C) ×ˢ (V ∩ C)) = W ∩ C

end MaxEntCont


