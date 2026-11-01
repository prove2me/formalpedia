-- Prove2me | Definitions.Def_MaxEntCont_IsFace
-- name    : MaxEntCont_IsFace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:19.973355+00:00
-- url     : https://prove2.me/theorems/42421d6d-d472-47df-8693-48f1ef773116
-- title:
--   Face of a convex set
-- statement:
--   Let $C$ be a subset of a real vector space. A **face** of $C$ is a convex subset $F\subseteq C$ which contains every segment of $C$ that meets $F$ in an interior point: whenever $x_1,x_2\in C$ and some point of the open segment
--   $$
--   (x_1,x_2)=\{(1-t)x_1+t x_2 : 0<t<1\}
--   $$
--   lies in $F$, then $x_1\in F$ and $x_2\in F$ (and hence, by convexity, the whole segment $[x_1,x_2]$ lies in $F$).
--
--   The empty set and $C$ itself are faces of a convex set $C$. A face which is a single point is an extremal point. Faces are the building blocks of the face function $x\mapsto F(x)$, which assigns to each point of $C$ the unique face containing it in its relative interior.
--
--   **Formalization Note** `IsFace C F` is `Convex ℝ F ∧ IsExtreme ℝ C F`, where Mathlib's `IsExtreme ℝ C F` says $F\subseteq C$ and every open segment of $C$ meeting $F$ has both endpoints in $F$. The ambient set comes first.
-- source:
--   Rodman, Spitkovsky, Szkoła, Weis, Continuity of the maximum-entropy inference, arXiv:1502.02018v1, §3, p. 9, definition of a face (in text, citing Rockafellar [35])

import Mathlib

namespace MaxEntCont

/-- **Face** of a convex set (Rodman, Spitkovsky, Szkoła, Weis, *Continuity of the maximum-entropy inference*, arXiv:1502.02018v1, p. 9): "a face of a convex set `C` is any convex subset
`F ⊂ C` which contains all segments in `C` which meet `F` with an interior point".

`IsFace C F` holds when `F` is convex and `F` is an extreme subset of `C` in Mathlib's sense
(`IsExtreme ℝ C F`: `F ⊆ C`, and whenever a point of `F` lies in the open segment between two
points of `C`, both endpoints lie in `F`).

**Formalization Note** The ambient set comes first: `IsFace C F` says that `F` is a face of
`C`. The empty set is a face, as in the paper's source [35] (Rockafellar, §18). -/
def IsFace {X : Type*} [AddCommGroup X] [Module ℝ X] (C F : Set X) : Prop :=
  Convex ℝ F ∧ IsExtreme ℝ C F

end MaxEntCont


