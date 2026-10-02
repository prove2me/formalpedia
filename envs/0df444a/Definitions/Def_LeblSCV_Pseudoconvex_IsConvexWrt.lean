-- Prove2me | Definitions.Def_LeblSCV_Pseudoconvex_IsConvexWrt
-- name    : LeblSCV_Pseudoconvex_IsConvexWrt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T04:09:38.64541+00:00
-- url     : https://prove2.me/theorems/433569cb-54d8-4da8-aa67-d42aed397232
-- title:
--   Definition 2.5.1 — convexity with respect to a class $\mathcal{F}$
-- statement:
--   Let $\mathcal{F}$ be a class of extended-real-valued functions on an open set $U$. Then $U$ is **convex with respect to $\mathcal{F}$** if, for every $K \subset\subset U$, the hull is also relatively compact:
--   $$K \subset\subset U \implies \widehat{K} \subset\subset U.$$
--
--   With $\mathcal{F}$ the plurisubharmonic functions on $U$, this is condition (iii) of Theorem 2.5.6.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 90, Definition 2.5.1

import Mathlib
import Definitions.Def_LeblSCV_Pseudoconvex_hull
import Definitions.Def_LeblSCV_Pseudoconvex_IsRelCompactIn

namespace LeblSCV.Pseudoconvex

/-- Definition 2.5.1 (Lebl, p. 90), convexity: an open set `U` is *convex with respect to* `𝓕`
if for every `K ⊂⊂ U`, the hull `K̂ ⊂⊂ U`. -/
def IsConvexWrt {X : Type*} [TopologicalSpace X] (U : Set X) (𝓕 : Set (X → EReal)) : Prop :=
  ∀ K : Set X, IsRelCompactIn K U → IsRelCompactIn (hull U 𝓕 K) U

end LeblSCV.Pseudoconvex


