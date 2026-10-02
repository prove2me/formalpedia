-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlows_UpperCapOf
-- name    : DiscreteConvex_NetworkFlows_UpperCapOf
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:13:56.172491+00:00
-- url     : https://prove2.me/theorems/4d9f5de9-e08a-4b0f-a5b8-54229b7bf9a8
-- title:
--   Total upper capacity of an arc set
-- statement:
--   $\sum_{a \in S} \bar c(a)$, the total upper capacity of an arc set $S$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247

import Mathlib

/-!
The total upper capacity of an arc set, in `DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- `Σ_{a ∈ S} c̄(a)`, the total upper capacity of an arc set `S`. -/
noncomputable def UpperCapOf {A : Type*} (cUpper : A → WithTop ℝ) (S : Finset A) : WithTop ℝ :=
  ∑ a ∈ S, cUpper a

end DiscreteConvex.NetworkFlows


