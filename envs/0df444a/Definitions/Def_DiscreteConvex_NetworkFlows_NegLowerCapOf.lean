-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlows_NegLowerCapOf
-- name    : DiscreteConvex_NetworkFlows_NegLowerCapOf
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:14:54.198461+00:00
-- url     : https://prove2.me/theorems/a9fb6c63-ea12-4991-a51f-0f5f69919832
-- title:
--   Negated total lower capacity of an arc set
-- statement:
--   $\sum_{a \in S} (-\underline c(a))$, the negated total lower capacity of an arc set $S$, landing in $\mathbb R \cup \{+\infty\}$ via `NegLowerToUpper` so it can be added to an `UpperCapOf` term.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlows_NegLowerToUpper

/-!
The negated total lower capacity of an arc set, in `DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- `Σ_{a ∈ S} (-c(a))`, the negated total lower capacity of an arc set `S`, landing in
`ℝ ∪ {+∞}` via `NegLowerToUpper`. -/
noncomputable def NegLowerCapOf {A : Type*} (cLower : A → WithBot ℝ) (S : Finset A) : WithTop ℝ :=
  ∑ a ∈ S, NegLowerToUpper (cLower a)

end DiscreteConvex.NetworkFlows


