-- Prove2me | Definitions.Def_NesterovSSAAudit_SSA_rawOracle
-- name    : NesterovSSAAudit_SSA_rawOracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:41:06.088476+00:00
-- url     : https://prove2.me/theorems/3a808ec0-5037-4151-97fc-91829113d349
-- title:
--   Pointwise bounded relative-subgradient oracle
-- statement:
--   Let $E$ be a real normed space, $Q\subseteq E$, $\Xi$ a sample carrier, $f:E\times\Xi\to\mathbb R$ a cost, $a:E\times\Xi\to E^*$ a specified oracle, and $L\ge0$. A raw oracle satisfies samplewise convexity on $Q$ and
--
--   $$f(x,\xi)+\langle a(x,\xi),y-x\rangle\le f(y,\xi),\qquad \|a(x,\xi)\|_*\le L\quad(x,y\in Q,\ \xi\in\Xi).$$
--
--   The relative-subgradient concept is the published arbitrary-norm predicate `ConvexOptAlg.StochMD.IsSubgradientOnN`; its reversed difference formula is equivalent by linearity. This layer contains no probability data or global oracle-measurability condition. It separates the pointwise requirements from the actual algorithm's random-state requirement. Off-$Q$ values are arbitrary extensions.
-- source:
--   Yu. Nesterov, Primal-dual subgradient methods for convex problems, September 2005 revised manuscript, SHA256 095a7bfedc1ebd85f8fbd9e7765194e180a95c38fdfbef172ecd27cbe920f96c, p.25, Assumptions 1–2

import Mathlib
import Definitions.Def_ConvexOptAlg_StochMD_Defs

set_option autoImplicit false

namespace NesterovSSAAudit.SSA

variable {E Ξ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- September 2005 manuscript, p.25, Assumptions 1–2, pointwise part only.
No measurability of the oracle, including at unqueried points, is required. -/
structure RawOracle (Q : Set E) (f : E → Ξ → ℝ)
    (a : E → Ξ → StrongDual ℝ E) (L : ℝ) : Prop where
  nonneg : 0 ≤ L
  convex : ∀ ξ, ConvexOn ℝ Q (fun x => f x ξ)
  subgrad : ∀ x ∈ Q, ∀ ξ, ConvexOptAlg.StochMD.IsSubgradientOnN Q (fun y => f y ξ) x (a x ξ)
  bound : ∀ x ∈ Q, ∀ ξ, ‖a x ξ‖ ≤ L

end NesterovSSAAudit.SSA


