-- Prove2me | Definitions.Def_TransitoryQueue_rn
-- name    : TransitoryQueue_rn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:21.209427+00:00
-- url     : https://prove2.me/theorems/5bc78203-2a96-4c28-a12e-359856dbd0a8
-- title:
--   The uniform distance $r_n(G)=\sup_{t\ge0}|G^{(n)}(t)-G(t)|$
-- statement:
--   For distribution functions $G^{(n)}$ and $G$,
--
--   $$r_n(G)=\sup_{t\in[0,\infty)}\bigl|G^{(n)}(t)-G(t)\bigr|.$$
--
--   Assumption 2.5 requires $r_n(G)=O(1/\sqrt n)$; this is the rate at which the arrival distribution of the $n$-th system approaches its limit.
--
--   **Formalization Note** The supremum is taken over $t\ge0$ as a real supremum; the definition is only applied to distribution functions, whose values lie in $[0,1]$, so the supremum is that of a bounded set.
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, eq. (3), p.5

import Mathlib

namespace TransitoryQueue

/-- The uniform distance `r_n(G) = sup_{t ∈ [0, ∞)} |G^{(n)}(t) - G(t)|` between the arrival
distribution `Fn = G^{(n)}` of the `n`-th system and the limiting distribution `G`.
Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, eq. (3), p.5.

**Formalization Note** The supremum is a real `⨆` over `t ∈ [0, ∞)`. It is applied only to
distribution functions, whose values lie in `[0, 1]`, so the set is bounded and the supremum
is the genuine one. -/
noncomputable def rn (Fn G : ℝ → ℝ) : ℝ :=
  ⨆ t : Set.Ici (0 : ℝ), |Fn t - G t|

end TransitoryQueue


