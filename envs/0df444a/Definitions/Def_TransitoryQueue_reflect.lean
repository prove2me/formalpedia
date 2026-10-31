-- Prove2me | Definitions.Def_TransitoryQueue_reflect
-- name    : TransitoryQueue_reflect
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:23.742176+00:00
-- url     : https://prove2.me/theorems/7b7a1322-b79b-4242-80e1-ac3a424cc5b1
-- title:
--   The reflection map $\phi(f)(t)=f(t)-\inf_{u\le t}f(u)$
-- statement:
--   For a function $f$ on $[0,\infty)$, the **reflection map** (one-sided Skorokhod map) is
--
--   $$\phi(f)(t)=f(t)-\inf_{0\le u\le t}f(u),\qquad t\ge0.$$
--
--   It turns a netput process into a nonnegative content process: $\phi(W_n-c_n\cdot\mathrm{id})$ is the remaining workload of the queue.
--
--   **Formalization Note** The infimum is a real infimum over $[0,t]$. It is the true infimum whenever $f$ is bounded below on $[0,t]$, which holds for every process reflected in this mission; for $t<0$ the value is not used.
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, Theorem 2.10, p.7; Proposition 6.3, p.35

import Mathlib

namespace TransitoryQueue

/-- The reflection map `φ(f)(t) = f(t) - inf_{u ≤ t} f(u)` on `[0, ∞)`.
Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, Theorem 2.10, p.7 ("Let φ be the reflection map functional given by
φ(f)(t) := f(t) − inf_{u≤t} f(u)"), and Proposition 6.3, p.35.

**Formalization Note** Time runs over `[0, ∞)`, so the infimum is over `u ∈ [0, t]`, a
nonempty set for `t ≥ 0`. It is a real `⨅`: it is the genuine infimum when `f` is bounded
below on `[0, t]`, which holds for every process this mission reflects. -/
noncomputable def reflect (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  f t - ⨅ u : Set.Icc (0 : ℝ) t, f u

end TransitoryQueue


