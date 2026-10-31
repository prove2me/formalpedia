-- Prove2me | Definitions.Def_TransitoryQueue_IsArrivalCDF
-- name    : TransitoryQueue_IsArrivalCDF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:27.61438+00:00
-- url     : https://prove2.me/theorems/257b15f1-8241-4f0b-ad34-38c2184a830c
-- title:
--   Arrival-epoch distribution function supported on $[0,\infty)$
-- statement:
--   A function $F:\mathbb R\to\mathbb R$ is an **arrival distribution function** if
--
--   1. $F$ is nondecreasing;
--   2. $F$ is right-continuous at every point;
--   3. $F(t)=0$ for every $t\le 0$;
--   4. $F(t)\to 1$ as $t\to\infty$.
--
--   This is the distribution function $G$ of the arrival epochs in Assumption 2.1, and $G^{(n)}$ of Assumption 2.5, with the convention of Remark 2.6 that "arrivals are supported on $[0,\infty)$, that is, $G(0)=G^{(n)}(0)=0$".
--
--   **Formalization Note** The limit $0$ at $-\infty$ is implied by clause 3. The paper's extra conditions in Assumption 2.5 (strict monotonicity and Lipschitz continuity) are not part of this definition; the theorems of this mission do not need them.
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, Assumptions 2.1 and 2.5, p.5; Remark 2.6, p.5

import Mathlib
open Filter Topology

namespace TransitoryQueue

/-- `F` is the distribution function of an arrival epoch supported on `[0, ∞)`: it is
nondecreasing, right-continuous, vanishes on `(-∞, 0]` and tends to `1` at `+∞`.
Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, Assumptions 2.1 and 2.5, p.5, and Remark 2.6, p.5 ("arrivals are supported on
[0, ∞), that is, G(0) = G^{(n)}(0) = 0").

**Formalization Note** A distribution function on `ℝ` is a nondecreasing right-continuous
function with limits `0` at `-∞` and `1` at `+∞`; the limit at `-∞` is implied by
`F t = 0` for `t ≤ 0`, which is Remark 2.6's support condition. -/
def IsArrivalCDF (F : ℝ → ℝ) : Prop :=
  Monotone F ∧ (∀ t : ℝ, ContinuousWithinAt F (Set.Ici t) t) ∧ (∀ t : ℝ, t ≤ 0 → F t = 0) ∧
    Tendsto F atTop (𝓝 1)

end TransitoryQueue


