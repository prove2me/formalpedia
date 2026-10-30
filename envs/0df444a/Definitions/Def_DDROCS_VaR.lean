-- Prove2me | Definitions.Def_DDROCS_VaR
-- name    : DDROCS_VaR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:28:47.040957+00:00
-- url     : https://prove2.me/theorems/b2605dbb-2387-45e2-b456-3d3903831b89
-- title:
--   Value at Risk $\mathrm{VaR}^{\mathbb P}_\epsilon(v)$
-- statement:
--   Let $\mathbb P$ be a probability measure on $\mathbb R^d$, the law of a random vector $\tilde u$, and let $v \in \mathbb R^d$ and $\epsilon \in \mathbb R$. The **Value at Risk** of $\tilde u^\top v$ at level $\epsilon$ is
--
--   $$
--   \mathrm{VaR}^{\mathbb P}_\epsilon(v) \;=\; \inf\bigl\{\, t \in \mathbb R : \mathbb P(\tilde u^\top v \le t) \ge 1-\epsilon \,\bigr\}.
--   $$
--
--   It is the $(1-\epsilon)$-quantile of $\tilde u^\top v$. The uncertainty sets of the paper are built so that their support function dominates the worst case of $\mathrm{VaR}^{\mathbb P}_\epsilon$ over a confidence region of distributions.
--
--   **Formalization Note** The event $\{\tilde u^\top v \le t\}$ is the closed half-space $\{u : \langle u, v\rangle \le t\}$ of `EuclideanSpace ℝ (Fin d)`. The infimum is a real `sInf`. For a probability measure and $0<\epsilon<1$ the set of such $t$ is nonempty and bounded below, so the value is the true infimum; Lean's default value $0$ occurs only for $\epsilon \le 0$ or $\epsilon \ge 1$, where no statement of the mission relies on it.
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, eq. (6), p. 10

import Mathlib
open MeasureTheory InnerProductSpace

namespace DDROCS

/-- **Value at Risk** `VaR^P_ε(v)`, eq. (6).
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, eq. (6), p. 10:
"For any `v ∈ ℝ^d` and measure `P`, the Value at Risk at level `ϵ` with respect to `v` is
`VaR^P_ϵ(v) ≡ inf { t : P(ũᵀv ≤ t) ≥ 1 − ϵ }`."

`VaR P ε v` is the infimum of the reals `t` with `P{u : ⟪u, v⟫ ≤ t} ≥ 1 − ε`.

**Formalization Note.** The random vector `ũ` is the identity on `ℝ^d = EuclideanSpace ℝ (Fin d)`
under the law `P`, so `P(ũᵀv ≤ t)` is the `P`-measure of the closed half-space
`{u : ⟪u, v⟫ ≤ t}`. The value is a real `sInf`. For a probability measure and `0 < ε < 1` the set
of such `t` is nonempty and bounded below, so `VaR P ε v` is the true infimum; Lean's junk value
`0` only occurs for `ε ≤ 0` or `ε ≥ 1`, where no statement of this mission relies on it
(Theorem 1(a) holds trivially for `ε ≥ 1`). -/
noncomputable def VaR {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d))) (ε : ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sInf {t : ℝ | 1 - ε ≤ (P {u | ⟪u, v⟫_ℝ ≤ t}).toReal}

end DDROCS


