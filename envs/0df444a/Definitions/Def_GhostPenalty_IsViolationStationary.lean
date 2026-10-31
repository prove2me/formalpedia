-- Prove2me | Definitions.Def_GhostPenalty_IsViolationStationary
-- name    : GhostPenalty_IsViolationStationary
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:42.162298+00:00
-- url     : https://prove2.me/theorems/fe4a720d-542c-4615-96fd-e94a8ea84420
-- title:
--   Stationary point of the violation problem (4), condition (5)
-- statement:
--   The violation problem is
--   $$\operatorname*{minimize}_x\ F(x)=\max_i\{g_i(x)_+\},\qquad x\in K. \tag{4}$$
--   A point $\hat x\in K$ is **stationary** for (4) if
--   $$0\in\partial F(\hat x)+N_K(\hat x). \tag{5}$$
--   $F=\max\{0,g_1,\dots,g_m\}$ is a pointwise maximum of $C^1$ functions, so its subdifferential at $\hat x$ is the convex hull of the gradients of the active pieces: $\nabla g_i(\hat x)$ for every $i$ with $g_i(\hat x)=F(\hat x)$, together with $0$ when $F(\hat x)=0$. Every feasible point is stationary for (4).
--
--   **Formalization Note** Mathlib has no Clarke subdifferential, so $\partial F(\hat x)$ is written out by the max rule (Clarke 1983, Prop. 2.3.12; the maximum is regular, so Clarke and regular subdifferentials agree). $N_K$ is the published `normalCone` at $\hat x\in K$.
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, §2, (4) and (5), p.5

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone
import Definitions.Def_GhostPenalty_posMax

namespace GhostPenalty

open FirstOrderOpt.ConvexTheory

/-- **Stationary point of the violation problem (4)**, condition (5).
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, §2, (4) and (5), p.5: "minimize_x max_i{g_i(x)+}, x ∈ K (4)" and "the stationarity
condition for problem (4), `0 ∈ ∂max_i{g_i(x̂)+} + N_K(x̂)` (5)".

`F(x) = max_i{g_i(x)₊} = max{0, g_1(x), …, g_m(x)}` is a pointwise maximum of the `C¹` functions
`0, g_1, …, g_m`. Its (Clarke) subdifferential at `x̂` is the convex hull of the gradients of the
pieces active at `x̂`: `∇g_i(x̂)` for every `i` with `g_i(x̂) = F(x̂)`, and `0` (the gradient of
the constant piece) when `F(x̂) = 0`. `x̂ ∈ K` is stationary for (4) if `-v ∈ N_K(x̂)` for some
`v` in that subdifferential.

**Formalization Note.** Mathlib has no Clarke subdifferential; `∂F(x̂)` is written out by the
max rule for finitely many `C¹` functions (Clarke, *Optimization and Nonsmooth Analysis*, 1983,
Prop. 2.3.12; such a maximum is regular, so the Clarke and the regular subdifferential agree).
In particular every feasible point is stationary (`0 ∈ ∂F(x̂)` when `F(x̂) = 0`), as the paper
notes on p.11. `N_K` is the published `normalCone`, used at `x̂ ∈ K`. -/
def IsViolationStationary {n m : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ K ∧ ∃ v ∈ convexHull ℝ
      ({v | ∃ i, g i x = posMax g x ∧ v = gradient (g i) x} ∪ {v | v = 0 ∧ posMax g x = 0}),
    -v ∈ normalCone K x

end GhostPenalty


