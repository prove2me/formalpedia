-- Prove2me | Definitions.Def_NonconvexSaddle_PGDVar_Algorithm4
-- name    : NonconvexSaddle_PGDVar_Algorithm4
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:11:46.507297+00:00
-- url     : https://prove2.me/theorems/b8172b29-7e86-4e6d-a110-7666caff0915
-- title:
--   Algorithm 4 — Perturbed Gradient Descent (Variant)
-- statement:
--   **Algorithm 4 (Perturbed Gradient Descent, Variant).** The input is a starting point $x_0\in\mathbb R^d$, a step size $\eta$, a perturbation radius $r$, a time interval $\mathscr T\in\mathbb N$, a tolerance $\varepsilon$, and perturbation vectors $\xi_0,\xi_1,\dots\in\mathbb R^d$. Set $t_{\text{perturb}}=0$. For $t=0,1,\dots$:
--
--   1. if $\|\nabla f(x_t)\|\le\varepsilon$ and $t-t_{\text{perturb}}>\mathscr T$, replace $x_t$ by $x_t-\eta\xi_t$ and set $t_{\text{perturb}}\leftarrow t$;
--   2. set $x_{t+1}=x_t-\eta\nabla f(x_t)$, at the (possibly perturbed) point.
--
--   The **$t$-th iterate** is the point $x_t$ tested at the start of iteration $t$, before any perturbation. In the paper the $\xi_t$ are drawn independently from $\mathrm{Uniform}(B_0(r))$; here the run is a deterministic function of the sequence $(\xi_t)$, and the law is imposed in the statements that use it.
--
--   Algorithm 4 perturbs only when the gradient is small and at least $\mathscr T+1$ iterations have passed since the last perturbation (or since the start), so that each perturbation is followed by $\mathscr T$ iterations of plain gradient descent.
--
--   **Formalization Note** The state is the pair $(x_t,t_{\text{perturb}})$, with $t_{\text{perturb}}\le t$ always, so the natural-number difference $t-t_{\text{perturb}}$ is exact. Since $t_{\text{perturb}}=0$ initially, no perturbation happens before $t=\mathscr T+1$, as on the page. A finite family $\xi_0,\dots,\xi_{T-1}$ is extended by $0$ to all $t$; iterates $x_t$ with $t<T$ use only $\xi_s$ with $s<t$.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, p. 12, Algorithm 4

import Mathlib
import Definitions.Def_NonconvexSaddle_PGDVar_Setting

open scoped RealInnerProductSpace

namespace NonconvexSaddle.PGDVar

open Classical in
/-- Iteration `t` of Algorithm 4, Perturbed Gradient Descent (Variant) (arXiv:1902.04811v2, p. 12),
acting on the state `(x_t, t_perturb)` with step size `η`, tolerance `ε`, time interval `𝒯` and
perturbation vectors `ξ`:
if `‖∇f(x_t)‖ ≤ ε` and `t − t_perturb > 𝒯`, then `x_t ← x_t − ηξ_t` and `t_perturb ← t`;
then `x_{t+1} = x_t − η∇f(x_t)`, evaluated at the (possibly perturbed) point. -/
noncomputable def pgdvStep {d : ℕ} (f : NonconvexSaddle.PSGD.E d → ℝ) (η ε : ℝ) (𝒯 : ℕ) (ξ : ℕ → NonconvexSaddle.PSGD.E d) (t : ℕ)
    (s : NonconvexSaddle.PSGD.E d × ℕ) : NonconvexSaddle.PSGD.E d × ℕ :=
  if ‖gradient f s.1‖ ≤ ε ∧ 𝒯 < t - s.2 then
    (gdStep f η (s.1 - η • ξ t), t)
  else
    (gdStep f η s.1, s.2)

/-- The state of Algorithm 4 at the start of iteration `t`: `(x_t, t_perturb)`, with `x_0` the input
and `t_perturb = 0` initially. -/
noncomputable def pgdvState {d : ℕ} (f : NonconvexSaddle.PSGD.E d → ℝ) (η ε : ℝ) (𝒯 : ℕ) (x₀ : NonconvexSaddle.PSGD.E d) (ξ : ℕ → NonconvexSaddle.PSGD.E d) :
    ℕ → NonconvexSaddle.PSGD.E d × ℕ
  | 0 => (x₀, 0)
  | t + 1 => pgdvStep f η ε 𝒯 ξ t (pgdvState f η ε 𝒯 x₀ ξ t)

/-- The `t`-th iterate `x_t` of Algorithm 4: the point tested at the start of iteration `t`, before a
possible perturbation. -/
noncomputable def pgdvIter {d : ℕ} (f : NonconvexSaddle.PSGD.E d → ℝ) (η ε : ℝ) (𝒯 : ℕ) (x₀ : NonconvexSaddle.PSGD.E d) (ξ : ℕ → NonconvexSaddle.PSGD.E d)
    (t : ℕ) : NonconvexSaddle.PSGD.E d :=
  (pgdvState f η ε 𝒯 x₀ ξ t).1

/-- A finite family of perturbations `ξ_0, …, ξ_{T−1}` extended by `0` to all of `ℕ` (iterations
`t ≥ T` are never inspected). -/
noncomputable def extendPert {d T : ℕ} (ξ : Fin T → NonconvexSaddle.PSGD.E d) (t : ℕ) : NonconvexSaddle.PSGD.E d :=
  if h : t < T then ξ ⟨t, h⟩ else 0

end NonconvexSaddle.PGDVar


