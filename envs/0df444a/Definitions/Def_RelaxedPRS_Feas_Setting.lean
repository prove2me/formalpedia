-- Prove2me | Definitions.Def_RelaxedPRS_Feas_Setting
-- name    : RelaxedPRS_Feas_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:21:57.238526+00:00
-- url     : https://prove2.me/theorems/d3d1cbcf-00b7-4afe-8769-221e04ae2d7c
-- title:
--   §5 and Appendix C, pp. 4, 16–18, 35 — d²_C, refl, T^{γ_f,γ_g}_PRS, (T)_λ, iteration (5.1), bounded linear regularity (Definition 5.1), the rate C(γ_f, γ_g, λ, μ)
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $C_f, C_g\subseteq\mathcal H$. This file fixes the objects of the feasibility section of Davis–Yin.
--
--   1. **Squared distance.** For $C\subseteq\mathcal H$, $d_C(x)=\inf_{y\in C}\|x-y\|$ and $d_C^2(x)=d_C(x)^2$, viewed as a function $\mathcal H\to(-\infty,\infty]$ that happens to be finite everywhere. The feasibility problem is modelled with $f=d^2_{C_f}$ and $g=d^2_{C_g}$.
--   2. **Reflection and PRS operator.** For a map $P$ (in use: a proximal map $P=\mathbf{prox}_{\gamma h}$), $\mathbf{refl}(z)=2P(z)-z$. For prox maps $P_f=\mathbf{prox}_{\gamma_f f}$ and $P_g=\mathbf{prox}_{\gamma_g g}$,
--   $$
--   T^{\gamma_f,\gamma_g}_{\mathrm{PRS}}=\mathbf{refl}_{\gamma_f f}\circ\mathbf{refl}_{\gamma_g g},\qquad (T)_\lambda=(1-\lambda)I_{\mathcal H}+\lambda T .
--   $$
--   The auxiliary points of one step at $z$ are $x_g=\mathbf{prox}_{\gamma_g g}(z)$ and $x_f=\mathbf{prox}_{\gamma_f f}(\mathbf{refl}_{\gamma_g g}(z))$.
--   3. **Iteration (5.1).** Given step-$k$ prox maps $P_{f,k}=\mathbf{prox}_{\gamma_{f,k}d^2_{C_f}}$, $P_{g,k}=\mathbf{prox}_{\gamma_{g,k}d^2_{C_g}}$ and relaxation parameters $\lambda_k$, a sequence $(z^k)$ is a run of (5.1) if for all $k\ge0$
--   $$
--   x_g^k=P_{g,k}(z^k),\quad x_f^k=P_{f,k}(2x_g^k-z^k),\quad z^{k+1}=z^k+2\lambda_k(x_f^k-x_g^k).
--   $$
--   4. **Bounded linear regularity** (Definition 5.1 with two sets). $\{C_f,C_g\}$ is boundedly linearly regular if for every $\rho>0$ there is $\mu_\rho>0$ with
--   $$
--   d_{C_f\cap C_g}(x)\le\mu_\rho\max\{d_{C_f}(x),d_{C_g}(x)\}\qquad\text{for all }x\in B(0,\rho),
--   $$
--   where $B(0,\rho)$ is the open ball. Definition 5.1 is stated for closed convex sets with nonempty intersection; those conditions are hypotheses of every theorem that uses the notion.
--   5. **The rate of Theorem 5.1.**
--   $$
--   C(\gamma_f,\gamma_g,\lambda,\mu)=\left(1-\frac{4\lambda\min\{\gamma_g/(2\gamma_g+1)^2,\ \gamma_f/(2\gamma_f+1)^2\}}{\mu^2\max\{16\gamma_g^2/(2\gamma_g+1)^2,\ 1\}}\right)^{1/2}.
--   $$
--
--   These are the objects in which Theorem 5.1 (linear convergence of relaxed PRS for the two-set feasibility problem) and its supporting lemmas are stated.
--
--   **Formalization Note** The prox maps are arbitrary maps $P$ satisfying the published predicate `IsProx γ h P` ($P(x)$ minimises $h(y)+\|y-x\|^2/(2\gamma)$); for $h=d_C^2$ with $C$ closed, convex and nonempty and $\gamma>0$ the minimiser is unique, so $P$ is the prox map. Metric projections are maps satisfying the published `IsMetricProjection`. The square root is `Real.sqrt`, which returns $0$ on a negative radicand; for positive parameters the radicand is at most $1$, and it can be negative only when $\mu<1$, in which case every point of the ball already lies in $C_f\cap C_g$.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, p. 4 (refl, (T)_λ), pp. 16–17 (§5, Definition 5.1, f = d²_{C_f}, g = d²_{C_g}, (5.1)), p. 18 (Theorem 5.1, C(γ_f,k, γ_g,k, λ_k, μ_ρ)), p. 35 (Appendix C, T^{γ_f,γ_g}_PRS)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_RelaxedPRS_BestIter_Setting
import Definitions.Def_RelaxedPRS_StrongCvx_Setting

namespace RelaxedPRS.Feas

/-- The squared distance function `d²_C(x) = (inf_{y ∈ C} ‖x − y‖)²` (§5, p. 17), viewed as a
`(−∞, ∞]`-valued function so that `ThreeOpSplitting.ConvexRates.IsProx` applies to it. It is
finite everywhere. -/
noncomputable def dsq {H : Type*} [NormedAddCommGroup H] (C : Set H) : H → EReal :=
  fun x => ((Metric.infDist x C ^ 2 : ℝ) : EReal)

/-- The averaged operator `(T)_λ = (1 − λ) I_H + λ T` (p. 4). -/
def relaxOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (T : H → H) (t : ℝ)
    (z : H) : H :=
  (1 - t) • z + t • T z

/-- A run of iteration (5.1), p. 17, with the step-`k` prox maps `Pf k = prox_{γ_{f,k} d²_{C_f}}`
and `Pg k = prox_{γ_{g,k} d²_{C_g}}`:
`x_g^k = Pg k (z^k)`, `x_f^k = Pf k (2 x_g^k − z^k)`, `z^{k+1} = z^k + 2 λ_k (x_f^k − x_g^k)`. -/
def IsFeasRun {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Pf Pg : ℕ → H → H) (lam : ℕ → ℝ) (z : ℕ → H) : Prop :=
  ∀ k, z (k + 1) = z k + (2 * lam k) • (Pf k ((2 : ℝ) • Pg k (z k) - z k) - Pg k (z k))

/-- Bounded linear regularity of the pair `{C_f, C_g}` (Definition 5.1, p. 17, with `m = 2`):
for every `ρ > 0` there is `μ_ρ > 0` with `d_{C_f ∩ C_g}(x) ≤ μ_ρ max{d_{C_f}(x), d_{C_g}(x)}` for
all `x` in the open ball `B(0, ρ)`. The definition's preamble (`C_f`, `C_g` closed, convex, with
nonempty intersection) is carried by the hypotheses of every theorem that uses it. -/
def IsBddLinReg {H : Type*} [NormedAddCommGroup H] (Cf Cg : Set H) : Prop :=
  ∀ ρ > 0, ∃ μ > 0, ∀ x ∈ Metric.ball (0 : H) ρ,
    Metric.infDist x (Cf ∩ Cg) ≤ μ * max (Metric.infDist x Cf) (Metric.infDist x Cg)

/-- The contraction factor of Theorem 5.1, p. 18:
`C(γ_f, γ_g, λ, μ) = (1 − 4λ min{γ_g/(2γ_g+1)², γ_f/(2γ_f+1)²} / (μ² max{16γ_g²/(2γ_g+1)², 1}))^{1/2}`. -/
noncomputable def Cfeas (γf γg t μ : ℝ) : ℝ :=
  Real.sqrt (1 - 4 * t * min (γg / (2 * γg + 1) ^ 2) (γf / (2 * γf + 1) ^ 2) /
    (μ ^ 2 * max (16 * γg ^ 2 / (2 * γg + 1) ^ 2) 1))

end RelaxedPRS.Feas


