-- Prove2me | Definitions.Def_You2015_Shared_Solution
-- name    : You2015_Shared_Solution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T01:32:07.081687+00:00
-- url     : https://prove2.me/theorems/3a4f3d78-fa4c-4c43-9a62-50ab39516ed1
-- title:
--   The sampling time δ_t = [t/τ]τ and solutions of the controlled hybrid SDE (2.1) with feedback u(x(δ_t), r(t), t)
-- statement:
--   Let $\tau>0$. The **sampling time** is
--   $$\delta_t=\Big[\frac t\tau\Big]\tau\qquad(t\ge0),$$
--   where $[t/\tau]$ is the integer part of $t/\tau$; the state is observed only at the times $0,\tau,2\tau,\dots$ and $\delta_t$ is the last observation time not after $t$.
--
--   Given a stochastic basis (filtration under the usual conditions, $m$-dimensional Brownian motion $w$, Markov chain $r$ on $S$, see the definition file of the basis), coefficients $f,u:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^n$ and $g:\mathbb R^n\times S\times\mathbb R_+\to\mathbb R^{n\times m}$, and $x_0\in\mathbb R^n$, a process $x$ is a **solution** of the controlled hybrid SDE
--   $$dx(t)=\big(f(x(t),r(t),t)+u(x(\delta_t),r(t),t)\big)dt+g(x(t),r(t),t)\,dw(t),\qquad x(0)=x_0,\tag{2.1}$$
--   on $t\ge0$ when
--
--   1. $x$ is progressively measurable with respect to $\{\mathcal F_t\}$;
--   2. almost every path $t\mapsto x(t)$ is continuous;
--   3. $\mathbb E|x(t)|^2<\infty$ for every $t\ge0$;
--   4. there are Itô integral processes $J_k(t)=\int_0^t g_k(x(s),r(s),s)\,dw_k(s)$, $k=1,\dots,m$, where $g_k$ is the $k$-th column of $g$, and for every $t\ge0$, almost surely, the drift $s\mapsto f(x(s),r(s),s)+u(x(\delta_s),r(s),s)$ is Lebesgue integrable on $[0,t]$ and
--   $$x(t)=x_0+\int_0^t\big(f(x(s),r(s),s)+u(x(\delta_s),r(s),s)\big)ds+\sum_{k=1}^m J_k(t).$$
--
--   The feedback control $u(x(\delta_t),r(t),t)$ uses the state only at the discrete observation times; (2.1) is therefore a stochastic differential delay equation with the bounded, non-differentiable delay $t-\delta_t$.
--
--   Used by both missions of this paper: 01-asymptotic-stability (Theorem 3.4 series; p. 907, Eqs. (2.1)–(2.2) and p. 908) and 02-exponential-stability (Theorem 4.2 series; p. 907, Eqs. (2.1)–(2.2) and p. 908).
--
--   **Formalization Note** The state space is `EuclideanSpace ℝ (Fin n)`, whose norm is the Euclidean norm $|x|$ of the paper. The diffusion $g$ is given by its $m$ columns (column $k$ multiplies $dw_k$). The paper speaks of "the unique solution" (p. 908, citing Mao–Yuan [23] for existence and uniqueness); the theorems of the mission are stated for **every** process satisfying this definition, and existence is not asserted. Path continuity is required almost surely because Theorem 3.4 and its proof are statements about paths. $\mathbb E|x(t)|^2<\infty$ is the paper's "such that $\mathbb E|x(t)|^2<\infty$ for all $t\ge0$" (p. 908).
-- source:
--   You, Liu, Lu, Mao, Qiu, Stabilization of Hybrid Systems by Feedback Control Based on Discrete-Time State Observations, SIAM J. Control Optim. 53(2), 2015, https://doi.org/10.1137/140985779, p. 907, Eqs. (2.1)–(2.2); p. 908 (the solution x(t) with E|x(t)|² < ∞)

import Mathlib
import Definitions.Def_You2015_Shared_Basis
import Definitions.Def_You2015_Shared_Ito

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace You2015.Shared

/-- The last observation time before `t`: `δ_t = [t/τ] τ`, where `[t/τ]` is the integer part
of `t/τ ≥ 0`. -/
noncomputable def delta (τ t : ℝ≥0) : ℝ≥0 := (⌊t / τ⌋₊ : ℝ≥0) * τ

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `x` is a solution of the controlled hybrid SDE (2.1),
`dx(t) = (f(x(t), r(t), t) + u(x(δ_t), r(t), t)) dt + g(x(t), r(t), t) dw(t)`, `x(0) = x₀`,
on `t ≥ 0`, driven by the stochastic basis `S` (the diffusion `g` is given by its `m` columns;
column `k` multiplies `dw_k`):

* `x` is progressively measurable for `{𝓕_t}`;
* almost every path `t ↦ x(t, ω)` is continuous;
* `E|x(t)|² < ∞` for every `t ≥ 0`;
* there are Itô integral processes `J_k(t) = ∫₀ᵗ g_k(x(s), r(s), s) dw_k(s)`, `k = 1, …, m`, and
  for every `t ≥ 0`, almost surely, the drift `s ↦ f(x(s), r(s), s) + u(x(δ_s), r(s), s)` is
  Lebesgue integrable on `[0, t]` and
  `x(t) = x₀ + ∫₀ᵗ (f(x(s), r(s), s) + u(x(δ_s), r(s), s)) ds + ∑_k J_k(t)`. -/
def SolvesSampledHybridSDE {P : Measure Ω} {n m N : ℕ} {Γ : Matrix (Fin N) (Fin N) ℝ}
    {r₀ : Fin N} (S : HybridSetup P m N Γ r₀)
    (f u : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → Fin N → ℝ≥0 → Fin m → EuclideanSpace ℝ (Fin n))
    (τ : ℝ≥0) (x₀ : EuclideanSpace ℝ (Fin n)) (x : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n)) :
    Prop :=
  IsStronglyProgressive S.𝓕 x ∧
    (∀ᵐ ω ∂P, Continuous (fun t => x t ω)) ∧
    (∀ t : ℝ≥0, ∫⁻ ω, ‖x t ω‖ₑ ^ 2 ∂P < ⊤) ∧
    ∃ J : Fin m → ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n),
      (∀ k, IsItoIntegral P S.𝓕 (fun t ω => S.w t ω k)
          (fun s ω => g (x s ω) (S.r s ω) s k) (J k)) ∧
      ∀ t : ℝ≥0, ∀ᵐ ω ∂P,
        IntegrableOn (fun s : ℝ => f (x s.toNNReal ω) (S.r s.toNNReal ω) s.toNNReal
            + u (x (delta τ s.toNNReal) ω) (S.r s.toNNReal ω) s.toNNReal)
          (Set.Icc 0 (t : ℝ)) ∧
        x t ω = x₀ + (∫ s in Set.Icc (0 : ℝ) t,
            (f (x s.toNNReal ω) (S.r s.toNNReal ω) s.toNNReal
              + u (x (delta τ s.toNNReal) ω) (S.r s.toNNReal ω) s.toNNReal))
          + ∑ k, J k t ω

end You2015.Shared


