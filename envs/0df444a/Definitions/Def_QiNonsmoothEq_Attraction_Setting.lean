-- Prove2me | Definitions.Def_QiNonsmoothEq_Attraction_Setting
-- name    : QiNonsmoothEq_Attraction_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:44.65422+00:00
-- url     : https://prove2.me/theorems/9c715a53-89bb-4d17-be2b-b1d158b21496
-- title:
--   §2 and §4, pp. 229, 232, 236 — directional differentiability, B-differentiability (2.1), BD-regularity, the norm function g, the Armijo test (4.1) and runs of Algorithm 4.1
-- statement:
--   This module fixes the objects of Qi's attraction theorem (§5) and of its application to the damped Newton method. Throughout, $E$ and $G$ are real normed spaces (in the theorems, $E=G=\mathbb R^n$ with the Euclidean norm), $F:E\to G$, and $F'(x;h)=\lim_{t\downarrow 0}\big(F(x+th)-F(x)\big)/t$ is the one-sided directional derivative (the published definition `NonsmoothNewton.Local.dirDeriv`).
--
--   1. **Directional differentiability.** $F$ is directionally differentiable at $x$ if the limit $F'(x;h)$ exists for every direction $h$.
--   2. **B-differentiability** (2.1)–(2.2). $F$ is B-differentiable at $x$ if it is directionally differentiable at $x$ and
--   $$\lim_{h\to 0}\frac{F(x+h)-F(x)-F'(x;h)}{\|h\|}=0,\qquad\text{i.e.}\qquad F(x+h)=F(x)+F'(x;h)+o(\|h\|).$$
--   3. **BD-regularity** (p. 232). $F$ is BD-regular at $x$ if it is directionally differentiable at $x$ and $F'(x;h)\neq 0$ for every $h\neq 0$.
--   4. **Norm function** (p. 227). For $F:E\to E$, $g(x)=\tfrac12\|F(x)\|^2$; on $\mathbb R^n$ this is $\tfrac12F(x)^{\mathsf T}F(x)$.
--   5. **Armijo test** (4.1). For $s,\beta,\sigma\in\mathbb R$, a point $y$, a direction $d$ and an integer $m\ge 0$, the test is
--   $$g(y)-g(y+\beta^m s\,d)\ \ge\ -\sigma\beta^m s\,g'(y;d).$$
--   6. **Run of Algorithm 4.1** (the damped Newton method, p. 236). Sequences $x^k,d^k\in E$ and $\alpha_k\in\mathbb R$ form a run if for every $k$: $d^k$ solves the generalized Newton equation (3.12) $F(x^k)+F'(x^k;d^k)=0$; $\alpha_k=\beta^{m_k}s$ where $m_k$ is the first nonnegative integer passing the Armijo test at $(x^k,d^k)$; and $x^{k+1}=x^k+\alpha_kd^k$.
--
--   These are the hypotheses of the attraction theorem (Theorem 5.1) and of its corollary for the damped Newton method (Corollary 5.2).
--
--   **Formalization Note** Equation (3.12) is stated as "$F'(x^k;d^k)$ exists and equals $-F(x^k)$", so that the junk value of an undefined limit is never used. The parameter ranges $s>0$, $\beta\in(0,1)$, $\sigma\in(0,\tfrac12)$ and the condition $F(x^k)\neq 0$ are hypotheses of the theorems, not part of the run. The norm function, the Armijo test and the run are restated in each mission of this series because drafts cannot import drafts; they will be merged later.
-- source:
--   Qi, Convergence analysis of some algorithms for solving nonsmooth equations, Math. Oper. Res. 18 (1993), pp. 227, 229, 232, 236, (2.1), (2.2), BD-regularity, (4.1), Algorithm 4.1

import Mathlib
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_QiNonsmoothEq_Local_Setting

namespace QiNonsmoothEq.Attraction

open Filter Topology NonsmoothNewton.Local

/-- BD-regularity at `x`, Qi 1993, p. 232: `F` is directionally differentiable at `x` and
`F'(x; h) ≠ 0` for every `h ≠ 0`. -/
def BDRegularAt {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (x : E) : Prop :=
  QiNonsmoothEq.Local.DirDiffAt F x ∧ ∀ h : E, h ≠ 0 → dirDeriv F x h ≠ 0

/-- The norm function `g(x) = ½ F(x)ᵀF(x) = ½ ‖F(x)‖²` of Qi 1993, §1, p. 227. -/
noncomputable def normFn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (x : E) : ℝ :=
  (1 / 2) * ‖F x‖ ^ 2

/-- The Armijo test (4.1) of Algorithm 4.1, Qi 1993, p. 236, for the trial exponent `m`:
`g(y) - g(y + β^m s d) ≥ -σ β^m s g'(y; d)`. -/
def armijoTest {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (s β σ : ℝ) (y d : E) (m : ℕ) : Prop :=
  normFn F y - normFn F (y + (β ^ m * s) • d) ≥ -σ * β ^ m * s * dirDeriv (normFn F) y d

/-- A run of Algorithm 4.1 (the damped Newton method), Qi 1993, p. 236: at every step `d k`
solves the generalized Newton equation (3.12) `F(x^k) + F'(x^k; d^k) = 0`, the step size is
`α_k = β^{m_k} s` with `m_k` the first nonnegative integer passing the Armijo test (4.1), and
`x^{k+1} = x^k + α_k d^k`. The parameter ranges `s > 0`, `β ∈ (0,1)`, `σ ∈ (0,1/2)` are
hypotheses of the theorems that use the run. -/
def IsDampedNewtonRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (s β σ : ℝ) (x d : ℕ → E) (α : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, HasDirDerivAt F (x k) (d k) (-F (x k)) ∧
    (∃ m : ℕ, armijoTest F s β σ (x k) (d k) m ∧
      (∀ j < m, ¬ armijoTest F s β σ (x k) (d k) j) ∧ α k = β ^ m * s) ∧
    x (k + 1) = x k + α k • d k

end QiNonsmoothEq.Attraction


