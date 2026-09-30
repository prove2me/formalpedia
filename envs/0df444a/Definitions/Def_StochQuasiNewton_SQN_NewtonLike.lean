-- Prove2me | Definitions.Def_StochQuasiNewton_SQN_NewtonLike
-- name    : StochQuasiNewton_SQN_NewtonLike
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:51:36.892193+00:00
-- url     : https://prove2.me/theorems/f87eb734-ab6a-42f1-ad5e-77872ce12b3a
-- title:
--   The Newton-like stochastic iteration (3.14) and the corrected rate constant Q_c(β)
-- statement:
--   Let $(\Omega,P)$ be a probability space with a filtration $(\mathcal F_k)_{k\ge0}$, where $\mathcal F_k$ is the information available before the sample $\xi^k$ is drawn. Let $F:\mathbb R^n\to\mathbb R$ be the objective, and let $\nabla f(w,\xi)$ be a jointly measurable stochastic gradient. The random iterates $w^k$, samples $\xi^k$ and matrices $H_k$ form a **Newton-like iteration** (3.14) with step lengths $\alpha^k$, constants $0<\mu_1\le\mu_2$ and $\gamma$, starting at $w^1$, if:
--
--   1. $w^k$ and $H_k$ are $\mathcal F_k$-measurable and $\xi^k$ is $\mathcal F_{k+1}$-measurable;
--   2. $w^1$ is the deterministic point $w^1$;
--   3. for $k\ge1$, $\;w^{k+1}=w^k-\alpha^kH_k\nabla f(w^k,\xi^k)$;
--   4. for $k\ge1$, $\;\mu_1I\prec H_k\prec\mu_2I$ (3.15);
--   5. for $k\ge1$, $\;E[\nabla f(w^k,\xi^k)\mid\mathcal F_k]=\nabla F(w^k)$ almost surely;
--   6. for $k\ge1$, $\;\|\nabla f(w^k,\xi^k)\|^2$ is integrable and $E[\|\nabla f(w^k,\xi^k)\|^2\mid\mathcal F_k]\le\gamma^2$ almost surely.
--
--   The file also defines the **corrected rate constant**
--   $$Q_c(\beta)=\max\Big\{\frac{\Lambda\mu_2^2\beta^2\gamma^2}{2(2\mu_1\lambda\beta-1)},\ \Lambda\mu_2^2\beta^2\gamma^2,\ F(w^1)-F(w^*)\Big\}.$$
--
--   **Formalization Note** Condition 6 is the reading of Assumption 1(3), Eq. (3.5), that the proof of Theorem 3.2 uses: the paper's "for all $w\in\mathbb R^n$" cannot hold together with unbiasedness and strong convexity on $\mathbb R^n$, since then $\|\nabla F(w)\|\le\gamma$ for all $w$ while $\|\nabla F(w)\|\ge\lambda\|w-w^*\|$. Condition 1 (the matrix $H_k$ is fixed before $\xi^k$ is drawn) is used, but not stated, by the paper at (3.18). The paper's constant (3.17) is $Q(\beta)=\max\{\Lambda\mu_2^2\beta^2\gamma^2/(2(2\mu_1\lambda\beta-1)),\,F(w^1)-F(w^*)\}$; the middle entry is added because Theorem 3.2 is false with $Q(\beta)$ (see that theorem). $Q_c=Q$ whenever $2\mu_1\lambda\beta\le3/2$. Matrices act on `EuclideanSpace ℝ (Fin n)` through `Matrix.toEuclideanLin`; the strict order $\prec$ is `Matrix.PosDef` of the difference.
-- source:
--   Byrd, Hansen, Nocedal, Singer, A Stochastic Quasi-Newton Method for Large-Scale Optimization, SIAM J. Optim. 26(2) (2016), p. 1016, Eq. (3.14) and the paragraph after it, Eq. (3.15); p. 1015, Assumption 1(3), Eq. (3.5); p. 1017, Eq. (3.17)

import Mathlib

open scoped RealInnerProductSpace
open MeasureTheory

namespace StochQuasiNewton.SQN

/-- The Newton-like stochastic iteration (3.14) together with its standing assumptions.
`(Ω, P)` is a probability space with filtration `ℱ` (`ℱ k` is the information available before
the sample `ξ^k` is drawn); `G w ξ` is the stochastic gradient `∇f(w, ξ)` of the objective `F`
at `w` for the sample `ξ`; `w k`, `ξ k`, `H k` are the random iterate `w^k`, sample `ξ^k` and
matrix `H_k`. The fields say:
* `G` is jointly measurable; `w^k` and `H_k` are `ℱ k`-measurable, `ξ^k` is `ℱ (k+1)`-measurable;
* `w^1 = w1` is deterministic;
* for `k ≥ 1`, `w^{k+1} = w^k − α^k H_k ∇f(w^k, ξ^k)` (3.14);
* for `k ≥ 1`, `μ₁ I ≺ H_k ≺ μ₂ I` (3.15), in the strict Loewner order;
* for `k ≥ 1`, the stochastic gradient is conditionally unbiased,
  `E[∇f(w^k, ξ^k) | ℱ k] = ∇F(w^k)` a.s.;
* for `k ≥ 1`, `‖∇f(w^k, ξ^k)‖²` is integrable and its conditional expectation given `ℱ k` is
  at most `γ²` a.s. (the iterate-wise reading of Assumption 1(3), (3.5)). -/
structure NewtonLikeIteration {n : ℕ} {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace Ξ] (P : Measure Ω) (ℱ : Filtration ℕ mΩ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → Ξ → EuclideanSpace ℝ (Fin n))
    (γ : ℝ) (α : ℕ → ℝ) (μ₁ μ₂ : ℝ) (w1 : EuclideanSpace ℝ (Fin n))
    (w : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ξ : ℕ → Ω → Ξ)
    (H : ℕ → Ω → Matrix (Fin n) (Fin n) ℝ) : Prop where
  measurable_G : Measurable (Function.uncurry G)
  adapted_w : ∀ k, Measurable[ℱ k] (w k)
  adapted_H : ∀ k (i j : Fin n), Measurable[ℱ k] (fun ω => H k ω i j)
  measurable_ξ : ∀ k, Measurable[ℱ (k + 1)] (ξ k)
  init : ∀ ω, w 1 ω = w1
  step : ∀ k, 1 ≤ k → ∀ ω,
    w (k + 1) ω = w k ω - α k • Matrix.toEuclideanLin (H k ω) (G (w k ω) (ξ k ω))
  eig_bounds : ∀ k, 1 ≤ k → ∀ ω,
    (H k ω - μ₁ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef ∧
      (μ₂ • (1 : Matrix (Fin n) (Fin n) ℝ) - H k ω).PosDef
  unbiased : ∀ k, 1 ≤ k →
    P[fun ω => G (w k ω) (ξ k ω) | ℱ k] =ᵐ[P] fun ω => gradient F (w k ω)
  sq_integrable : ∀ k, 1 ≤ k → Integrable (fun ω => ‖G (w k ω) (ξ k ω)‖ ^ 2) P
  second_moment : ∀ k, 1 ≤ k →
    P[fun ω => ‖G (w k ω) (ξ k ω)‖ ^ 2 | ℱ k] ≤ᵐ[P] fun _ => γ ^ 2

/-- The corrected rate constant
`Q_c(β) = max { Λ μ₂² β² γ² / (2(2 μ₁ λ β − 1)), Λ μ₂² β² γ², F(w¹) − F(w*) }`, where `gap`
stands for `F(w¹) − F(w*)`. The paper's constant (3.17) is the maximum of the first and last
entries only. -/
noncomputable def rateConstant (Lam lam μ₁ μ₂ β γ gap : ℝ) : ℝ :=
  max (max (Lam * μ₂ ^ 2 * β ^ 2 * γ ^ 2 / (2 * (2 * μ₁ * lam * β - 1)))
    (Lam * μ₂ ^ 2 * β ^ 2 * γ ^ 2)) gap

end StochQuasiNewton.SQN


