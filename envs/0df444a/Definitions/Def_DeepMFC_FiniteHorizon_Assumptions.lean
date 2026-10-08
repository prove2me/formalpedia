-- Prove2me | Definitions.Def_DeepMFC_FiniteHorizon_Assumptions
-- name    : DeepMFC_FiniteHorizon_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:55.13455+00:00
-- url     : https://prove2.me/theorems/3fb23395-2573-4e3d-ac6f-00959024d609
-- title:
--   §2.2 and Appendix A, pp. 4067–4068, 4087–4090 — L-derivative, assumptions (A1)–(A4), (B1)–(B3), (C1)–(C3), the MKV FBSDE (2.7) and the decoupling field
-- statement:
--   This module states the standing assumptions of Carmona and Laurière's finite-horizon analysis.
--
--   **L-derivative.** A function $\partial_\mu F:\mathcal P_2(\mathbb R^d)\times\mathbb R^d\to\mathbb R^d$ is an *L-derivative* (Lions derivative) of $F:\mathcal P_2(\mathbb R^d)\to\mathbb R$ when, on the atomless probability space $([0,1],\mathrm{Leb})$, the lift $\vartheta\mapsto F(\mathcal L(\vartheta))$ is Fréchet differentiable on $L^2$ at every $\vartheta_0$, with derivative $\eta\mapsto\mathbb E[\partial_\mu F(\mathcal L(\vartheta_0))(\vartheta_0)\cdot\eta]$.
--
--   **Assumptions on the coefficients** (witness functions for every derivative are part of the data).
--   1. **(A1)** For $t\in[0,T]$ and $\mu\in\mathcal P_2$: $b(t,x,\mu,\alpha)=b_0(t)+b_1(t)x+\bar b_1(t)\bar\mu+b_2(t)\alpha$ and $\sigma(t,x,\mu)=\sigma_0(t)+\sigma_1(t)x+\bar\sigma_1(t)\bar\mu$, with bounded Lipschitz deterministic coefficients.
--   2. **(A2)** $f$ is differentiable in $(x,\alpha)$, $g$ in $x$; $f$ and $g$ have L-derivatives in $\mu$; $t\mapsto f(t,0,\delta_0,0)$ is bounded; and for some $L$, whenever $|x|,M_2(\mu),|\alpha|\le R$, the quantities $|\partial_xf|$, $|\partial_xg|$, $|\partial_\alpha f|$ and the $L^2(\mu)$-norms of $x'\mapsto\partial_\mu f(t,x,\mu,\alpha)(x')$, $x'\mapsto\partial_\mu g(x,\mu)(x')$ are at most $L(1+R)$.
--   3. **(A3)** $\partial_xf,\partial_\alpha f$ are $L$-Lipschitz in $(x,\alpha,\mu)$ and $\partial_xg$ in $(x,\mu)$ ($W_2$ in $\mu$), and for random variables $X,X'$ with laws $\mu,\mu'$,
--   $$\mathbb E\big[|\partial_\mu f(t,x',\mu',\alpha')(X')-\partial_\mu f(t,x,\mu,\alpha)(X)|^2\big]\le L\big(|(x',\alpha')-(x,\alpha)|^2+\mathbb E[|X'-X|^2]\big),$$
--   and the same for $\partial_\mu g$ without $\alpha$.
--   4. **(A4)** For some $\lambda>0$,
--   $$f(t,x',\mu',\alpha')-f(t,x,\mu,\alpha)-\partial_{(x,\alpha)}f(t,x,\mu,\alpha)\cdot(x'-x,\alpha'-\alpha)-\mathbb E[\partial_\mu f(t,x,\mu,\alpha)(X)\cdot(X'-X)]\ge\lambda|\alpha'-\alpha|^2,$$
--   and $g$ is L-convex in $(x,\mu)$.
--   5. **(B1)** $(t,x)\mapsto\partial_\alpha f(t,x,\mu,\alpha)$ is Lipschitz, uniformly in $\mu,\alpha$. **(B3)** $\mu_0\in\mathcal P_4(\mathbb R^d)$.
--   6. **(C1)** $|\partial_tf|$ has at most quadratic growth in $\Theta=(t,x,\mu,\alpha)$; $|\partial_\alpha f|$, $|\partial_xf|$, $|\partial_\mu f(\Theta)(x')|$ have at most linear growth; $\partial^2_{xx}f$, $\partial^2_{x\alpha}f$, $\partial^2_{\alpha\alpha}f$, $\partial_x\partial_\mu f$, $\partial_\alpha\partial_\mu f$, $\partial_v\partial_\mu f$ and $\partial^2_\mu f(\Theta)(x',x')$ are bounded.
--
--   **Pontryagin objects.** $\hat\alpha(t,x,\mu,y)$ minimizes $\alpha\mapsto\tilde H(t,x,\mu,y,\alpha)$ over $\mathbb R^k$ (2.6). The forward–backward system
--   $$dX_t=b(t,X_t,\mathcal L(X_t),\hat\alpha_t)\,dt+\sigma(t,X_t,\mathcal L(X_t))\,dW_t,$$
--   $$dY_t=-\partial_xH(t,X_t,\mathcal L(X_t),Y_t,Z_t,\hat\alpha_t)\,dt-\tilde{\mathbb E}\big[\partial_\mu H(t,\tilde X_t,\mathcal L(X_t),\tilde Y_t,\tilde Z_t,\tilde{\hat\alpha}_t)(X_t)\big]\,dt+Z_t\,dW_t,\qquad(2.7)$$
--   with $\hat\alpha_t=\hat\alpha(t,X_t,\mathcal L(X_t),Y_t)$, $X_0\sim\mu_0$ and $Y_T=\partial_xg(X_T,\mathcal L(X_T))+\tilde{\mathbb E}[\partial_\mu g(\tilde X_T,\mathcal L(X_T))(X_T)]$, has a solution on some Problem-1 space; $\mu_t=\mathcal L(X_t)$ is its flow of marginals and the **decoupling field** $V$ satisfies $Y_t=V(t,X_t)$ a.s. (2.8)–(2.9). Moreover **(B2)** $V$ is Lipschitz in $(t,x)$; **(C2)** $V$ is twice differentiable in $x$ with $\partial^2_{xx}V$ Lipschitz in $(t,x)$; **(C3)** $\hat\alpha$ is twice differentiable in $(x,y)$ with second derivatives Lipschitz in $(t,x,\mu,y)$. The optimal feedback is $\hat v(t,x)=\hat\alpha(t,x,\mu_t,V(t,x))$ (3.3).
--
--   These hypotheses are those under which the paper proves its approximation theorem; (A1)–(A4), (B1) are those of Carmona–Delarue's Pontryagin analysis of McKean–Vlasov control, and (B2), (B3), (C1)–(C3) are the extra regularity used for the propagation-of-chaos and time-discretization steps.
--
--   **Formalization Note.** All conditions are required for $t\in[0,T]$ and $\mu\in\mathcal P_2$. The expectations over pairs $(X,X')$ with laws $(\mu,\mu')$ in (A3)–(A4) are integrals over couplings of $\mu$ and $\mu'$; every such law is a coupling and every coupling is such a law. Under (A1), $b$ and $\sigma$ depend on $\mu$ only through $\bar\mu$, so $\partial_\mu b=\bar b_1$, $\partial_\mu\sigma=\bar\sigma_1$, and the backward drift is written with $\partial_xH=b_1^\top y+\sigma_1^\top\cdot z+\partial_xf$ and $\partial_\mu H=\bar b_1^\top y'+\bar\sigma_1^\top\cdot z'+\partial_\mu f$; the copy expectation $\tilde{\mathbb E}$ is the integral over a second copy of the probability space. The backward equation is the published `SolvesBSDE` ($-dY=F\,dt-\sum_jZ_j\,dW^j$), with $Z$ given by its columns. Readings disclosed: (i) "$g$ is L-convex in $(x,\mu)$" is the inequality of (A4) for $g$ without $\alpha$-terms and with right-hand side $0$; (ii) the continuity clauses of (A2) and its "in particular" display follow from (A3) and (A2) and are not repeated; (iii) unique solvability of (2.7) is not assumed, only existence (uniqueness follows from (A1)–(A4) by Carmona–Delarue, Theorem 6.19, cited on p. 4089), and the master field $\mathcal U$ enters only through $V(t,x)=\mathcal U(t,x,\mu_t)$; (iv) uniqueness of the minimizer and Lipschitz continuity of $\hat\alpha$ are not assumed (they follow from (A4) and are Lemma 18); (v) the regularity of $\hat v$ asked for on p. 4068 is not assumed separately, since Appendix A says (C2)–(C3) ensure it; (vi) in (C1) the growth is in $|t|+|x|+M_2(\mu)+|\alpha|$, $\partial_x\partial_\mu f(\Theta)(x')$ is the derivative in the $x$ of $\Theta$ evaluated at $x'$, $\partial^2_\mu f(\Theta)(x',x')$ is the L-derivative of $\mu\mapsto\partial_\mu f(\Theta)(x')_j$ at $x'$, entrywise, and the duplicated $\partial_xf$ is listed once; (vii) matrix-valued coefficients are bounded and Lipschitz entrywise, and (C3)'s three blocks $\partial^2_{xx}\hat\alpha,\partial^2_{yy}\hat\alpha,\partial^2_{xy}\hat\alpha$ are Lipschitz exactly when the full second derivative in $(x,y)$ is.
-- source:
--   Carmona, Laurière, Convergence analysis of machine learning algorithms for the numerical solution of mean field control and games: II—the finite horizon case, Ann. Appl. Probab. 32(6) (2022), https://doi.org/10.1214/21-AAP1715, pp. 4067–4068, §2.2, (2.6)–(2.10), (3.3); pp. 4087–4090, Appendix A, (A1)–(A4), (B1)–(B3), (C1)–(C3)

import Mathlib
import Definitions.Def_DeepMFC_FiniteHorizon_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DeepMFC.FiniteHorizon

/-! # Standing assumptions (§2.2, pp. 4067–4068; Appendix A, pp. 4087–4090)

Carmona, Laurière, Ann. Appl. Probab. 32(6) (2022). -/

/-- The linear functional `y ↦ v · y` on `ℝⁿ` represented by the vector `v` (a gradient). -/
noncomputable def dotL {n : ℕ} (v : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, v i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i

/-- `DF` is an L-derivative (Lions derivative) of `F : 𝒫₂(ℝᵈ) → ℝ`: for every square-integrable
`ϑ₀` on the atomless lift space `([0,1], Lebesgue)`, the lift `ϑ ↦ F(ℒ(ϑ))` is Fréchet
differentiable at `ϑ₀` in `L²` with derivative `η ↦ 𝔼[DF(ℒ(ϑ₀))(ϑ₀) · η]`: for every `ε > 0` there
is `δ > 0` with `|F(ℒ(ϑ)) − F(ℒ(ϑ₀)) − 𝔼[DF(ℒ(ϑ₀))(ϑ₀) · (ϑ − ϑ₀)]| ≤ ε ‖ϑ − ϑ₀‖_{L²}` whenever
`‖ϑ − ϑ₀‖_{L²} < δ`. -/
def IsLDeriv {d : ℕ} (F : Measure (E d) → ℝ) (DF : Measure (E d) → E d → E d) : Prop :=
  ∀ ϑ₀ : unitInterval → E d, MemLp ϑ₀ 2 volume → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ ϑ : unitInterval → E d, MemLp ϑ 2 volume → (eLpNorm (ϑ - ϑ₀) 2 volume).toReal < δ →
      |F (volume.map ϑ) - F (volume.map ϑ₀)
          - ∫ ω, dot (DF (volume.map ϑ₀) (ϑ₀ ω)) (ϑ ω - ϑ₀ ω)|
        ≤ ε * (eLpNorm (ϑ - ϑ₀) 2 volume).toReal

/-- `π` is a coupling of `μ` and `μ'`: a measure on `ℝᵈ × ℝᵈ` with marginals `μ` and `μ'` (the law
of a pair `(X, X')` with `ℒ(X) = μ`, `ℒ(X') = μ'`). -/
def IsCoupling {d : ℕ} (μ μ' : Measure (E d)) (π : Measure (E d × E d)) : Prop :=
  π.map Prod.fst = μ ∧ π.map Prod.snd = μ'

/-- The coefficients of (A1) and the derivatives of `f` and `g` used in (A2)–(A4), (B1), (C1)
(witness functions; their defining properties are in `Coeff`).
* `b₀, b₁, b̄₁, b₂` and `σ₀, σ₁, σ̄₁` are the coefficient functions of (A1); `σ₁ t j` is the matrix
  multiplying `x_j`, so `σ₁(t)x = Σⱼ xⱼ σ₁(t)ⱼ`.
* `fx, fα` are the gradients `∂ₓf, ∂_αf`; `fμ t x μ α x'` is `∂_μf(t, x, μ, α)(x')`; `gx, gμ`
  likewise for `g`.
* `ft = ∂_t f`, `fxx = ∂²ₓₓf`, `fxα = ∂²ₓ_αf` (the derivative in `α` of `∂ₓf`), `fαα = ∂²_{αα}f`,
  `fxμ t x μ α x' = ∂ₓ∂_μf(Θ)(x')`, `fαμ = ∂_α∂_μf(Θ)(x')`, `fvμ = ∂_v∂_μf(Θ)(v)|_{v=x'}`, and
  `fμμ t x μ α x' j v = ∂_μ((∂_μf(Θ)(x'))_j)(μ)(v)`, the second-order L-derivative. -/
structure Deriv (d k : ℕ) where
  b0 : ℝ → E d
  b1 : ℝ → Matrix (Fin d) (Fin d) ℝ
  b1bar : ℝ → Matrix (Fin d) (Fin d) ℝ
  b2 : ℝ → Matrix (Fin d) (Fin k) ℝ
  σ0 : ℝ → Matrix (Fin d) (Fin d) ℝ
  σ1 : ℝ → Fin d → Matrix (Fin d) (Fin d) ℝ
  σ1bar : ℝ → Fin d → Matrix (Fin d) (Fin d) ℝ
  fx : ℝ → E d → Measure (E d) → (Fin k → ℝ) → E d
  fα : ℝ → E d → Measure (E d) → (Fin k → ℝ) → Fin k → ℝ
  fμ : ℝ → E d → Measure (E d) → (Fin k → ℝ) → E d → E d
  gx : E d → Measure (E d) → E d
  gμ : E d → Measure (E d) → E d → E d
  ft : ℝ → E d → Measure (E d) → (Fin k → ℝ) → ℝ
  fxx : ℝ → E d → Measure (E d) → (Fin k → ℝ) → E d →L[ℝ] E d
  fxα : ℝ → E d → Measure (E d) → (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] E d
  fαα : ℝ → E d → Measure (E d) → (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)
  fxμ : ℝ → E d → Measure (E d) → (Fin k → ℝ) → E d → E d →L[ℝ] E d
  fαμ : ℝ → E d → Measure (E d) → (Fin k → ℝ) → E d → (Fin k → ℝ) →L[ℝ] E d
  fvμ : ℝ → E d → Measure (E d) → (Fin k → ℝ) → E d → E d →L[ℝ] E d
  fμμ : ℝ → E d → Measure (E d) → (Fin k → ℝ) → E d → Fin d → E d → E d

/-- A real function of time is bounded and Lipschitz on `[0, T]`. -/
def BddLipOn (T : ℝ≥0) (h : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ s ∈ Set.Icc (0 : ℝ) T, |h t| ≤ C ∧ |h t - h s| ≤ C * |t - s|

/-- **(A1)**: `b(t, x, μ, α) = b₀(t) + b₁(t)x + b̄₁(t)μ̄ + b₂(t)α` and
`σ(t, x, μ) = σ₀(t) + σ₁(t)x + σ̄₁(t)μ̄` for `t ∈ [0, T]`, `μ ∈ 𝒫₂(ℝᵈ)`, with bounded Lipschitz
deterministic coefficient functions (every entry bounded and Lipschitz on `[0, T]`). -/
def A1 {d k : ℕ} (M : Model d k) (D : Deriv d k) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ (x : E d) (μ : Measure (E d)) (a : Fin k → ℝ), IsP2 μ →
    M.b t x μ a = D.b0 t + (D.b1 t).mulVec x + (D.b1bar t).mulVec (mean μ) + (D.b2 t).mulVec a ∧
    M.σ t x μ = D.σ0 t + ∑ j, x j • D.σ1 t j + ∑ j, mean μ j • D.σ1bar t j) ∧
  (∀ i, BddLipOn M.T (fun t => D.b0 t i)) ∧
  (∀ i j, BddLipOn M.T (fun t => D.b1 t i j)) ∧
  (∀ i j, BddLipOn M.T (fun t => D.b1bar t i j)) ∧
  (∀ i j, BddLipOn M.T (fun t => D.b2 t i j)) ∧
  (∀ i j, BddLipOn M.T (fun t => D.σ0 t i j)) ∧
  (∀ l i j, BddLipOn M.T (fun t => D.σ1 t l i j)) ∧
  (∀ l i j, BddLipOn M.T (fun t => D.σ1bar t l i j))

/-- **(A2)** ("Pontryagin optimality", [18] p. 542): `f` is differentiable in `(x, α)` with
gradients `fx, fα`; `f` and `g` have L-derivatives `fμ, gμ` in `μ`; `g` is differentiable in `x`
with gradient `gx`; `t ↦ f(t, 0, δ₀, 0)` is bounded on `[0, T]`; and for some `L`, for all `R ≥ 0`
and `|x|, M₂(μ), |α| ≤ R`, the quantities `|∂ₓf|`, `|∂ₓg|`, `|∂_αf|` and the `L²(μ)`-norms of
`x' ↦ ∂_μf(t, x, μ, α)(x')`, `x' ↦ ∂_μg(x, μ)(x')` are at most `L(1 + R)`. -/
def A2 {d k : ℕ} (M : Model d k) (D : Deriv d k) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ (x : E d) (μ : Measure (E d)) (a : Fin k → ℝ), IsP2 μ →
    HasFDerivAt (fun p : E d × (Fin k → ℝ) => M.f t p.1 μ p.2)
      ((dotL (D.fx t x μ a)).coprod (dotL (D.fα t x μ a))) (x, a)) ∧
  (∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ (x : E d) (a : Fin k → ℝ),
    IsLDeriv (fun μ => M.f t x μ a) (fun μ x' => D.fμ t x μ a x')) ∧
  (∀ (x : E d) (μ : Measure (E d)), IsP2 μ →
    HasFDerivAt (fun x' => M.g x' μ) (dotL (D.gx x μ)) x) ∧
  (∀ x : E d, IsLDeriv (fun μ => M.g x μ) (fun μ x' => D.gμ x μ x')) ∧
  (∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) M.T, |M.f t 0 (Measure.dirac 0) 0| ≤ C) ∧
  ∃ L : ℝ, ∀ R : ℝ, 0 ≤ R → ∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ (x : E d) (μ : Measure (E d))
    (a : Fin k → ℝ), IsP2 μ → ‖x‖ ≤ R → M2 μ ≤ R → ‖a‖ ≤ R →
    ‖D.fx t x μ a‖ ≤ L * (1 + R) ∧ ‖D.gx x μ‖ ≤ L * (1 + R) ∧ ‖D.fα t x μ a‖ ≤ L * (1 + R) ∧
    ∫⁻ x', ‖D.fμ t x μ a x'‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal ((L * (1 + R)) ^ 2) ∧
    ∫⁻ x', ‖D.gμ x μ x'‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal ((L * (1 + R)) ^ 2)

/-- **(A3)**: `∂ₓf, ∂_αf` are `L`-Lipschitz in `(x, α, μ)` and `∂ₓg` in `(x, μ)` (`W₂` in `μ`),
and for all random variables `X, X'` with laws `μ, μ'` — i.e. for every coupling `π` of `μ, μ'` —
`𝔼|∂_μf(t, x', μ', α')(X') − ∂_μf(t, x, μ, α)(X)|² ≤ L(|(x', α') − (x, α)|² + 𝔼|X' − X|²)`
and `𝔼|∂_μg(x', μ')(X') − ∂_μg(x, μ)(X)|² ≤ L(|x' − x|² + 𝔼|X' − X|²)`. -/
def A3 {d k : ℕ} (M : Model d k) (D : Deriv d k) : Prop :=
  ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ (x x' : E d) (μ μ' : Measure (E d)) (a a' : Fin k → ℝ),
    IsP2 μ → IsP2 μ' →
    ‖D.fx t x' μ' a' - D.fx t x μ a‖ ≤ L * (‖x' - x‖ + ‖a' - a‖ + (W2 μ μ').toReal) ∧
    ‖D.fα t x' μ' a' - D.fα t x μ a‖ ≤ L * (‖x' - x‖ + ‖a' - a‖ + (W2 μ μ').toReal) ∧
    ‖D.gx x' μ' - D.gx x μ‖ ≤ L * (‖x' - x‖ + (W2 μ μ').toReal) ∧
    ∀ π : Measure (E d × E d), IsCoupling μ μ' π →
      ∫⁻ p, ‖D.fμ t x' μ' a' p.2 - D.fμ t x μ a p.1‖ₑ ^ 2 ∂π ≤
        ENNReal.ofReal L * (ENNReal.ofReal (‖x' - x‖ ^ 2 + ‖a' - a‖ ^ 2) +
          ∫⁻ p, ‖p.2 - p.1‖ₑ ^ 2 ∂π) ∧
      ∫⁻ p, ‖D.gμ x' μ' p.2 - D.gμ x μ p.1‖ₑ ^ 2 ∂π ≤
        ENNReal.ofReal L * (ENNReal.ofReal (‖x' - x‖ ^ 2) + ∫⁻ p, ‖p.2 - p.1‖ₑ ^ 2 ∂π)

/-- **(A4)**: `f` is L-convex with a constant `λ > 0`: for all `t ∈ [0, T]`, `(x, μ, α)`,
`(x', μ', α')` with `μ, μ' ∈ 𝒫₂` and every coupling `π` of `(μ, μ')` (the law of `(X, X')`),
`f(t, x', μ', α') − f(t, x, μ, α) − ∂_{(x,α)}f(t, x, μ, α)·(x' − x, α' − α)
 − 𝔼[∂_μf(t, x, μ, α)(X)·(X' − X)] ≥ λ|α' − α|²`;
and `g` is L-convex in `(x, μ)`: the same inequality for `g`, without the `α` terms and with right
hand side `0`. -/
def A4 {d k : ℕ} (M : Model d k) (D : Deriv d k) : Prop :=
  ∃ lam : ℝ, 0 < lam ∧
    (∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ (x x' : E d) (μ μ' : Measure (E d)) (a a' : Fin k → ℝ),
      IsP2 μ → IsP2 μ' → ∀ π : Measure (E d × E d), IsCoupling μ μ' π →
      M.f t x' μ' a' - M.f t x μ a - dot (D.fx t x μ a) (x' - x) - dot (D.fα t x μ a) (a' - a)
        - ∫ p, dot (D.fμ t x μ a p.1) (p.2 - p.1) ∂π ≥ lam * ‖a' - a‖ ^ 2) ∧
    (∀ (x x' : E d) (μ μ' : Measure (E d)), IsP2 μ → IsP2 μ' →
      ∀ π : Measure (E d × E d), IsCoupling μ μ' π →
      M.g x' μ' - M.g x μ - dot (D.gx x μ) (x' - x)
        - ∫ p, dot (D.gμ x μ p.1) (p.2 - p.1) ∂π ≥ 0)

/-- **(B1)**: for every `μ ∈ 𝒫₂(ℝᵈ)` and `α ∈ A`, `(t, x) ↦ ∂_αf(t, x, μ, α)` is Lipschitz on
`[0, T] × ℝᵈ` with a constant independent of `μ` and `α`. -/
def B1 {d k : ℕ} (M : Model d k) (D : Deriv d k) : Prop :=
  ∃ L : ℝ, ∀ (μ : Measure (E d)) (a : Fin k → ℝ), IsP2 μ →
    ∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ t' ∈ Set.Icc (0 : ℝ) M.T, ∀ x x' : E d,
      ‖D.fα t x μ a - D.fα t' x' μ a‖ ≤ L * (|t - t'| + ‖x - x'‖)

/-- **(B3)**: `μ₀ ∈ 𝒫₄(ℝᵈ)`: `M₄(μ₀) = ∫ |x|⁴ dμ₀(x) < ∞`. -/
def B3 {d k : ℕ} (M : Model d k) : Prop :=
  IsP4 M.μ0

/-- The size `|t| + |x| + M₂(μ) + |α|` of `Θ = (t, x, μ, α)`, used for growth conditions. -/
noncomputable def sizeΘ {d k : ℕ} (t : ℝ) (x : E d) (μ : Measure (E d)) (a : Fin k → ℝ) : ℝ :=
  |t| + ‖x‖ + M2 μ + ‖a‖

/-- **(C1)**: with `Θ = (t, x, μ, α)`, `t ∈ [0, T]`, `μ ∈ 𝒫₂`: `f` is differentiable in `t` with
`|∂_tf(Θ)|` of at most quadratic growth; `|∂_αf(Θ)|`, `|∂ₓf(Θ)|` and `(Θ, x') ↦ |∂_μf(Θ)(x')|` of
at most linear growth; and the second derivatives `∂²ₓₓf`, `∂²ₓ_αf`, `∂²_{αα}f`, `∂ₓ∂_μf(Θ)(x')`,
`∂_α∂_μf(Θ)(x')`, `∂_v∂_μf(Θ)(v)|_{v=x'}` exist and are bounded, as is the second-order L-derivative
`∂²_μf(Θ)(x', x')` on the diagonal. -/
def C1 {d k : ℕ} (M : Model d k) (D : Deriv d k) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ (x : E d) (μ : Measure (E d)) (a : Fin k → ℝ), IsP2 μ →
    HasDerivWithinAt (fun s => M.f s x μ a) (D.ft t x μ a) (Set.Icc (0 : ℝ) M.T) t ∧
    HasFDerivAt (fun x' => D.fx t x' μ a) (D.fxx t x μ a) x ∧
    HasFDerivAt (fun a' => D.fx t x μ a') (D.fxα t x μ a) a ∧
    HasFDerivAt (fun a' => D.fα t x μ a') (D.fαα t x μ a) a ∧
    ∀ x' : E d,
      HasFDerivAt (fun y => D.fμ t y μ a x') (D.fxμ t x μ a x') x ∧
      HasFDerivAt (fun a' => D.fμ t x μ a' x') (D.fαμ t x μ a x') a ∧
      HasFDerivAt (fun v => D.fμ t x μ a v) (D.fvμ t x μ a x') x') ∧
  (∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ (x x' : E d) (a : Fin k → ℝ) (j : Fin d),
    IsLDeriv (fun μ => D.fμ t x μ a x' j) (fun μ v => D.fμμ t x μ a x' j v)) ∧
  ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ (x x' : E d) (μ : Measure (E d)) (a : Fin k → ℝ),
    IsP2 μ →
    |D.ft t x μ a| ≤ C * (1 + sizeΘ t x μ a) ^ 2 ∧
    ‖D.fα t x μ a‖ ≤ C * (1 + sizeΘ t x μ a) ∧
    ‖D.fx t x μ a‖ ≤ C * (1 + sizeΘ t x μ a) ∧
    ‖D.fμ t x μ a x'‖ ≤ C * (1 + sizeΘ t x μ a + ‖x'‖) ∧
    ‖D.fxx t x μ a‖ ≤ C ∧ ‖D.fxα t x μ a‖ ≤ C ∧ ‖D.fαα t x μ a‖ ≤ C ∧
    ‖D.fxμ t x μ a x'‖ ≤ C ∧ ‖D.fαμ t x μ a x'‖ ≤ C ∧ ‖D.fvμ t x μ a x'‖ ≤ C ∧
    ∀ j : Fin d, ‖D.fμμ t x μ a x' j x'‖ ≤ C

/-- The assumptions on the coefficients and the initial law: (A1)–(A4), (B1), (B3), (C1), with the
witnesses `D`. -/
structure Coeff {d k : ℕ} (M : Model d k) (D : Deriv d k) : Prop where
  a1 : A1 M D
  a2 : A2 M D
  a3 : A3 M D
  a4 : A4 M D
  b1 : B1 M D
  b3 : B3 M
  c1 : C1 M D

/-! ### The minimizer (2.6), the FBSDE (2.7) and the decoupling field ((2.8)–(2.10), (B2), (C2), (C3)) -/

/-- (2.6): `α̂(t, x, μ, y)` minimizes `α ↦ H̃(t, x, μ, y, α)` over `A = ℝᵏ`, for `t ∈ [0, T]`,
`x, y ∈ ℝᵈ`, `μ ∈ 𝒫₂(ℝᵈ)`. -/
def IsMinimizer {d k : ℕ} (M : Model d k)
    (αhat : ℝ → E d → Measure (E d) → E d → Fin k → ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ (x : E d) (μ : Measure (E d)) (y : E d), IsP2 μ →
    ∀ a : Fin k → ℝ, M.Htilde t x μ y (αhat t x μ y) ≤ M.Htilde t x μ y a

/-- `∂ₓH(t, x, μ, y, z, α)` under (A1): `b₁(t)ᵀy + σ₁(t)ᵀ·z + ∂ₓf(t, x, μ, α)`, with
`(σ₁(t)ᵀ·z)_j = Σ_{a,b} σ₁(t)_{j,ab} z_{ab}`. The matrix `z` is given by its columns `z j`. -/
noncomputable def dxH {d k : ℕ} (D : Deriv d k) (t : ℝ) (x : E d) (μ : Measure (E d)) (y : E d)
    (z : Fin d → E d) (a : Fin k → ℝ) : E d :=
  fun j => (∑ i, D.b1 t i j * y i) + (∑ i, ∑ l, D.σ1 t j i l * z l i) + D.fx t x μ a j

/-- `∂_μH(t, x', μ, y', z', α')(v)` under (A1): `b̄₁(t)ᵀy' + σ̄₁(t)ᵀ·z' + ∂_μf(t, x', μ, α')(v)`
(b and σ depend on `μ` only through `μ̄`, so `∂_μb = b̄₁` and `∂_μσ = σ̄₁`). -/
noncomputable def dμH {d k : ℕ} (D : Deriv d k) (t : ℝ) (x' : E d) (μ : Measure (E d)) (y' : E d)
    (z' : Fin d → E d) (a' : Fin k → ℝ) (v : E d) : E d :=
  fun j => (∑ i, D.b1bar t i j * y' i) + (∑ i, ∑ l, D.σ1bar t j i l * z' l i) + D.fμ t x' μ a' v j

/-- The Pontryagin objects of §2.2: `α̂` satisfies (2.6), and the MKV FBSDE (2.7) has a solution
`(X, Y, Z)` on some Problem-1 setting, with `μ_t = ℒ(X_t)` the given flow and `Y_t = V(t, X_t)` a.s.
((2.8)–(2.9)); `V` satisfies (B2), (C2), and `α̂` satisfies (C3).

The backward equation is Peng's `−dY = F dt − Σⱼ Zⱼ dWʲ` with
`F(s, y, z) = ∂ₓH(s, X_s, μ_s, y, z, α̂(s, X_s, μ_s, y)) + 𝔼̃[∂_μH(s, X̃_s, μ_s, Ỹ_s, Z̃_s,
α̂(s, X̃_s, μ_s, Ỹ_s))(X_s)]` and `Y_T = ∂ₓg(X_T, μ_T) + 𝔼̃[∂_μg(X̃_T, μ_T)(X_T)]`; the copy
expectation `𝔼̃` is the integral over a second copy `ω'` of the probability space. -/
structure DecouplingField {d k : ℕ} (M : Model d k) (D : Deriv d k)
    (αhat : ℝ → E d → Measure (E d) → E d → Fin k → ℝ) (μflow : ℝ → Measure (E d))
    (V : ℝ → E d → E d) : Prop where
  minimizer : IsMinimizer M αhat
  fbsde : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : ℝ≥0 → Ω → E d) (X0 : Ω → E d)
      (X Y : ℝ≥0 → Ω → E d) (Z : Fin d → ℝ≥0 → Ω → E d),
    Setting1 M P W X0 ∧
    Solves22 M P W X0 (fun t ω => αhat t (X t ω) (P.map (X t)) (Y t ω)) X ∧
    (∀ t : ℝ≥0, t ≤ M.T → μflow t = P.map (X t)) ∧
    Peng1990.SMP.SolvesBSDE (filt1 W X0) P M.T W
      (fun ω => D.gx (X M.T ω) (P.map (X M.T)) +
        ∫ ω', D.gμ (X M.T ω') (P.map (X M.T)) (X M.T ω) ∂P)
      (fun s ω y z => dxH D s (X s ω) (P.map (X s)) y z (αhat s (X s ω) (P.map (X s)) y) +
        ∫ ω', dμH D s (X s ω') (P.map (X s)) (Y s ω') (fun j => Z j s ω')
          (αhat s (X s ω') (P.map (X s)) (Y s ω')) (X s ω) ∂P)
      Y Z ∧
    ∀ t : ℝ≥0, t ≤ M.T → ∀ᵐ ω ∂P, Y t ω = V t (X t ω)
  /-- (B2): `(t, x) ↦ V(t, x)` is Lipschitz on `[0, T] × ℝᵈ`. -/
  b2 : ∃ L : ℝ≥0, LipschitzOnWith L (fun p : ℝ × E d => V p.1 p.2) (Set.Icc (0 : ℝ) M.T ×ˢ Set.univ)
  /-- (C2): `V` is twice differentiable in `x` and `(t, x) ↦ ∂²ₓₓV(t, x)` is Lipschitz. -/
  c2 : ∃ (Vx : ℝ → E d → E d →L[ℝ] E d) (Vxx : ℝ → E d → E d →L[ℝ] E d →L[ℝ] E d) (L : ℝ≥0),
    (∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ x : E d,
      HasFDerivAt (V t) (Vx t x) x ∧ HasFDerivAt (Vx t) (Vxx t x) x) ∧
    LipschitzOnWith L (fun p : ℝ × E d => Vxx p.1 p.2) (Set.Icc (0 : ℝ) M.T ×ˢ Set.univ)
  /-- (C3): `α̂` is twice differentiable in `(x, y)` and its second derivatives (`∂²ₓₓα̂`, `∂²_{yy}α̂`,
  `∂²ₓ_yα̂`, the blocks of `A2`) are Lipschitz in `(t, x, μ, y)`, with `W₂` in `μ`. -/
  c3 : ∃ (A1 : ℝ → E d → Measure (E d) → E d → (E d × E d) →L[ℝ] (Fin k → ℝ))
      (A2 : ℝ → E d → Measure (E d) → E d → (E d × E d) →L[ℝ] (E d × E d) →L[ℝ] (Fin k → ℝ))
      (L : ℝ),
    (∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ (x y : E d) (μ : Measure (E d)), IsP2 μ →
      HasFDerivAt (fun p : E d × E d => αhat t p.1 μ p.2) (A1 t x μ y) (x, y) ∧
      HasFDerivAt (fun p : E d × E d => A1 t p.1 μ p.2) (A2 t x μ y) (x, y)) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ t' ∈ Set.Icc (0 : ℝ) M.T, ∀ (x x' y y' : E d)
      (μ μ' : Measure (E d)), IsP2 μ → IsP2 μ' →
      ‖A2 t x μ y - A2 t' x' μ' y'‖ ≤ L * (|t - t'| + ‖x - x'‖ + (W2 μ μ').toReal + ‖y - y'‖)

/-- The optimal feedback (3.3): `v̂(t, x) = α̂(t, x, μ_t, V(t, x))`. -/
noncomputable def vhat {d k : ℕ} (αhat : ℝ → E d → Measure (E d) → E d → Fin k → ℝ)
    (μflow : ℝ → Measure (E d)) (V : ℝ → E d → E d) : ℝ → E d → Fin k → ℝ :=
  fun t x => αhat t x (μflow t) (V t x)

end DeepMFC.FiniteHorizon


