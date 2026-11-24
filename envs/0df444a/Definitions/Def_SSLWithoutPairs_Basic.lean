-- Prove2me | Definitions.Def_SSLWithoutPairs_Basic
-- name    : SSLWithoutPairs_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T06:36:26.841979+00:00
-- url     : https://prove2.me/theorems/3594f66c-60ac-4a91-ab32-064158515e35
-- title:
--   Linear BYOL/SimSiam model: objective, augmentation moments, gradient flows and reduced dynamics
-- statement:
--   Objects of Sections 2 and 3 and Appendices A and B of Tian, Chen and Ganguli (2021), for the bias-free linear BYOL/SimSiam model.
--
--   1. **Norms and eigenvalues.** $\|v\|_2^2=\sum_i v_i^2$; $\|A\|_F=(\sum_{i,j}A_{ij}^2)^{1/2}$; $\lambda_{\min}(A)$ is the least real root of the characteristic polynomial of a square real matrix $A$ (used only for symmetric $A$).
--   2. **Trajectories.** A matrix trajectory $A(t)$, $t\ge0$, has derivative $\dot A(t)=A'(t)$ if every entry has that derivative within $[0,\infty)$ at every $t\ge0$ (one-sided at $t=0$).
--   3. **Data and augmentation (Section 2).** The data $x\in\mathbb R^{n_1}$ has law $\mu=p(x)$ and the augmentation is a Markov kernel $\kappa=p_{\mathrm{aug}}(\cdot\mid x)$. Then $\bar x(x)=\mathbb E_{x'\sim\kappa(x)}[x']$, $X=\mathbb E_x[\bar x\bar x^\top]$ and $X'=\mathbb E_x[\operatorname{Var}_{x'\mid x}[x']]$.
--   4. **Objective (eq. 1).** For $W,W_a\in\mathbb R^{n_2\times n_1}$ and $W_p\in\mathbb R^{n_2\times n_2}$, $J(W,W_p;W_a)=\tfrac12\mathbb E\|W_pWx_1-W_ax_2\|_2^2$, where $x\sim\mu$ and $x_1,x_2\sim\kappa(x)$ are independent given $x$. The target weight $W_a$ is a separate argument, which encodes the stop-gradient.
--   5. **Flows (eqs. 2, 3).** $\dot W_p=\alpha_p(-W_pW(X+X')+W_aX)W^\top-\eta W_p$ and $\dot W=W_p^\top(-W_pW(X+X')+W_aX)-\eta W$.
--   6. **No-stop-gradient matrix (Theorem 2).** $H=X'\otimes(W_p^\top W_p+I_{n_2})+X\otimes\tilde W_p^\top\tilde W_p+\eta I_{n_1n_2}$ with $\tilde W_p=W_p-I_{n_2}$, acting on $\operatorname{vec}(W)$ (columns stacked).
--   7. **Reduced flows (Section 3).** Under Assumptions 1 and 2 ($W_a=\tau W$, $X=I$, $X'=\sigma^2I$, $F=WW^\top$) the predictor flow is $\dot W_p=-\alpha_p(1+\sigma^2)W_pF+\alpha_p\tau F-\eta W_p$ (eq. 62). The symmetrised flow (eq. 7) is $\dot W_p=-\frac{\alpha_p}2(1+\sigma^2)\{W_p,F\}+\alpha_p\tau F-\eta W_p$, $\dot F=-(1+\sigma^2)\{W_p^2,F\}+\tau\{W_p,F\}-2\eta F$, with $\{A,B\}=AB+BA$. The commutator is $[F,W_p]=FW_p-W_pF$, and
--   $$K=(1+\sigma^2)\Big[\frac{\alpha_p}2F+W_p^2-\frac{\tau}{1+\sigma^2}W_p\Big]+\frac32\eta I\quad\text{(eq. 9)}.$$
--   8. **Modes (Section 3.2).** The right sides of eqs. (11), (12), (16) are $\alpha_ps[\tau-(1+\sigma^2)p]-\eta p$, $2ps[\tau-(1+\sigma^2)p]-2\eta s$ and $p^2[\tau-(1+\sigma^2)p]-\eta p$. The fixed points are $p^*_\pm=\big(\tau\pm\sqrt{\tau^2-4\eta(1+\sigma^2)}\big)/(2(1+\sigma^2))$, and $\Delta=p[\tau-(1+\sigma^2)p]-\eta$.
--
--   **Formalization Note** Vectors of $\mathbb R^n$ are functions $\mathrm{Fin}\,n\to\mathbb R$, and the Euclidean norm is written out, since Lean's default norm on this type is the sup norm. Derivatives of matrix trajectories are taken entrywise. $J$ is a Bochner integral against $\mu\otimes(\kappa\times\kappa)$. Statements that use $J$ assume finite second moments, so that this integral is not a junk value.
-- source:
--   Tian, Chen and Ganguli, Understanding Self-Supervised Learning Dynamics without Contrastive Pairs, arXiv:2102.06810v4 (2021), Sections 2, 3, 3.1, 3.2 and Appendices A, B

import Mathlib

/-!
Tian, Chen and Ganguli, *Understanding Self-Supervised Learning Dynamics without Contrastive
Pairs*, arXiv:2102.06810v4 (ICML 2021): the bias-free linear BYOL/SimSiam model of Section 2
and Appendix A (objective, augmentation moments `X`, `X'`, gradient flows), the reduced dynamics
of Section 3 and Appendix B under Assumptions 1-3 (eqs. (7), (9), (11)-(13), (16), (17), (62)),
and the norms and minimal eigenvalue used in Theorems 2 and 3 and Lemma 2.
-/

open MeasureTheory ProbabilityTheory Matrix

noncomputable section

namespace SSLWithoutPairs

/-- Squared Euclidean norm `‖v‖₂²` of a vector of `ℝⁿ` (Section 2, eq. (1)). -/
def sqNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ := ∑ i, v i ^ 2

/-- Euclidean norm `‖v‖₂` of a vector (Lemma 2, Appendix A, p. 14). -/
def l2Norm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ := Real.sqrt (sqNorm v)

/-- Frobenius norm `‖A‖_F` of a real matrix (Theorem 3, eq. (10), p. 5). -/
def frobNorm {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

/-- The minimal eigenvalue `λ_min(A)` of a square real matrix (Theorems 2 and 3, Lemma 2):
the least real root of its characteristic polynomial. It is only applied to symmetric matrices,
whose eigenvalues are all real. -/
def minEig {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : ℝ :=
  sInf {μ : ℝ | A.charpoly.IsRoot μ}

/-- A matrix-valued trajectory `A(t)`, `t ≥ 0`, has time derivative `Ȧ(t) = A'(t)` for every
`t ≥ 0` (one-sided at `t = 0`), entrywise. This is how the gradient flows of Section 2 and the
reduced flows of Section 3 are read. -/
def HasMatDerivOn {m n : Type*} (A A' : ℝ → Matrix m n ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ i j, HasDerivWithinAt (fun s => A s i j) (A' t i j) (Set.Ici 0) t

section Moments

variable {n : ℕ}

/-- Section 2, p. 3: the average augmented view `x̄(x) = E_{x' ∼ p_aug(·|x)}[x']` of a data
point `x`, for the augmentation kernel `κ = p_aug`. -/
def augMean (κ : Kernel (Fin n → ℝ) (Fin n → ℝ)) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∫ y, y i ∂(κ x)

/-- Section 2, p. 3: `X = E_x[x̄(x) x̄(x)ᵀ]`, for the data distribution `μ = p(x)`. -/
def augMeanCorr (μ : Measure (Fin n → ℝ)) (κ : Kernel (Fin n → ℝ) (Fin n → ℝ)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ x, augMean κ x i * augMean κ x j ∂μ

/-- Section 2, p. 3: `X' = E_x[Var_{x'|x}[x']]`, the covariance of the augmented views of `x`,
averaged over the data. -/
def augCov (μ : Measure (Fin n → ℝ)) (κ : Kernel (Fin n → ℝ) (Fin n → ℝ)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ x, (∫ y, (y i - augMean κ x i) * (y j - augMean κ x j) ∂(κ x)) ∂μ

end Moments

/-- Eq. (1) (Appendix A, eq. (20)): the BYOL objective
`J = ½ E_{x ∼ p, x₁, x₂ ∼ p_aug(·|x)} ‖W_p W x₁ - W_a x₂‖²`, with the two views drawn
independently given `x`. The target weight `W_a` is a separate argument: the stop-gradient means
that `J` is differentiated in `W` and `W_p` with `W_a` held fixed (for SimSiam `W_a = W`). -/
def byolLoss {n₁ n₂ : ℕ} (μ : Measure (Fin n₁ → ℝ)) (κ : Kernel (Fin n₁ → ℝ) (Fin n₁ → ℝ))
    [IsSFiniteKernel κ] (Wp : Matrix (Fin n₂) (Fin n₂) ℝ) (W Wa : Matrix (Fin n₂) (Fin n₁) ℝ) :
    ℝ :=
  (1 / 2 : ℝ) * ∫ q, sqNorm (Wp *ᵥ (W *ᵥ q.2.1) - Wa *ᵥ q.2.2) ∂(μ ⊗ₘ (κ ×ₖ κ))

/-- Eq. (2): the right side of the predictor flow
`Ẇ_p = α_p (-W_p W (X + X') + W_a X) Wᵀ - η W_p`. -/
def byolFlowWp {n₁ n₂ : ℕ} (αp η : ℝ) (X X' : Matrix (Fin n₁) (Fin n₁) ℝ)
    (Wp : Matrix (Fin n₂) (Fin n₂) ℝ) (W Wa : Matrix (Fin n₂) (Fin n₁) ℝ) :
    Matrix (Fin n₂) (Fin n₂) ℝ :=
  αp • ((-(Wp * W * (X + X')) + Wa * X) * Wᵀ) - η • Wp

/-- Eq. (3): the right side of the online flow `Ẇ = W_pᵀ (-W_p W (X + X') + W_a X) - η W`. -/
def byolFlowW {n₁ n₂ : ℕ} (η : ℝ) (X X' : Matrix (Fin n₁) (Fin n₁) ℝ)
    (Wp : Matrix (Fin n₂) (Fin n₂) ℝ) (W Wa : Matrix (Fin n₂) (Fin n₁) ℝ) :
    Matrix (Fin n₂) (Fin n₁) ℝ :=
  Wpᵀ * (-(Wp * W * (X + X')) + Wa * X) - η • W

/-- Theorem 2, p. 3: `H = X' ⊗ (W_pᵀ W_p + I_{n₂}) + X ⊗ W̃_pᵀ W̃_p + η I_{n₁ n₂}` with
`W̃_p = W_p - I_{n₂}` and `⊗` the Kronecker product, indexed so that it acts on
`vec(W)` (`Matrix.vec`, columns stacked). -/
def noStopH {n₁ n₂ : ℕ} (X X' : Matrix (Fin n₁) (Fin n₁) ℝ) (η : ℝ)
    (Wp : Matrix (Fin n₂) (Fin n₂) ℝ) : Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℝ :=
  Matrix.kronecker X' (Wpᵀ * Wp + 1) + Matrix.kronecker X ((Wp - 1)ᵀ * (Wp - 1)) + η • 1

/-- Eq. (62) (Appendix B, p. 15): the predictor flow of eq. (2) under Assumptions 1 and 2
(`W_a = τ W`, `X = I`, `X' = σ² I`, `F = W Wᵀ`):
`Ẇ_p = -α_p (1 + σ²) W_p F + α_p τ F - η W_p`. -/
def isoFlowWp {d : ℕ} (αp σ η τ : ℝ) (Wp F : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  -(αp * (1 + σ ^ 2)) • (Wp * F) + (αp * τ) • F - η • Wp

/-- Eq. (7), first line: the symmetrised predictor flow
`Ẇ_p = -(α_p/2)(1 + σ²){W_p, F} + α_p τ F - η W_p`, `{A, B} = AB + BA`. -/
def symFlowWp {d : ℕ} (αp σ η τ : ℝ) (Wp F : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  -(αp / 2 * (1 + σ ^ 2)) • (Wp * F + F * Wp) + (αp * τ) • F - η • Wp

/-- Eq. (7), second line: `Ḟ = -(1 + σ²){W_p², F} + τ{W_p, F} - 2η F`. -/
def symFlowF {d : ℕ} (σ η τ : ℝ) (Wp F : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  -(1 + σ ^ 2) • (Wp * Wp * F + F * (Wp * Wp)) + τ • (Wp * F + F * Wp) - (2 * η) • F

/-- Theorem 3: the commutator `[F, W_p] = F W_p - W_p F`. -/
def commutator {d : ℕ} (F Wp : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  F * Wp - Wp * F

/-- Eq. (9): `K = (1 + σ²)[(α_p/2) F + W_p² - τ/(1 + σ²) W_p] + (3/2) η I`. -/
def alignK {d : ℕ} (αp σ η τ : ℝ) (F Wp : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (1 + σ ^ 2) • ((αp / 2) • F + Wp * Wp - (τ / (1 + σ ^ 2)) • Wp) + ((3 / 2 : ℝ) * η) • 1

/-- Eq. (11): the decoupled predictor mode `ṗ_j = α_p s_j [τ - (1 + σ²) p_j] - η p_j`. -/
def modeFlowP (αp σ η τ p s : ℝ) : ℝ := αp * s * (τ - (1 + σ ^ 2) * p) - η * p

/-- Eq. (12): the decoupled online mode `ṡ_j = 2 p_j s_j [τ - (1 + σ²) p_j] - 2η s_j`. -/
def modeFlowS (σ η τ p s : ℝ) : ℝ := 2 * p * s * (τ - (1 + σ ^ 2) * p) - 2 * η * s

/-- Eq. (16): the predictor mode on the invariant parabola `s_j = α_p⁻¹ p_j²`, at fixed `τ`:
`ṗ_j = p_j² [τ - (1 + σ²) p_j] - η p_j`. -/
def parabolaFlowP (σ η τ p : ℝ) : ℝ := p ^ 2 * (τ - (1 + σ ^ 2) * p) - η * p

/-- Section 3.2, p. 6: the fixed point `p*_{j-} = (τ - √(τ² - 4η(1 + σ²))) / (2(1 + σ²))`
of eq. (16). -/
def fixedPointMinus (σ η τ : ℝ) : ℝ :=
  (τ - Real.sqrt (τ ^ 2 - 4 * η * (1 + σ ^ 2))) / (2 * (1 + σ ^ 2))

/-- Section 3.2, p. 6: the fixed point `p*_{j+} = (τ + √(τ² - 4η(1 + σ²))) / (2(1 + σ²))`
of eq. (16). -/
def fixedPointPlus (σ η τ : ℝ) : ℝ :=
  (τ + Real.sqrt (τ ^ 2 - 4 * η * (1 + σ ^ 2))) / (2 * (1 + σ ^ 2))

/-- Section 3.2, p. 6: `Δ_j = p_j [τ - (1 + σ²) p_j] - η`. -/
def modeDelta (σ η τ p : ℝ) : ℝ := p * (τ - (1 + σ ^ 2) * p) - η

end SSLWithoutPairs


