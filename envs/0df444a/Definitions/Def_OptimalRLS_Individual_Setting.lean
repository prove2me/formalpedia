-- Prove2me | Definitions.Def_OptimalRLS_Individual_Setting
-- name    : OptimalRLS_Individual_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T19:32:18.4988+00:00
-- url     : https://prove2.me/theorems/8559e870-ce2b-4808-8a66-1aabfe4b936b
-- title:
--   §3, pp. 6–10 — Hypotheses 1–2, the risk, the covariance form and eigen-system of T, T^s, and the prior P(b, c) of Definition 1
-- statement:
--   This file fixes the setting of Caponnetto and De Vito's analysis of regularized least squares in a reproducing kernel Hilbert space of vector-valued functions.
--
--   The input space $X$ is Polish with its Borel $\sigma$-algebra, and the output space $Y$ is a real separable Hilbert space. The hypothesis space $\mathcal H$ is a real separable Hilbert space of functions $f : X \to Y$ in which every evaluation is continuous. Hence for each $x$ there is a bounded operator $K_x : Y \to \mathcal H$ with $f(x) = K_x^* f$ for all $f \in \mathcal H$ (equation (4)).
--
--   1. **Hypothesis 1** (p. 6). The function $(x, t) \mapsto \langle K_t v, K_x w\rangle_{\mathcal H}$ is measurable for all $v, w \in Y$ (5). Moreover there is $\kappa > 0$ such that $\operatorname{Tr}(K_x^* K_x) = \sum_j \|K_x v_j\|_{\mathcal H}^2 \le \kappa$ for every $x$ (6), where $(v_j)$ is a Hilbert basis of $Y$.
--   2. **Risk** (p. 4). For a distribution $\rho$ on $Z = X \times Y$, $\mathcal E[f] = \int_Z \|f(x) - y\|_Y^2 \, d\rho(x, y)$.
--   3. **Hypothesis 2** (p. 7). The measure satisfies $\int_Z \|y\|_Y^2 \, d\rho < \infty$ (7). Some $f_{\mathcal H} \in \mathcal H$ minimizes $\mathcal E$ over $\mathcal H$ (8). For $\rho_X$-almost every $x$,
--   $$\int_Y \Big(e^{\|y - f_{\mathcal H}(x)\|_Y/M} - \frac{\|y - f_{\mathcal H}(x)\|_Y}{M} - 1\Big)\, d\rho(y \mid x) \le \frac{\Sigma^2}{2M^2}, \qquad (9)$$
--   with positive constants $M, \Sigma$.
--   4. **The operator $T = \int_X K_x K_x^* \, d\rho_X(x)$** (14) is described by its quadratic form $\langle Tf, g\rangle_{\mathcal H} = \int_X \langle f(x), g(x)\rangle_Y \, d\rho_X(x)$ and by an eigen-system: an orthonormal family $(e_n)$ and positive numbers $(t_n)$ with $\langle Tf, g\rangle = \sum_n t_n \langle f, e_n\rangle \langle g, e_n\rangle$ (16). The powers are $T^s g = \sum_n t_n^s \langle g, e_n\rangle e_n$.
--   5. **The prior $\mathcal P(b, c)$** (Definition 1, branch $b < \infty$). Fix positive constants $M, \Sigma, R, \alpha, \beta$. A probability measure $\rho$ on $Z$ belongs to $\mathcal P(b, c)$ when the following hold.
--      - Hypothesis 2 holds for the minimal-norm minimizer $f_{\mathcal H}$.
--      - $f_{\mathcal H} = T^{(c-1)/2} g$ with $\|g\|_{\mathcal H}^2 \le R$.
--      - $T$ has infinitely many nonzero eigenvalues $t_1 \ge t_2 \ge \dots > 0$ satisfying $\alpha \le n^b t_n \le \beta$ for all $n \ge 1$ (17).
--
--   These are the standing objects of the whole paper. Every statement of the individual-lower-rate mission is phrased in them.
--
--   **Formalization Note** $\mathcal H$ is Mathlib's `RKHS ℝ H X Y`, and $K_x$ is `RKHS.kerFun H x`. The paper's $\Sigma$ is written `Sig`. The marginal $\rho_X$ is `ρ.fst`, and the conditional distribution $\rho(\cdot \mid x)$ is `ρ.condKernel x`.
--   - $T$ is never formed as an operator-valued Bochner integral, which Lean would silently set to $0$ if strong measurability failed. It enters only through `covForm` and `IsEigenSystem`, which also requires the series $\sum_n t_n \langle f, e_n\rangle^2$ to be summable.
--   - The paper indexes eigenvalues from $n = 1$; here they are indexed from $0$, so (17) reads $\alpha \le (n+1)^b t_n \le \beta$.
--   - The trace in (6) is computed in one fixed Hilbert basis of $Y$; footnote 4 of the paper notes that it does not depend on the basis.
--   - Condition (9) is a `lintegral` of a nonnegative integrand.
--   - `InPrior` includes "ρ is a probability measure", and the positivity of $R, \alpha, \beta$ ($M, \Sigma > 0$ is part of `Hyp2`).
--   - For $c = 1$, $T^0$ is the projection onto $(\ker T)^\perp$. Since the minimal-norm minimizer is orthogonal to $\ker T$, this describes the same class as $T^0 = \mathrm{Id}$.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, §3, Hypothesis 1 (p. 6), Hypothesis 2 (p. 7), (12)–(16) (p. 9), Definition 1 (pp. 9–10)

import Mathlib

/-!
# Caponnetto–De Vito (2007), §3: the setting of the individual lower rate

Notation: the paper's `Σ` is written `Sig` (`Σ` is reserved in Lean 4).

* `X` is a Polish space with its Borel σ-algebra, `Y` a real separable Hilbert space (outputs),
  `H` a real separable Hilbert space of functions `X → Y` with continuous evaluations
  (Mathlib's `RKHS ℝ H X Y`); `RKHS.kerFun H x : Y →L[ℝ] H` is the paper's `K_x`, and
  `RKHS.adjoint_kerFun` is (4): `K_x^* f = f x`.
* A distribution is `ρ : Measure (X × Y)`; its marginal `ρ_X` is `ρ.fst` and the conditional
  distribution `ρ(·|x)` is `ρ.condKernel x`.
* The operator `T = ∫ K_x K_x^* dρ_X` of (14) is never built as an operator-valued integral: it
  enters only through its quadratic form `covForm` (`⟨T f, g⟩_H = ∫ ⟨f(x), g(x)⟩_Y dρ_X`) and
  through an eigen-system `(e, t)` realizing the spectral decomposition (16).

Hypothesis 1 (p. 6), verbatim: "The space H is a separable Hilbert space of functions f : X → Y
such that – for all x ∈ X there is a Hilbert-Schmidt operator K_x : Y → H satisfying
(4) f(x) = K_x^* f, f ∈ H, where K_x^* : H → Y is the adjoint of K_x; – the real function from
X × X to R (5) (x, t) ↦ ⟨K_t v, K_x w⟩_H is measurable ∀ v, w ∈ Y; – there is κ > 0 such that
(6) Tr(K_x^* K_x) ≤ κ ∀ x ∈ X."

Hypothesis 2 (p. 7), verbatim: "The probability measure ρ on Z satisfies the following properties
(7) ∫_Z ‖y‖²_Y dρ(x, y) < +∞, – there exists f_H ∈ H such that (8) E[f_H] = inf_{f∈H} E[f], where
E[f] = ∫_Z ‖f(x) − y‖²_Y dρ(x, y); – there are two positive constants Σ, M such that
(9) ∫_Y (e^{‖y−f_H(x)‖_Y/M} − ‖y − f_H(x)‖_Y/M − 1) dρ(y|x) ≤ Σ²/(2M²) for ρ_X-almost all x ∈ X."

Definition 1 (pp. 9–10), verbatim: "Let us fix the positive constants M, Σ, R, α and β. Then,
given 1 < b ≤ +∞ and 1 ≤ c ≤ 2, we define P = P(b, c) the set of probability distributions ρ on Z
such that i) Hypotheses 2 holds with the given choice for M and Σ in (9); ii) there is g ∈ H such
that f_H = T^{(c−1)/2} g with ‖g‖²_H ≤ R; iii) if b < +∞, then N = +∞ and the eigenvalues of T
given by (16) satisfy (17) α ≤ n^b t_n ≤ β ∀ n ≥ 1, whereas if b = +∞, then N ≤ β < +∞."
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace OptimalRLS.Individual

variable {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H] [RKHS ℝ H X Y]

variable (X H) in
/-- **Hypothesis 1** (p. 6), the clauses beyond "`H` is a separable Hilbert space of functions
`X → Y` with `f(x) = K_x^* f`" (which is the `RKHS` instance):
(5) `(x, t) ↦ ⟨K_t a, K_x b⟩_H` is measurable on `X × X` for all `a, b ∈ Y`;
(6) `K_x` is Hilbert–Schmidt with `Tr(K_x^* K_x) = ∑_j ‖K_x v_j‖² ≤ κ` for every `x`, computed in a
fixed Hilbert basis `v` of `Y` (the trace does not depend on the basis, footnote 4), with `κ > 0`. -/
def Hyp1 {ι : Type*} (κ : ℝ) (v : HilbertBasis ι ℝ Y) : Prop :=
  (∀ a b : Y, Measurable fun p : X × X => ⟪RKHS.kerFun H p.2 a, RKHS.kerFun H p.1 b⟫_ℝ) ∧
  0 < κ ∧
  ∀ x : X, Summable (fun j => ‖RKHS.kerFun H x (v j)‖ ^ 2) ∧
    ∑' j, ‖RKHS.kerFun H x (v j)‖ ^ 2 ≤ κ

/-- The expected risk `E[f] = ∫_Z ‖f(x) − y‖²_Y dρ(x, y)` (p. 4). It is a Bochner integral: every
statement using it carries (7) (square-integrable outputs) through `Hyp2` / `InPrior`, or concerns
an explicitly constructed distribution with Gaussian outputs. -/
noncomputable def risk (ρ : Measure (X × Y)) (f : H) : ℝ :=
  ∫ p, ‖f p.1 - p.2‖ ^ 2 ∂ρ

/-- **Hypothesis 2** (p. 7) for the constants `M, Sig > 0` and the function `fH ∈ H`, for a finite
measure `ρ` (needed to form the conditional distribution `ρ(·|x) = ρ.condKernel x`):
(7) `∫ ‖y‖² dρ < ∞`; (8) `fH` minimizes the risk over `H`; (9) the noise condition
`∫_Y (e^{‖y−fH(x)‖/M} − ‖y−fH(x)‖/M − 1) dρ(y|x) ≤ Sig²/(2M²)` for `ρ_X`-almost every `x`
(a `lintegral` of a nonnegative integrand, since `e^u − u − 1 ≥ 0`). -/
def Hyp2 (M Sig : ℝ) (ρ : Measure (X × Y)) [IsFiniteMeasure ρ] (fH : H) : Prop :=
  0 < M ∧ 0 < Sig ∧
  Integrable (fun p : X × Y => ‖p.2‖ ^ 2) ρ ∧
  (∀ f : H, risk ρ fH ≤ risk ρ f) ∧
  ∀ᵐ x ∂ρ.fst, ∫⁻ y, ENNReal.ofReal (Real.exp (‖y - fH x‖ / M) - ‖y - fH x‖ / M - 1)
      ∂(ρ.condKernel x) ≤ ENNReal.ofReal (Sig ^ 2 / (2 * M ^ 2))

/-- `fH` is the minimizer of the risk of minimal norm in `H` (p. 9: "we recover uniqueness by
choosing the one with minimal norm in H"). -/
def IsMinNormMinimizer (ρ : Measure (X × Y)) (fH : H) : Prop :=
  (∀ f : H, risk ρ fH ≤ risk ρ f) ∧
  ∀ f : H, (∀ g : H, risk ρ f ≤ risk ρ g) → ‖fH‖ ≤ ‖f‖

/-- The quadratic form of `T` (14): `⟨T f, g⟩_H = ∫_X ⟨f(x), g(x)⟩_Y dρ_X(x)`; in particular
`‖√T h‖²_H = covForm ρX h h = ∫ ‖h(x)‖² dρ_X`. -/
noncomputable def covForm (ρX : Measure X) (f g : H) : ℝ :=
  ∫ x, ⟪f x, g x⟫_ℝ ∂ρX

/-- `(e, t)` realizes the spectral decomposition (16) `T = ∑ t_n ⟨·, e_n⟩ e_n` of the operator `T` of
(14) for the marginal `ρX`: `e` is orthonormal, every `t_i > 0`, and the quadratic form of `T` is
`∑ t_i ⟨f, e_i⟩⟨g, e_i⟩` (with the series `∑ t_i ⟨f, e_i⟩²` summable, so the `tsum` is a genuine
sum). Then `(e_i)` is an orthonormal basis of `(ker T)^⊥` and the `t_i` are the nonzero
eigenvalues of `T`, repeated with multiplicity. -/
def IsEigenSystem {ι : Type*} (ρX : Measure X) (e : ι → H) (t : ι → ℝ) : Prop :=
  Orthonormal ℝ e ∧ (∀ i, 0 < t i) ∧
  (∀ f : H, Summable fun i => t i * ⟪f, e i⟫_ℝ ^ 2) ∧
  ∀ f g : H, covForm ρX f g = ∑' i, t i * ⟪f, e i⟫_ℝ * ⟪g, e i⟫_ℝ

/-- The power `T^s g = ∑_n t_n^s ⟨g, e_n⟩ e_n` (`s ≥ 0`), computed in an eigen-system of `T`. For
`s = 0` it is the orthogonal projection onto `(ker T)^⊥`; for the minimal-norm `f_H`, which is
orthogonal to `ker T`, "`f_H = T^0 g`" with `T^0` the identity or the projection describe the same
class. -/
noncomputable def Tpow {ι : Type*} (e : ι → H) (t : ι → ℝ) (s : ℝ) (g : H) : H :=
  ∑' i, ((t i) ^ s * ⟪g, e i⟫_ℝ) • e i

/-- **Definition 1** (pp. 9–10), branch `1 < b < +∞`: `ρ ∈ P(b, c)` for the positive constants
`M, Sig, R, α, β`:
`ρ` is a probability measure, and
i) Hypothesis 2 holds with `M, Sig`, for the minimal-norm minimizer `fH`;
ii) `fH = T^{(c−1)/2} g` with `‖g‖²_H ≤ R`;
iii) `N = +∞` (an `ℕ`-indexed eigen-system with nonincreasing eigenvalues) and (17)
`α ≤ n^b t_n ≤ β` for all `n ≥ 1`; the paper's `t_n, e_n` (`n ≥ 1`) are `t (n-1), e (n-1)` here,
so (17) reads `α ≤ (n+1)^b t n ≤ β` for `n : ℕ`.
The ranges `1 < b`, `1 ≤ c ≤ 2` are hypotheses of the theorems. -/
def InPrior (M Sig R α β b c : ℝ) (ρ : Measure (X × Y)) : Prop :=
  ∃ _ : IsProbabilityMeasure ρ,
  0 < R ∧ 0 < α ∧ 0 < β ∧
  ∃ fH : H, IsMinNormMinimizer ρ fH ∧ Hyp2 M Sig ρ fH ∧
    ∃ (e : ℕ → H) (t : ℕ → ℝ), IsEigenSystem ρ.fst e t ∧ Antitone t ∧
      (∀ n : ℕ, α ≤ ((n : ℝ) + 1) ^ b * t n ∧ ((n : ℝ) + 1) ^ b * t n ≤ β) ∧
      ∃ g : H, fH = Tpow e t ((c - 1) / 2) g ∧ ‖g‖ ^ 2 ≤ R

end OptimalRLS.Individual


