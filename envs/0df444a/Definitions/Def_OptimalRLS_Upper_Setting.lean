-- Prove2me | Definitions.Def_OptimalRLS_Upper_Setting
-- name    : OptimalRLS_Upper_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T19:03:51.958605+00:00
-- url     : https://prove2.me/theorems/38606cc7-8e3e-44ff-b709-ccee636dbb1d
-- title:
--   §3, pp. 6–10 — Hypotheses 1–2, the risk, the covariance form and eigen-system of T, T^s, the prior P(b, c) of Definition 1, RLS, N(λ), λ_ℓ and a_ℓ
-- statement:
--   This file sets up the vector-valued regression problem of Caponnetto and De Vito and the objects that the upper rate of Theorem 1 is stated with.
--
--   **Spaces.** The input space $X$ is a Polish space with its Borel $\sigma$-algebra, the output space $Y$ is a real separable Hilbert space, and $Z=X\times Y$. The hypothesis space $\mathcal H$ is a real separable Hilbert space of functions $f:X\to Y$ in which every evaluation $f\mapsto f(x)$ is continuous. For $x\in X$ the operator $K_x:Y\to\mathcal H$ is the adjoint of evaluation at $x$, so that $f(x)=K_x^*f$ for all $f\in\mathcal H$ (equation (4)).
--
--   **Hypothesis 1** (p. 6). Besides the above, (5) the real function $(x,t)\mapsto\langle K_tv,K_xw\rangle_{\mathcal H}$ is measurable on $X\times X$ for all $v,w\in Y$, and (6) there is $\kappa>0$ with
--   $$\operatorname{Tr}(K_x^*K_x)=\sum_j\|K_xv_j\|_{\mathcal H}^2\le\kappa\qquad\text{for all }x\in X,$$
--   where $(v_j)$ is a Hilbert basis of $Y$ (each $K_x$ is Hilbert–Schmidt).
--
--   **Risk.** For a probability measure $\rho$ on $Z$ with marginal $\rho_X$ and conditional laws $\rho(\cdot\mid x)$, the expected risk of $f\in\mathcal H$ is
--   $$\mathcal E[f]=\int_Z\|f(x)-y\|_Y^2\,d\rho(x,y).$$
--
--   **Hypothesis 2** (p. 7), for constants $M,\Sigma>0$ and $f_{\mathcal H}\in\mathcal H$: (7) $\int_Z\|y\|_Y^2\,d\rho<\infty$; (8) $\mathcal E[f_{\mathcal H}]=\inf_{f\in\mathcal H}\mathcal E[f]$; (9) for $\rho_X$-almost every $x$,
--   $$\int_Y\Big(e^{\|y-f_{\mathcal H}(x)\|_Y/M}-\frac{\|y-f_{\mathcal H}(x)\|_Y}{M}-1\Big)\,d\rho(y\mid x)\le\frac{\Sigma^2}{2M^2}.$$
--   Among the minimizers, $f_{\mathcal H}$ denotes the one of minimal norm (p. 9).
--
--   **The operator $T$.** $T=\int_XK_xK_x^*\,d\rho_X(x)$ (14) is the positive trace-class operator with quadratic form $\langle Tf,g\rangle_{\mathcal H}=\int_X\langle f(x),g(x)\rangle_Y\,d\rho_X(x)$; in particular $\|\sqrt T h\|_{\mathcal H}^2=\int_X\|h(x)\|_Y^2\,d\rho_X$. By the spectral theorem (16), $T=\sum_nt_n\langle\cdot,e_n\rangle_{\mathcal H}e_n$ with $(e_n)$ an orthonormal basis of $(\ker T)^\perp$ and $t_n>0$. Powers are $T^sg=\sum_nt_n^s\langle g,e_n\rangle e_n$ for $s\ge0$.
--
--   **Definition 1** (pp. 9–10), case $1<b<+\infty$. For positive constants $M,\Sigma,R,\alpha,\beta$ and $1\le c\le 2$, the class $\mathcal P(b,c)$ consists of the probability measures $\rho$ on $Z$ such that (i) Hypothesis 2 holds with $M$ and $\Sigma$; (ii) $f_{\mathcal H}=T^{(c-1)/2}g$ for some $g\in\mathcal H$ with $\|g\|_{\mathcal H}^2\le R$; (iii) $T$ has infinitely many nonzero eigenvalues $t_1\ge t_2\ge\cdots>0$ and
--   $$\alpha\le n^bt_n\le\beta\qquad\text{for all }n\ge1.\tag{17}$$
--
--   **Regularized least squares.** For $\lambda>0$ and a training set $\mathbf z=((x_1,y_1),\dots,(x_\ell,y_\ell))\in Z^\ell$, the RLS estimator $f_{\mathbf z}^\lambda$ minimizes (18)
--   $$\frac1\ell\sum_{i=1}^\ell\|f(x_i)-y_i\|_Y^2+\lambda\|f\|_{\mathcal H}^2,$$
--   and $f^\lambda$ minimizes the regularized expected risk $\mathcal E[f]+\lambda\|f\|_{\mathcal H}^2$. The effective dimension is
--   $$\mathcal N(\lambda)=\operatorname{Tr}[(T+\lambda)^{-1}T]=\sum_n\frac{t_n}{t_n+\lambda}.$$
--
--   **Parameter choice and rate** ((19), (20), $b<+\infty$):
--   $$\lambda_\ell=\begin{cases}(1/\ell)^{b/(bc+1)}&c>1\\(\log\ell/\ell)^{b/(b+1)}&c=1\end{cases}\qquad a_\ell=\begin{cases}(1/\ell)^{bc/(bc+1)}&c>1\\(\log\ell/\ell)^{b/(b+1)}&c=1.\end{cases}$$
--
--   These are the objects of the upper-rate theorem and of the intermediate results of §5.1–5.2.
--
--   **Formalization Note** The paper's $\Sigma$ and $\lambda$ are written `Sig` and `lam`. $\mathcal H$ is Mathlib's `RKHS ℝ H X Y` and $K_x$ is `RKHS.kerFun H x`; the trace in (6) is computed in one fixed Hilbert basis `v` of $Y$ (it does not depend on the basis). $\rho_X$ is `ρ.fst` and $\rho(\cdot\mid x)$ is `ρ.condKernel x`. The operator $T$ is never built as an operator-valued integral: it enters through its quadratic form `covForm` and through an eigen-system `(e, t)` with `IsEigenSystem` (orthonormal $e$, positive $t$, and the quadratic form equal to $\sum_it_i\langle f,e_i\rangle\langle g,e_i\rangle$ with summable weights). In Definition 1 the eigen-system is indexed by $\mathbb N$ from $0$: the paper's $t_n,e_n$ ($n\ge1$) are `t (n-1)`, `e (n-1)`, so (17) reads $\alpha\le(n+1)^bt_n\le\beta$. Condition (9) is a `lintegral` of a nonnegative integrand. The positivity of $M,\Sigma$ is part of `Hyp2` and that of $R,\alpha,\beta$ is part of `InPrior`. For $c=1$, $T^0$ is the projection onto $(\ker T)^\perp$; the minimal-norm $f_{\mathcal H}$ lies in that subspace, so this is the same class as with $T^0=\mathrm{id}$. Only the branch $1<b<+\infty$ of (19), (20) and Definition 1 is defined.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, §2 (p. 4, risk), Hypothesis 1 (p. 6), Hypothesis 2 (p. 7), (12)–(16) (p. 9), Definition 1 (pp. 9–10), (18) (p. 10), (19)–(20) (p. 11), A, B, N (p. 13)

import Mathlib

/-!
# Caponnetto–De Vito (2007), §2–§4: the setting of the upper rate

Notation: the paper's `Σ` is written `Sig` and `λ` is written `lam` (both are reserved in Lean 4).

* `X` is a Polish space with its Borel σ-algebra, `Y` a real separable Hilbert space (outputs),
  `H` a real separable Hilbert space of functions `X → Y` with continuous evaluations
  (Mathlib's `RKHS ℝ H X Y`); `RKHS.kerFun H x : Y →L[ℝ] H` is the paper's `K_x`, and
  `RKHS.adjoint_kerFun` is (4): `K_x^* f = f x`.
* A distribution is `ρ : Measure (X × Y)`; its marginal `ρ_X` is `ρ.fst` and the conditional
  `ρ(·|x)` is `ρ.condKernel x`.
* The operator `T = ∫ K_x K_x^* dρ_X` of (14) is never built as an operator-valued integral: it
  enters only through its quadratic form `covForm` (`⟨T f, g⟩_H = ∫ ⟨f(x), g(x)⟩_Y dρ_X`, by (29))
  and through an eigen-system `(e, t)` realizing the spectral decomposition (16).
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace OptimalRLS.Upper

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
fixed Hilbert basis `v` of `Y` (the trace does not depend on the basis), with `κ > 0`. -/
def Hyp1 {ι : Type*} (κ : ℝ) (v : HilbertBasis ι ℝ Y) : Prop :=
  (∀ a b : Y, Measurable fun p : X × X => ⟪RKHS.kerFun H p.2 a, RKHS.kerFun H p.1 b⟫_ℝ) ∧
  0 < κ ∧
  ∀ x : X, Summable (fun j => ‖RKHS.kerFun H x (v j)‖ ^ 2) ∧
    ∑' j, ‖RKHS.kerFun H x (v j)‖ ^ 2 ≤ κ

/-- The expected risk `E[f] = ∫_Z ‖f(x) − y‖²_Y dρ(x, y)` (p. 4). It is a Bochner integral: every
statement using it carries (7) (square-integrable outputs) through `Hyp2` or `InPrior`. -/
noncomputable def risk (ρ : Measure (X × Y)) (f : H) : ℝ :=
  ∫ p, ‖f p.1 - p.2‖ ^ 2 ∂ρ

/-- **Hypothesis 2** (p. 7), for a probability measure `ρ` on `Z = X × Y`, the constants
`M, Sig > 0` and the function `fH ∈ H`:
(7) `∫ ‖y‖² dρ < ∞`; (8) `fH` minimizes the risk over `H`; (9) the Bernstein-type noise condition
`∫_Y (e^{‖y−fH(x)‖/M} − ‖y−fH(x)‖/M − 1) dρ(y|x) ≤ Sig²/(2M²)` for `ρ_X`-almost every `x`
(a `lintegral` of a nonnegative integrand). -/
def Hyp2 (M Sig : ℝ) (ρ : Measure (X × Y)) [IsProbabilityMeasure ρ] (fH : H) : Prop :=
  0 < M ∧ 0 < Sig ∧
  Integrable (fun p : X × Y => ‖p.2‖ ^ 2) ρ ∧
  (∀ f : H, risk ρ fH ≤ risk ρ f) ∧
  ∀ᵐ x ∂ρ.fst, ∫⁻ y, ENNReal.ofReal (Real.exp (‖y - fH x‖ / M) - ‖y - fH x‖ / M - 1)
      ∂(ρ.condKernel x) ≤ ENNReal.ofReal (Sig ^ 2 / (2 * M ^ 2))

/-- `fH` is the minimizer of the risk of minimal norm in `H` (p. 9: "we recover uniqueness by
choosing the one with minimal norm"). -/
def IsMinNormMinimizer (ρ : Measure (X × Y)) (fH : H) : Prop :=
  (∀ f : H, risk ρ fH ≤ risk ρ f) ∧
  ∀ f : H, (∀ g : H, risk ρ f ≤ risk ρ g) → ‖fH‖ ≤ ‖f‖

/-- The quadratic form of `T` (14): `⟨T f, g⟩_H = ∫_X ⟨f(x), g(x)⟩_Y dρ_X(x)` (by (29)); in
particular `‖√T h‖²_H = covForm ρX h h`. -/
noncomputable def covForm (ρX : Measure X) (f g : H) : ℝ :=
  ∫ x, ⟪f x, g x⟫_ℝ ∂ρX

/-- `(e, t)` realizes the spectral decomposition (16) `T = ∑ t_n ⟨·, e_n⟩ e_n` of the operator `T` of
(14) for the marginal `ρX`: `e` is orthonormal, every `t_i > 0`, and the quadratic form of `T` is
`∑ t_i ⟨f, e_i⟩⟨g, e_i⟩` (with the series of `⟨f, e_i⟩²` weights summable, so that the `tsum` is a
genuine sum). Then `(e_i)` is an orthonormal basis of `(ker T)^⊥` and the `t_i` are the nonzero
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

variable (H) in
/-- **Definition 1** (pp. 9–10), branch `1 < b < +∞`: `ρ ∈ P(b, c)` for the positive constants
`M, Sig, R, α, β`:
i) Hypothesis 2 holds with `M, Sig`, for the minimal-norm minimizer `fH`;
ii) `fH = T^{(c−1)/2} g` with `‖g‖²_H ≤ R`;
iii) `N = +∞` (an `ℕ`-indexed eigen-system with nonincreasing eigenvalues) and (17)
`α ≤ n^b t_n ≤ β` for all `n ≥ 1`; the paper's `t_n, e_n` (`n ≥ 1`) are `t (n-1), e (n-1)` here,
so (17) reads `α ≤ (n+1)^b t n ≤ β` for `n : ℕ`.
The ranges `1 < b`, `1 ≤ c ≤ 2` are hypotheses of the theorems. The hypothesis space `H` is an
explicit argument. -/
def InPrior (M Sig R α β b c : ℝ) (ρ : Measure (X × Y)) [IsProbabilityMeasure ρ] : Prop :=
  0 < R ∧ 0 < α ∧ 0 < β ∧
  ∃ fH : H, IsMinNormMinimizer ρ fH ∧ Hyp2 M Sig ρ fH ∧
    ∃ (e : ℕ → H) (t : ℕ → ℝ), IsEigenSystem ρ.fst e t ∧ Antitone t ∧
      (∀ n : ℕ, α ≤ ((n : ℝ) + 1) ^ b * t n ∧ ((n : ℝ) + 1) ^ b * t n ≤ β) ∧
      ∃ g : H, fH = Tpow e t ((c - 1) / 2) g ∧ ‖g‖ ^ 2 ≤ R

/-- The regularized expected risk `E[f] + λ ‖f‖²_H` (Prop. 1 iv)). -/
noncomputable def regRisk (ρ : Measure (X × Y)) (lam : ℝ) (f : H) : ℝ :=
  risk ρ f + lam * ‖f‖ ^ 2

/-- The regularized empirical risk of (18), `(1/ℓ) ∑_{i} ‖f(x_i) − y_i‖² + λ ‖f‖²_H`, for a
training set `z = ((x_1, y_1), …, (x_ℓ, y_ℓ))`. -/
noncomputable def regEmpRisk {ℓ : ℕ} (lam : ℝ) (z : Fin ℓ → X × Y) (f : H) : ℝ :=
  (1 / (ℓ : ℝ)) * ∑ i, ‖f (z i).1 - (z i).2‖ ^ 2 + lam * ‖f‖ ^ 2

/-- `f` solves the minimization problem (18): `f = f_z^λ`, the RLS estimator. -/
def IsRLSMin {ℓ : ℕ} (lam : ℝ) (z : Fin ℓ → X × Y) (f : H) : Prop :=
  ∀ g : H, regEmpRisk lam z f ≤ regEmpRisk lam z g

/-- The effective dimension `N(λ) = Tr[(T + λ)^{−1} T] = ∑_i t_i/(t_i + λ)` (p. 13), computed in an
eigen-system of `T`. Under Hypothesis 1 the series is summable, since `∑ t_i = Tr T ≤ κ`. -/
noncomputable def effDim {ι : Type*} (t : ι → ℝ) (lam : ℝ) : ℝ :=
  ∑' i, t i / (t i + lam)

/-- The regularization parameter `λ_ℓ` of (19), branches `b < +∞`: `(1/ℓ)^{b/(bc+1)}` if `c > 1`,
`(log ℓ / ℓ)^{b/(b+1)}` if `c = 1` (with `1 ≤ c ≤ 2` the `else` branch is `c = 1`). -/
noncomputable def lamSeq (b c : ℝ) (ℓ : ℕ) : ℝ :=
  if 1 < c then (1 / (ℓ : ℝ)) ^ (b / (b * c + 1)) else (Real.log ℓ / ℓ) ^ (b / (b + 1))

/-- The rate `a_ℓ` of (20), branches `b < +∞`: `(1/ℓ)^{bc/(bc+1)}` if `c > 1`,
`(log ℓ / ℓ)^{b/(b+1)}` if `c = 1`. -/
noncomputable def aSeq (b c : ℝ) (ℓ : ℕ) : ℝ :=
  if 1 < c then (1 / (ℓ : ℝ)) ^ (b * c / (b * c + 1)) else (Real.log ℓ / ℓ) ^ (b / (b + 1))

end OptimalRLS.Upper


