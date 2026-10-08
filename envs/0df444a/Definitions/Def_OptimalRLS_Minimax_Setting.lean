-- Prove2me | Definitions.Def_OptimalRLS_Minimax_Setting
-- name    : OptimalRLS_Minimax_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T19:08:07.421367+00:00
-- url     : https://prove2.me/theorems/8011db59-cdbf-4c82-99f0-6b8da3d63458
-- title:
--   §3, pp. 6–10 and Prop. 4, p. 21 — Hypotheses 1–2, the risk, the covariance form and eigen-system of T, T^s, the prior P(b, c), and the model ρ_f
-- statement:
--   This definition file fixes the setting of Caponnetto and De Vito's analysis of regularized least squares, in the form used for the minimax lower rate (§5.3).
--
--   **Spaces.** The input space $X$ is Polish with its Borel $\sigma$-algebra, the output space $Y$ is a real separable Hilbert space, and $\mathcal H$ is a real separable Hilbert space of functions $f : X \to Y$ in which evaluation at each point is continuous. For $x \in X$ let $K_x : Y \to \mathcal H$ be the adjoint of evaluation at $x$, so that $f(x) = K_x^* f$ for all $f \in \mathcal H$ (equation (4)).
--
--   1. **Hypothesis 1** (p. 6), with constant $\kappa$ and a fixed Hilbert basis $(v_j)$ of $Y$: the map $(x,t) \mapsto \langle K_t a, K_x b\rangle_{\mathcal H}$ is measurable on $X \times X$ for all $a, b \in Y$ (equation (5)); $\kappa > 0$; and for every $x$ the operator $K_x$ is Hilbert–Schmidt with
--   $$\operatorname{Tr}(K_x^* K_x) = \sum_j \|K_x v_j\|_{\mathcal H}^2 \le \kappa .$$
--   2. **Risk.** For a probability measure $\rho$ on $Z = X \times Y$, $\mathcal E[f] = \int_Z \|f(x) - y\|_Y^2 \, d\rho(x,y)$.
--   3. **Hypothesis 2** (p. 7), with positive constants $M, \Sigma$ and a function $f_{\mathcal H} \in \mathcal H$: $\int \|y\|^2\,d\rho < \infty$ (7); $f_{\mathcal H}$ minimizes $\mathcal E$ over $\mathcal H$ (8); and for $\rho_X$-almost every $x$,
--   $$\int_Y \Big(e^{\|y - f_{\mathcal H}(x)\|/M} - \frac{\|y - f_{\mathcal H}(x)\|}{M} - 1\Big)\, d\rho(y\mid x) \le \frac{\Sigma^2}{2M^2} \qquad (9),$$
--   where $\rho_X$ is the marginal of $\rho$ on $X$ and $\rho(\cdot\mid x)$ its conditional distribution.
--   4. **The minimal-norm minimizer.** $f_{\mathcal H}$ is the minimizer of $\mathcal E$ of smallest norm (p. 9).
--   5. **The operator $T$** (12)–(16). For a probability measure $\nu$ on $X$ the operator $T = \int_X K_x K_x^*\, d\nu(x)$ is recorded through its quadratic form $\langle Tf, g\rangle_{\mathcal H} = \int_X \langle f(x), g(x)\rangle_Y\, d\nu(x)$, so that $\|\sqrt T h\|_{\mathcal H}^2 = \int_X \|h(x)\|_Y^2\,d\nu(x)$. An eigen-system of $T$ is an orthonormal family $(e_n)$ in $\mathcal H$ with positive numbers $(t_n)$ such that $\langle Tf, g\rangle = \sum_n t_n \langle f, e_n\rangle\langle g, e_n\rangle$ for all $f, g$, i.e. $T = \sum_n t_n \langle \cdot, e_n\rangle e_n$ (16). The power $T^s$ ($s \ge 0$) acts as $T^s g = \sum_n t_n^s \langle g, e_n\rangle e_n$.
--   6. **The prior $\mathcal P(b,c)$** (Definition 1, pp. 9–10, case $1 < b < +\infty$): $\rho \in \mathcal P(b,c)$ if $\rho$ is a probability measure on $Z$, Hypothesis 2 holds with $M, \Sigma$ for the minimal-norm minimizer $f_{\mathcal H}$, the operator $T$ of $\rho_X$ has infinitely many positive eigenvalues $t_1 \ge t_2 \ge \dots$ with
--   $$\alpha \le n^b t_n \le \beta \qquad (n \ge 1) \qquad (17),$$
--   and $f_{\mathcal H} = T^{(c-1)/2} g$ for some $g \in \mathcal H$ with $\|g\|_{\mathcal H}^2 \le R$.
--   7. **The model $\rho_f$ of Proposition 4** (p. 21). Let $\dim Y = d$, let $(v_j)_{j=1}^d$ be an orthonormal basis of $Y$, $L > 0$ and $f \in \mathcal H$. Then $\rho_f(x,y) = \nu(x)\rho_f(y\mid x)$ with
--   $$\rho_f(y\mid x) = \frac{1}{2dL} \sum_{j=1}^d \Big( (L - \langle f(x), v_j\rangle_Y)\, \delta_{-dLv_j} + (L + \langle f(x), v_j\rangle_Y)\, \delta_{+dLv_j} \Big),$$
--   and the constant used in the paper is $L = 4\sqrt{\kappa^c R}$.
--
--   These objects are shared by every statement of the mission: the goal (Theorem 2) is a statement about $\mathcal P(b,c)$ and the risk, and the milestones (Propositions 4–6, Theorem 5) use $T$, its eigen-system and $\rho_f$.
--
--   **Formalization Note.** The paper's $\Sigma$ is written `Sig`. The operator $T$ is never formed as an operator-valued Bochner integral: it enters through its quadratic form `covForm` and an eigen-system (`IsEigenSystem`, with a summability guard), and the eigen-system is indexed by $\mathbb N$ starting at $0$, so the paper's $t_n, e_n$ ($n \ge 1$) are `t (n-1)`, `e (n-1)`. The trace in (6) is a series over a fixed Hilbert basis of $Y$ (it does not depend on the basis). The conditional distribution in (9) is Mathlib's `Measure.condKernel`, and the integral in (9) is a `lintegral` of a nonnegative integrand. $T^0$ is the orthogonal projection onto $(\ker T)^\perp$; since the minimal-norm $f_{\mathcal H}$ is orthogonal to $\ker T$ this gives the same class as the identity. In $\rho_f$ the inner product $\langle f, K_x v_j\rangle_{\mathcal H}$ of the paper is written $\langle f(x), v_j\rangle_Y$, equal by (4); the paper's $\delta_{y+dLv_j}$ is the Dirac mass at $-dLv_j$. Negative weights would be clipped to $0$, but under the hypotheses of Proposition 4 they are nonnegative by (55). The basis $(v_j)$ is taken orthonormal (the paper says "a basis"; its computation of the regression function needs orthonormality).
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, §3, Hypothesis 1 (p. 6), Hypothesis 2 (p. 7), (12)–(16) (p. 9), Definition 1 (pp. 9–10); §5.3, (52) and Proposition 4 (p. 21)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace OptimalRLS.Minimax

/-! # The setting of Caponnetto & De Vito (2007), §3, for the minimax lower rate (§5.3)

Caponnetto & De Vito, *Optimal rates for the regularized least-squares algorithm*, Found. Comput.
Math. 7 (2007), authors' copy, §3 (pp. 6–10) and §5.3 (pp. 20–21).

Notation: the paper's `Σ` is written `Sig` and its `λ` is never used here (both are reserved in
Lean 4). `X` is the input space, `Y` the output space, `H` the hypothesis space of functions
`X → Y` (Mathlib's `RKHS ℝ H X Y`); `RKHS.kerFun H x : Y →L[ℝ] H` is the paper's `K_x`, and
`RKHS.adjoint_kerFun` is the reproducing property (4), `f(x) = K_x^* f`.

Hypothesis 1, p. 6 (verbatim):
"Hypothesis 1. The space H is a separable Hilbert space of functions f : X → Y such that
– for all x ∈ X there is a Hilbert-Schmidt operator K_x : Y → H satisfying
(4)   f(x) = K_x^* f   f ∈ H,
where K_x^* : H → Y is the adjoint of K_x;
– the real function from X × X to R
(5)   (x, t) ↦ ⟨K_t v, K_x w⟩_H is measurable ∀ v, w ∈ Y;
– there is κ > 0 such that
(6)   Tr(K_x^* K_x) ≤ κ   ∀ x ∈ X."

Hypothesis 2, p. 7 (verbatim):
"Hypothesis 2. The probability measure ρ on Z satisfies the following properties
(7)   ∫_Z ‖y‖²_Y dρ(x, y) < +∞,
– there exists f_H ∈ H such that
(8)   E[f_H] = inf_{f∈H} E[f],
where E[f] = ∫_Z ‖f(x) − y‖²_Y dρ(x, y);
– there are two positive constants Σ, M such that
(9)   ∫_Y ( e^{‖y−f_H(x)‖_Y / M} − ‖y − f_H(x)‖_Y / M − 1 ) dρ(y|x) ≤ Σ²/(2M²)
for ρ_X-almost all x ∈ X."

Definition 1, pp. 9–10 (verbatim):
"Definition 1. Let us fix the positive constants M, Σ, R, α and β.
Then, given 1 < b ≤ +∞ and 1 ≤ c ≤ 2, we define P = P(b, c) the set of probability distributions
ρ on Z such that
i) Hypotheses 2 holds with the given choice for M and Σ in (9);
ii) there is g ∈ H such that f_H = T^{(c−1)/2} g with ‖g‖²_H ≤ R;
iii) if b < +∞, then N = +∞ and the eigenvalues of T given by (16) satisfy
(17)   α ≤ n^b t_n ≤ β   ∀ n ≥ 1,
whereas if b = +∞, then N ≤ β < +∞."

§5.3, p. 20 (verbatim): "We assume now that Y is finite dimensional with d = dim Y and N = +∞, we
fix 1 < b < +∞, 1 ≤ c ≤ 2 and M, Σ, R, α, β as in the definition of P(b, c)."
-/

/-- **Hypothesis 1** (p. 6), the clauses beyond "H is a Hilbert space of functions with continuous
evaluation" (which is the class `RKHS ℝ H X Y`; the reproducing property (4) is
`RKHS.adjoint_kerFun`):
* (5): for all `a b : Y`, `(x, t) ↦ ⟪K_t a, K_x b⟫_H` is measurable on `X × X`;
* `0 < κ`, and (6) with Hilbert–Schmidt-ness: for every `x`, `Tr(K_x^* K_x) = ∑ⱼ ‖K_x vⱼ‖²` is a
  convergent series bounded by `κ`, computed in a fixed Hilbert basis `v` of `Y` (the trace does not
  depend on the basis, footnote 4, p. 6). -/
def Hyp1 (H : Type*) {X Y : Type*} [MeasurableSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [CompleteSpace Y] [RKHS ℝ H X Y] {ι : Type*} (κ : ℝ) (v : HilbertBasis ι ℝ Y) : Prop :=
  (∀ a b : Y, Measurable fun p : X × X => ⟪RKHS.kerFun H p.2 a, RKHS.kerFun H p.1 b⟫_ℝ) ∧
  0 < κ ∧
  ∀ x : X, Summable (fun j => ‖RKHS.kerFun H x (v j)‖ ^ 2) ∧
    ∑' j, ‖RKHS.kerFun H x (v j)‖ ^ 2 ≤ κ

/-- The **expected risk** `E[f] = ∫_Z ‖f(x) − y‖²_Y dρ(x, y)` (p. 4 and Hypothesis 2, p. 7). It is a
Bochner integral; every statement using it assumes (7) (through `Hyp2`/`InPrior`) and bounded or
square-integrable `f`, so it is not a junk value. -/
noncomputable def risk {X Y H : Type*} [MeasurableSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [MeasurableSpace Y] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [RKHS ℝ H X Y]
    (ρ : Measure (X × Y)) (f : H) : ℝ :=
  ∫ p, ‖f p.1 - p.2‖ ^ 2 ∂ρ

/-- **Hypothesis 2** (p. 7) with the constants `M`, `Sig` (the paper's `M`, `Σ`) and the minimizer
`fH`:
* `M` and `Σ` are positive;
* (7): `‖y‖²` is `ρ`-integrable;
* (8): `fH` minimizes the risk over `H`;
* (9): for `ρ_X`-almost every `x`, `∫ (e^{‖y − f_H(x)‖/M} − ‖y − f_H(x)‖/M − 1) dρ(y|x) ≤ Σ²/(2M²)`,
  with `ρ_X = ρ.fst` and `ρ(·|x) = ρ.condKernel x` (it exists since `Z` is Polish, p. 6). The
  integrand is nonnegative, so the integral is a `lintegral` (no junk value). -/
def Hyp2 {X Y H : Type*} [MeasurableSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [MeasurableSpace Y] [StandardBorelSpace Y] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [RKHS ℝ H X Y] (M Sig : ℝ) (ρ : Measure (X × Y)) [IsFiniteMeasure ρ] (fH : H) : Prop :=
  0 < M ∧ 0 < Sig ∧
  Integrable (fun p : X × Y => ‖p.2‖ ^ 2) ρ ∧
  (∀ f : H, risk ρ fH ≤ risk ρ f) ∧
  ∀ᵐ x ∂ρ.fst,
    ∫⁻ y, ENNReal.ofReal (Real.exp (‖y - fH x‖ / M) - ‖y - fH x‖ / M - 1) ∂(ρ.condKernel x)
      ≤ ENNReal.ofReal (Sig ^ 2 / (2 * M ^ 2))

/-- `fH` is **the** `f_H` of the paper: a minimizer of the risk of minimal norm among all minimizers
(p. 9, "we recover uniqueness by choosing the one with minimal norm in H"). -/
def IsMinNormMinimizer {X Y H : Type*} [MeasurableSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [MeasurableSpace Y] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [RKHS ℝ H X Y] (ρ : Measure (X × Y)) (fH : H) : Prop :=
  (∀ f : H, risk ρ fH ≤ risk ρ f) ∧ ∀ f : H, (∀ g : H, risk ρ f ≤ risk ρ g) → ‖fH‖ ≤ ‖f‖

/-- The **quadratic form of the operator `T`** of (12)–(14), p. 9: `covForm ν f g = ∫ ⟨f(x), g(x)⟩_Y dν(x)`,
which equals `⟨T f, g⟩_H` by (29) when `ν = ρ_X`. In particular `‖√T h‖²_H = covForm ν h h`.
The operator `T = ∫ T_x dρ_X(x)` is never built as an operator-valued Bochner integral. -/
noncomputable def covForm {X Y H : Type*} [MeasurableSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [RKHS ℝ H X Y] (ν : Measure X) (f g : H) : ℝ :=
  ∫ x, ⟪f x, g x⟫_ℝ ∂ν

/-- An **eigen-system of `T`** realizing the spectral decomposition (16), p. 9 (and (52), p. 21):
`(e i)` is an orthonormal family in `H`, the `t i` are positive, and
`⟨T f, g⟩_H = ∑ᵢ tᵢ ⟨f, eᵢ⟩⟨g, eᵢ⟩` for all `f, g`, i.e. `T = ∑ᵢ tᵢ ⟨·, eᵢ⟩ eᵢ`. Then `(eᵢ)` is an
orthonormal basis of `(ker T)^⊥` and the `tᵢ` are the nonzero eigenvalues of `T`. The `Summable`
clause guards against a divergent `tsum` being read as `0`. -/
def IsEigenSystem {X Y H : Type*} [MeasurableSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [RKHS ℝ H X Y]
    {ι : Type*} (ν : Measure X) (e : ι → H) (t : ι → ℝ) : Prop :=
  Orthonormal ℝ e ∧ (∀ i, 0 < t i) ∧ (∀ f : H, Summable fun i => t i * ⟪f, e i⟫_ℝ ^ 2) ∧
    ∀ f g : H, covForm ν f g = ∑' i, t i * ⟪f, e i⟫_ℝ * ⟪g, e i⟫_ℝ

/-- The **power `T^s`** (`s ≥ 0`) computed in an eigen-system `(e, t)` indexed by `ℕ` (the case
`N = +∞`): `T^s g = ∑ₙ tₙ^s ⟨g, eₙ⟩ eₙ`. On `(ker T)^⊥` this is `T^s`; for `s = 0` it is the orthogonal
projection onto `(ker T)^⊥`. For the minimal-norm `f_H`, which is orthogonal to `ker T`, the source
condition `f_H = T^0 g` reads the same with the identity or with this projection. The paper's
eigenvalue `tₙ`, eigenvector `eₙ` (`n ≥ 1`) are `t (n - 1)`, `e (n - 1)` here. -/
noncomputable def Tpow {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (e : ℕ → H) (t : ℕ → ℝ) (s : ℝ) (g : H) : H :=
  ∑' n, ((t n) ^ s * ⟪g, e n⟫_ℝ) • e n

/-- **Definition 1** (pp. 9–10), branch `1 < b < +∞` (so `N = +∞`): `ρ ∈ P(b, c)` for the constants
`M, Σ (Sig), R, α, β`:
* `ρ` is a probability measure on `Z = X × Y`;
* i) Hypothesis 2 holds with `M`, `Σ`, for `f_H` the minimal-norm minimizer of the risk;
* iii) `T` (built from `ρ_X = ρ.fst`) has an eigen-system `(eₙ, tₙ)` indexed by `ℕ` (`N = +∞`), with the
  eigenvalues in decreasing order and (17) `α ≤ nᵇ tₙ ≤ β` for all `n ≥ 1`, written with the index
  shift `n ↦ n + 1` as `α ≤ (n + 1)ᵇ t n ≤ β` for `n : ℕ`;
* ii) `f_H = T^{(c−1)/2} g` for some `g ∈ H` with `‖g‖² ≤ R`.
The positivity of the constants and `1 < b`, `1 ≤ c ≤ 2` are hypotheses of the theorems. -/
def InPrior (H : Type*) {X Y : Type*} [MeasurableSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [MeasurableSpace Y] [StandardBorelSpace Y] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [RKHS ℝ H X Y] (M Sig R α β b c : ℝ) (ρ : Measure (X × Y))
    [IsProbabilityMeasure ρ] : Prop :=
  ∃ fH : H, IsMinNormMinimizer ρ fH ∧ Hyp2 M Sig ρ fH ∧
    ∃ (e : ℕ → H) (t : ℕ → ℝ), IsEigenSystem ρ.fst e t ∧ Antitone t ∧
      (∀ n : ℕ, α ≤ ((n : ℝ) + 1) ^ b * t n ∧ ((n : ℝ) + 1) ^ b * t n ≤ β) ∧
      ∃ g : H, fH = Tpow e t ((c - 1) / 2) g ∧ ‖g‖ ^ 2 ≤ R

/-- The constant `L = 4 √(κ^c R)` of Proposition 4, p. 21. -/
noncomputable def Lconst (κ c R : ℝ) : ℝ :=
  4 * Real.sqrt (κ ^ c * R)

/-- The distribution `ρ_f` of **Proposition 4**, p. 21: `ρ_f(x, y) = ν(x) ρ_f(y|x)` with
`ρ_f(y|x) = (1/(2dL)) ∑ⱼ ((L − ⟨f, K_x vⱼ⟩) δ_{−dLvⱼ} + (L + ⟨f, K_x vⱼ⟩) δ_{+dLvⱼ})`,
where `(vⱼ)ⱼ₌₁^d` is an orthonormal basis of `Y` and `L` is the argument `Lc`. The paper writes the
Dirac measures as `δ_{y+dLvⱼ}`, `δ_{y−dLvⱼ}`, "the Dirac measure on Y at point ∓dLvⱼ": the weight
`L − ⟨f, K_x vⱼ⟩` sits at `−dLvⱼ`. By (4), `⟨f, K_x vⱼ⟩_H = ⟨f(x), vⱼ⟩_Y`, which is what is written.

Each summand is `ν` weighted by a density and pushed forward by `x ↦ (x, ±dLvⱼ)`. `ENNReal.ofReal`
clips negative weights to `0`; under the hypotheses of Proposition 4, `|⟨f(x), vⱼ⟩| ≤ L/4` by (55),
so no weight is negative and nothing is clipped. -/
noncomputable def rhoF {X Y H : Type*} [MeasurableSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [MeasurableSpace Y] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [RKHS ℝ H X Y] {d : ℕ} (ν : Measure X) (vb : OrthonormalBasis (Fin d) ℝ Y) (Lc : ℝ) (f : H) :
    Measure (X × Y) :=
  ∑ j : Fin d,
    ((ν.withDensity fun x => ENNReal.ofReal ((Lc - ⟪f x, vb j⟫_ℝ) / (2 * d * Lc))).map
        (fun x => (x, -((d : ℝ) * Lc) • vb j)) +
      (ν.withDensity fun x => ENNReal.ofReal ((Lc + ⟪f x, vb j⟫_ℝ) / (2 * d * Lc))).map
        (fun x => (x, ((d : ℝ) * Lc) • vb j)))

end OptimalRLS.Minimax


