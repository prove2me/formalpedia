-- Prove2me | Definitions.Def_TaoBR
-- name    : TaoBR
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T17:04:05.310802+00:00
-- url     : https://prove2.me/theorems/2c4acdba-cf5d-4a52-96db-c1b988ddb739
-- title:
--   Bochner–Riesz, restriction, local smoothing, Kakeya and Nikodym (Tao 1999)
-- statement:
--   The objects of Tao's paper, on $\mathbf R^n$ = `EuclideanSpace ℝ (Fin n)`. Throughout, the Fourier transform is Mathlib's $\hat f(\xi) = \int e^{-2\pi i \langle x, \xi\rangle} f(x)\,dx$, the normalization of the paper's oscillatory integrals (p. 3). Exponents $p$ range over $[1, \infty]$. Footnote 1 on p. 1: "All of the estimates in this paper will be *a priori*, in the sense that all functions are assumed to be Schwarz class." The estimates below quantify over Schwartz functions accordingly.
--
--   **Bochner–Riesz.** p. 1: "Fix $n \ge 2$. For any $1 \le p \le \infty$ and $\alpha \ge 0$ we use $BR(p, \alpha)$ to denote the statement that $S^{\delta(p)+\alpha}$ is bounded on $L^p$, where $\delta(p) = \max(n|\frac1p - \frac12| - \frac12, 0)$ and $S^\delta$ is the Bochner-Riesz multiplier $\widehat{S^\delta f}(\xi) = (1 - |\xi|^2)_+^\delta\hat f(\xi)$." And: "The Bochner-Riesz conjecture is the statement that $BR(p, \varepsilon)$ holds for all $1 \le p \le \infty$ and $\varepsilon > 0$."
--   - `bochnerRiesz δ` is $S^\delta$, the Fourier multiplier (`multiplier`) with symbol $(1 - |\xi|^2)_+^\delta$ (`brSymbol`). Here $t_+^\delta$ (`plusPow`) is $t^\delta$ for $t > 0$ and $0$ for $t \le 0$, also at $\delta = 0$, so $S^0$ is the multiplier with symbol the indicator of the open unit ball.
--   - `critIndex n p` is $\delta(p)$. `BR n p α` says that some $C$ has $\|S^{\delta(p)+\alpha} f\|_p \le C\|f\|_p$ for every Schwartz $f$. `BochnerRieszConjecture n` is the conjecture.
--   - `bochnerRieszDil δ R` is the operator of Conjecture 4.2, p. 8: "For $R, \delta > 0$ define the operators $S^\delta_R$ by $\widehat{S^\delta_R f}(\xi) = (1 - |\frac{\xi}{R}|^2)_+^\delta\hat f(\xi)$."
--
--   **Restriction.** p. 1: "Similarly, we use $R(p, \alpha)$ to denote the localized restriction estimate $\|\Re f\|_{L^p(S^{n-1})} \lesssim R^\alpha\|f\|_{L^p(B(0,R))}$ for $f$ supported in $B(0, R)$, where $\Re f = \hat f|_{S^{n-1}}$ is the sphere restriction operator." And: "The restriction conjecture asserts that $R(p, 0)$ holds for all $1 \le p < 2n/(n+1)$."
--   - `restriction f` is $\Re f$ on the unit sphere, which carries `sphereMeasure n`, surface measure (Mathlib's `MeasureTheory.Measure.toSphere` of Lebesgue measure).
--   - `Restr n p α` is $R(p, \alpha)$: one $C$ with $\|\Re f\|_{L^p(S^{n-1})} \le C R^\alpha\|f\|_{L^p(\overline B(0,R))}$ for every $R \ge 1$ and every Schwartz $f$ supported in $\overline B(0, R)$. The paper does not say which radii $R$ it means; the estimate is about large balls (it is used for $R \gg 1$ on pp. 3–5), read here as $R \ge 1$.
--   - `RestrictionConjecture n` is the conjecture. `conjExp p` is the conjugate exponent $p' = (1 - 1/p)^{-1}$, with $1' = \infty$ and $\infty' = 1$.
--
--   **Operators with kernels.** `kernelOp K` is $f \mapsto \int K(x, y)f(y)\,dy$, and `opNorm p q T` is the least $C \in [0, \infty]$ with $\|Tf\|_q \le C\|f\|_p$ for every $f \in L^p$.
--   - p. 3: "$G_R f(x) = \int e^{2\pi iR|x-y|}\psi(x, y)f(y)\,dy$, and $\psi(x, y)$ is a bump function supported on the set $|x|, |y| \lesssim 1, |x - y| \sim 1$." `carlesonSjolinOp ψ R` is $G_R$, for a real-valued $\psi$.
--   - p. 9: "suppose $S_R f(x) = \int e^{-2\pi iR\phi(x,y)}\psi(x, y)f(y)\,dy$, is a family of oscillatory integrals, where the amplitude $\psi$ is smooth and compactly supported in $\mathbf R^n \times \mathbf R^m$, where $m - 1 \le n \le m$, and $\phi$ is a phase function of constant rank $m - 1$ in the sense of Hörmander [15]." `oscillatoryOp φ ψ R` is $S_R$, with a real phase $\varphi$ and a complex amplitude $\psi$.
--   - "Then for each point $y_0$ in the domain of $y$ one can associate a Fourier restriction operator $\Re_{y_0}$ associated to the linearization of the $S_R$ at $y_0$: $\Re_{y_0}f(x) = \psi(x, y_0)\hat f(\nabla_y\phi(x, y_0))$." `linearizedRestriction φ ψ y₀` is $\Re_{y_0}$.
--   - `HasConstantRank φ ψ r` says that the mixed Hessian $\partial^2\varphi/\partial x\,\partial y$ (`mixedHessian`) has rank $r$ at every point of the support of $\psi$. This is the reading taken of "constant rank in the sense of Hörmander [15]": Hörmander's rank condition (3.1) (Ark. Mat. 11 (1973), §3), without Hörmander's curvature condition (3.2).
--
--   **Sparse balls and cubes (§3).** Definition 3.1, p. 5: "A collection $\{B(x_i, R)\}_{i=1}^N$ of $R$-balls is *sparse* if the centers $x_i$ are $R^CN^C$ seperated. ($C$ denotes a constant that will change from line to line)." `IsSparse C R x` makes $C$ a parameter: distinct centres are at distance at least $R^CN^C$. p. 7: "where $\chi$ is the characteristic function of the cube of size $c$, and $c \sim 1$ is chosen so that $\hat\chi$ is positive on the unit sphere. Combining the two reductions we see that it suffices to verify the original estimate (3) when $f$ is constant on $c$-cubes." There $f$ is a measure on the lattice $\mathbf Z^n$ convolved with $\chi$, so the $c$-cubes are the cubes of side $c$ centred at the points of $\mathbf Z^n$. `cCube c k` is $k + [-c/2, c/2]^n$ for $k \in \mathbf Z^n$, and `IsCubeUnion c S` says that $S$ is a finite union of them.
--
--   **Local smoothing (Conjecture 4.1).** p. 8: "If $u(x, t)$ is a solution of the homogeneous Cauchy problem $(-\frac{\partial^2}{\partial t^2} + \Delta)u(x, t) = 0$, $u(x, 0) = f(x)$, $u_t(x, 0) = 0$, then one has $\|u\|_{L^p(\mathbf R^n\times[1,2])} \lesssim \|(1 + \sqrt{-\Delta})^\varepsilon f\|_p$ for all $\varepsilon > 0$, where $p = 2n/(n-1)$ and $\Delta$ is the Laplacian." `waveSolution f` is the solution given by $\hat u(\xi, t) = \cos(2\pi t|\xi|)\hat f(\xi)$, and `besselOp ε` is $(1 + \sqrt{-\Delta})^\varepsilon$, the multiplier $(1 + 2\pi|\xi|)^\varepsilon$; with this Fourier normalization, $\sqrt{-\Delta}$ is the multiplier $2\pi|\xi|$. `LocalSmoothingConjecture n` is the estimate for every $\varepsilon > 0$ and Schwartz $f$.
--
--   **Maximal Bochner–Riesz (Conjecture 4.2).** p. 8: "Then for all $2 \le p \le \infty$ and $\delta > \delta(p)$, one has the estimate $\|\sup_{R>0}S^\delta_R f\|_p \lesssim \|f\|_p$." `MaximalBochnerRieszConjecture n` takes the supremum of $|S^\delta_R f|$, since $S^\delta_R f$ is complex-valued.
--
--   **Paraboloids (Conjectures 4.3, 4.4).** Here $\mathbf R^n = \mathbf R^{n-1} \times \mathbf R$, written with $m = n - 1$.
--   - p. 8, Conjecture 4.3: "For $\delta > 0$ define the operators $\tilde S^\delta$ by $\widehat{\tilde S^\delta_R f}(\underline\xi, \xi_n) = \eta(\xi)(\xi_n - \frac12|\underline\xi|^2)_+^\delta\hat f(\underline\xi, \xi_n)$, for $(\underline\xi, \xi_n) \in \mathbf R^{n-1} \times \mathbf R$, where $\eta$ is smooth and compactly supported." `horiz ξ` is $\underline\xi$, `vert ξ` is $\xi_n$, `mkPoint` puts them together, and `parabolicBochnerRiesz η δ` is $\tilde S^\delta$ for a real-valued $\eta$. `ParabolicBochnerRieszConjecture m` is the conjecture, for every smooth compactly supported $\eta$.
--   - p. 8, Conjecture 4.4: "Let $S = \{(\underline\xi, \frac12|\underline\xi|^2) : |\underline\xi| \lesssim 1\}$ be a subset of the standard paraboloid. Then for all $1 \le p < 2n/(n-1)$ we have $\|\hat f|_S\|_{L^p(S)} \lesssim \|f\|_p$." `paraboloidRestriction f` is $\underline\xi \mapsto \hat f(\underline\xi, \frac12|\underline\xi|^2)$ on $|\underline\xi| \le 1$, with the measure $d\underline\xi$ of the parametrization in place of surface measure on $S$.
--   - `ParabolicRestrictionConjecture m` takes the range $1 \le p < 2n/(n+1)$. With the printed range the conjecture is false ([`TaoBR.not_parabolicRestriction_printed`](https://prove2.me/theorems/517d7ce2-e6a8-4a1a-83a7-c900c57c57bb)), and the critical exponent of the paraboloid is the sphere's, $2n/(n+1)$, as the paper says on p. 10. The range is corrected under the standing rule for typographical errors.
--
--   **Kakeya and Nikodym (Conjectures 4.5–4.8).**
--   - p. 9, Conjecture 4.5: "If $f$ is a compactly supported function and $0 < \delta \ll 1$, we define the Kakeya maximal function $f^*_\delta$ on $S^{n-1}$ by $f^*_\delta(\omega) = \sup_{T/\!/\omega}\frac{1}{|T|}\int_T f(x)\,dx$, where the supremum is taken over all $1 \times \delta$ tubes $T$ which are oriented in the direction $\omega$."
--     - `tube δ ω c` is the solid cylinder of length $1$ and radius $\delta$ around the segment $c + [-\frac12, \frac12]\omega$.
--     - `kakeyaMaximal δ f` is $f^*_\delta$ for real-valued $f$.
--     - p. 9: "Let $K(p, \alpha)$ denote the estimate $\|f^*_\delta\|_p \lesssim \delta^{\frac np - 1 - \alpha}\|f\|_p$." `KakeyaMaximalEstimate n p α` is $K(p, \alpha)$: there are $C$ and $\delta_0 > 0$ with $\|f^*_\delta\|_{L^p(S^{n-1})} \le C\delta^{1 - n/p - \alpha}\|f\|_p$ for all $0 < \delta < \delta_0$ and all compactly supported Schwartz $f$; $\delta_0$ is the paper's "$0 < \delta \ll 1$".
--     - The paper prints the exponent $n/p - 1 - \alpha$, which is false for $p < n$ ([`TaoBR.not_kakeyaMaximalConjecture_printed`](https://prove2.me/theorems/47c2bf78-a61b-4157-8fce-ca52e70dcea7)). The exponent $1 - n/p - \alpha$ agrees with it at $p = n$. `KakeyaMaximalConjecture n` is $K(p, \alpha)$ for all $1 \le p \le n$ and $\alpha > 0$.
--   - p. 9, Conjecture 4.7: "If $f$ is a compactly supported function and $0 < \delta \ll 1$, we define the Kakeya maximal function $f^*_\delta$ on $\mathbf R^n$ by $f^*_\delta(x) = \sup_{x \in T}\frac{1}{|T|}\int_T f(y)\,dy$, where the supremum is taken over all $1 \times \delta$ tubes $T$ which contain $x$."
--     - The estimate then writes $f^{**}_\delta$, and `nikodymMaximal δ f` is this Nikodym maximal function under that name.
--     - "Let $N(p, \alpha)$ denote the estimate $\|f^{**}_\delta\|_p \lesssim \delta^{\frac np - 1 - \alpha}\|f\|_p$" `NikodymMaximalEstimate n p α` is $N(p, \alpha)$, the same bound for $\|f^{**}_\delta\|_{L^p(\mathbf R^n)}$, with the same exponent correction ([`TaoBR.not_nikodymMaximalConjecture_printed`](https://prove2.me/theorems/a2964169-1028-42ca-9272-4ea427982fe7)). `NikodymMaximalConjecture n` is the conjecture.
--   - p. 9, Conjecture 4.6: "Define a Kakeya set to be any subset $E$ of $\mathbf R^n$ which contains a unit line segment in each direction." This is `FCP.Kakeya.IsKakeya` (bundle `FCP_Kakeya`).
--   - Conjecture 4.8: "Define a Nikodym set to be any subset $E$ of $\mathbf R^n$ such that for every $x \in \mathbf R^n$ there exists a line $l$ through $x$ such that $E \cap l$ contains a unit line segment." This is `IsNikodymSet`.
--   - Both conjectures say these sets "have Minkowski dimension $n$".
--     - `coveringNumber A r` is the least number of open $r$-balls covering $A$, and `lowerMinkowskiDim A` and `upperMinkowskiDim A` are $\liminf$ and $\limsup_{r \to 0^+}$ of $\log N(A, r)/\log(1/r)$.
--     - Minkowski dimension is defined through finite covers, which an unbounded set does not have, so `KakeyaSetConjecture n` and `NikodymSetConjecture n` are stated for bounded sets. They state that the lower and upper Minkowski dimensions both equal $n$.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), pp. 1–9, §1 (BR(p, α), R(p, α)), Definition 3.1 and §4 (Conjectures 4.1–4.8)

import Mathlib
import Definitions.Def_FCP_Kakeya

/-!
# Bochner–Riesz, restriction, local smoothing, Kakeya and Nikodym (Tao 1999)

T. Tao, *The Bochner–Riesz conjecture implies the restriction conjecture*, Duke Math. J. 96
(1999) 363–375 (preprint pages). The operators, the estimates `BR(p, α)` and `R(p, α)` of §1,
sparse collections of balls (Definition 3.1), and the objects of the conjectures of §4.

Conventions:
- `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`; the Fourier transform is Mathlib's `𝓕`,
  `𝓕 f ξ = ∫ 𝐞(-⟪x, ξ⟫) f x dx` with `𝐞 t = exp(2πit)`, and `𝓕⁻` is its inverse.
- Exponents `p` live in `[1, ∞]` as elements of `ℝ≥0∞`.
- All estimates are a priori: the functions are Schwartz functions (p. 1, footnote 1).
- `(t)₊^δ` is `t^δ` for `t > 0` and `0` otherwise, also when `δ = 0`.
-/

namespace TaoBR

open MeasureTheory Metric
open scoped FourierTransform ENNReal NNReal SchwartzMap

/-- Euclidean space `ℝⁿ`. -/
abbrev E (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- `t₊^δ`: `t^δ` when `t > 0`, and `0` when `t ≤ 0`, for every `δ ≥ 0` including `δ = 0`. -/
noncomputable def plusPow (δ t : ℝ) : ℝ := if 0 < t then t ^ δ else 0

/-! ## Bochner–Riesz multipliers (p. 1; Conjectures 4.2, 4.3) -/

/-- The Bochner–Riesz symbol `(1 - |ξ|²)₊^δ` of p. 1. -/
noncomputable def brSymbol {n : ℕ} (δ : ℝ) (ξ : E n) : ℝ := plusPow δ (1 - ‖ξ‖ ^ 2)

/-- The Fourier multiplier with symbol `m`: `(m(D) f)^ = m f̂`. -/
noncomputable def multiplier {n : ℕ} (m : E n → ℂ) (f : E n → ℂ) : E n → ℂ :=
  𝓕⁻ (fun ξ => m ξ * 𝓕 f ξ)

/-- The Bochner–Riesz operator `S^δ` of p. 1. -/
noncomputable def bochnerRiesz {n : ℕ} (δ : ℝ) (f : E n → ℂ) : E n → ℂ :=
  multiplier (fun ξ => (brSymbol δ ξ : ℂ)) f

/-- The dilated Bochner–Riesz operator `S_R^δ` of Conjecture 4.2, with symbol
`(1 - |ξ/R|²)₊^δ`. -/
noncomputable def bochnerRieszDil {n : ℕ} (δ R : ℝ) (f : E n → ℂ) : E n → ℂ :=
  multiplier (fun ξ => (brSymbol δ (R⁻¹ • ξ) : ℂ)) f

/-- `δ(p) = max(n|1/p - 1/2| - 1/2, 0)`, p. 1. -/
noncomputable def critIndex (n : ℕ) (p : ℝ≥0∞) : ℝ :=
  max ((n : ℝ) * |p⁻¹.toReal - 1 / 2| - 1 / 2) 0

/-- `BR(p, α)`, p. 1: `S^{δ(p)+α}` is bounded on `Lᵖ`. -/
def BR (n : ℕ) (p : ℝ≥0∞) (α : ℝ) : Prop :=
  ∃ C : ℝ≥0, ∀ f : 𝓢(E n, ℂ),
    eLpNorm (bochnerRiesz (critIndex n p + α) f) p volume ≤ C * eLpNorm f p volume

/-- The Bochner–Riesz conjecture, p. 1: `BR(p, ε)` for all `1 ≤ p ≤ ∞` and `ε > 0`. -/
def BochnerRieszConjecture (n : ℕ) : Prop :=
  ∀ p : ℝ≥0∞, 1 ≤ p → ∀ ε : ℝ, 0 < ε → BR n p ε

/-! ## Restriction to the sphere (p. 1) -/

/-- Surface measure on the unit sphere `S^{n-1}`. -/
noncomputable def sphereMeasure (n : ℕ) : Measure (sphere (0 : E n) 1) :=
  (volume : Measure (E n)).toSphere

/-- The sphere restriction operator `ℜ f = f̂|_{S^{n-1}}`, p. 1. -/
noncomputable def restriction {n : ℕ} (f : E n → ℂ) : sphere (0 : E n) 1 → ℂ :=
  fun ω => 𝓕 f (ω : E n)

/-- `R(p, α)`, p. 1, the localized restriction estimate
`‖ℜ f‖_{Lᵖ(S^{n-1})} ≲ R^α ‖f‖_{Lᵖ(B(0,R))}` for `f` supported in `B(0, R)`, uniformly in `R ≥ 1`. -/
def Restr (n : ℕ) (p : ℝ≥0∞) (α : ℝ) : Prop :=
  ∃ C : ℝ≥0, ∀ R : ℝ, 1 ≤ R → ∀ f : 𝓢(E n, ℂ), tsupport f ⊆ closedBall 0 R →
    eLpNorm (restriction f) p (sphereMeasure n) ≤
      C * ENNReal.ofReal (R ^ α) * eLpNorm f p (volume.restrict (closedBall 0 R))

/-- The restriction conjecture, p. 1: `R(p, 0)` for all `1 ≤ p < 2n/(n+1)`. -/
def RestrictionConjecture (n : ℕ) : Prop :=
  ∀ p : ℝ≥0∞, 1 ≤ p → p < ENNReal.ofReal (2 * n / (n + 1)) → Restr n p 0

/-- The conjugate exponent `p' = (1 - 1/p)⁻¹`, with `1' = ∞` and `∞' = 1`. -/
noncomputable def conjExp (p : ℝ≥0∞) : ℝ≥0∞ := (1 - p⁻¹)⁻¹

/-! ## Operators given by kernels (p. 3, Lemma 2.1, Theorem 4.9) -/

/-- The operator with kernel `K`: `f ↦ (x ↦ ∫ K(x, y) f(y) dy)`. -/
noncomputable def kernelOp {n m : ℕ} (K : E n → E m → ℂ) (f : E m → ℂ) : E n → ℂ :=
  fun x => ∫ y, K x y * f y

/-- The operator norm of `T` from `Lᵖ(ℝᵐ)` to `L^q(ℝⁿ)`: the least `C` with
`‖T f‖_q ≤ C ‖f‖_p` for every `f ∈ Lᵖ`. -/
noncomputable def opNorm {n m : ℕ} (p q : ℝ≥0∞) (T : (E m → ℂ) → (E n → ℂ)) : ℝ≥0∞ :=
  sInf {C : ℝ≥0∞ | ∀ f : E m → ℂ, MemLp f p volume →
    eLpNorm (T f) q volume ≤ C * eLpNorm f p volume}

/-- The operator `G_R f(x) = ∫ e^{2πiR|x-y|} ψ(x, y) f(y) dy` of p. 3. -/
noncomputable def carlesonSjolinOp {n : ℕ} (ψ : E n → E n → ℝ) (R : ℝ) (f : E n → ℂ) :
    E n → ℂ :=
  kernelOp (fun x y => Complex.exp (2 * Real.pi * Complex.I * (R * ‖x - y‖ : ℝ)) * (ψ x y : ℂ)) f

/-- The oscillatory integral `S_R f(x) = ∫ e^{-2πiRφ(x,y)} ψ(x, y) f(y) dy` of p. 9, for
`x ∈ ℝⁿ` and `y ∈ ℝᵐ`. -/
noncomputable def oscillatoryOp {n m : ℕ} (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ) (R : ℝ)
    (f : E m → ℂ) : E n → ℂ :=
  kernelOp (fun x y => Complex.exp (-(2 * Real.pi * Complex.I * (R * φ x y : ℝ))) * ψ x y) f

/-- The Fourier restriction operator `ℜ_{y₀} f(x) = ψ(x, y₀) f̂(∇_y φ(x, y₀))` attached to the
linearization of `S_R` at `y₀` (p. 9). -/
noncomputable def linearizedRestriction {n m : ℕ} (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ)
    (y₀ : E m) (f : E m → ℂ) : E n → ℂ :=
  fun x => ψ x y₀ * 𝓕 f (gradient (fun y => φ x y) y₀)

/-- The mixed Hessian `∂²φ/∂x∂y` at `(x, y)`, as a linear map `ℝⁿ → (ℝᵐ)*`. -/
noncomputable def mixedHessian {n m : ℕ} (φ : E n → E m → ℝ) (x : E n) (y : E m) :
    E n →L[ℝ] (E m →L[ℝ] ℝ) :=
  fderiv ℝ (fun x' => fderiv ℝ (fun y' => φ x' y') y) x

/-- `φ` has constant rank `r` on the support of `ψ`, in the sense of Hörmander: the mixed Hessian
`∂²φ/∂x∂y` has rank `r` at every point of the support of `ψ`. -/
def HasConstantRank {n m : ℕ} (φ : E n → E m → ℝ) (ψ : E n → E m → ℂ) (r : ℕ) : Prop :=
  ∀ x y, (x, y) ∈ tsupport (Function.uncurry ψ) →
    Module.finrank ℝ (LinearMap.range (mixedHessian φ x y).toLinearMap) = r

/-! ## Sparse collections of balls and unions of cubes (§3) -/

/-- Definition 3.1, with the constant `C` made explicit: the `R`-balls centred at
`x 0, …, x (N-1)` form a sparse collection if their centres are `R^C N^C`-separated. -/
def IsSparse {n N : ℕ} (C R : ℝ) (x : Fin N → E n) : Prop :=
  ∀ i j, i ≠ j → R ^ C * (N : ℝ) ^ C ≤ dist (x i) (x j)

/-- The `c`-cube `k + [-c/2, c/2]ⁿ` centred at the lattice point `k ∈ ℤⁿ` (p. 7). -/
def cCube {n : ℕ} (c : ℝ) (k : Fin n → ℤ) : Set (E n) :=
  {x | ∀ i, |x i - k i| ≤ c / 2}

/-- `S` is a finite union of `c`-cubes centred at points of `ℤⁿ` (p. 7). -/
def IsCubeUnion {n : ℕ} (c : ℝ) (S : Set (E n)) : Prop :=
  ∃ s : Finset (Fin n → ℤ), S = ⋃ k ∈ s, cCube c k

/-! ## Local smoothing (Conjecture 4.1) -/

/-- The solution `u(x, t)` of `(-∂²_t + Δ) u = 0`, `u(·, 0) = f`, `u_t(·, 0) = 0`, given by
`û(ξ, t) = cos(2πt|ξ|) f̂(ξ)`. -/
noncomputable def waveSolution {n : ℕ} (f : E n → ℂ) (z : E n × ℝ) : ℂ :=
  multiplier (fun ξ => (Real.cos (2 * Real.pi * z.2 * ‖ξ‖) : ℂ)) f z.1

/-- `(1 + √-Δ)^ε f`, the multiplier `(1 + 2π|ξ|)^ε`. -/
noncomputable def besselOp {n : ℕ} (ε : ℝ) (f : E n → ℂ) : E n → ℂ :=
  multiplier (fun ξ => ((1 + 2 * Real.pi * ‖ξ‖) ^ ε : ℝ)) f

/-- Conjecture 4.1 (local smoothing for the wave equation): for `p = 2n/(n-1)` and every
`ε > 0`, `‖u‖_{Lᵖ(ℝⁿ × [1,2])} ≲ ‖(1 + √-Δ)^ε f‖_p`. -/
def LocalSmoothingConjecture (n : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ f : 𝓢(E n, ℂ),
    eLpNorm (waveSolution f) (ENNReal.ofReal (2 * n / (n - 1)))
        ((volume : Measure (E n)).prod (volume.restrict (Set.Icc (1 : ℝ) 2))) ≤
      C * eLpNorm (besselOp ε f) (ENNReal.ofReal (2 * n / (n - 1))) volume

/-- Conjecture 4.2 (maximal spherical Bochner–Riesz for `p ≥ 2`):
`‖sup_{R>0} |S_R^δ f|‖_p ≲ ‖f‖_p` for all `2 ≤ p ≤ ∞` and `δ > δ(p)`. -/
def MaximalBochnerRieszConjecture (n : ℕ) : Prop :=
  ∀ p : ℝ≥0∞, 2 ≤ p → ∀ δ : ℝ, critIndex n p < δ → ∃ C : ℝ≥0, ∀ f : 𝓢(E n, ℂ),
    eLpNorm (fun x => ⨆ R : Set.Ioi (0 : ℝ), ‖bochnerRieszDil δ R f x‖ₑ) p volume ≤
      C * eLpNorm f p volume

/-! ## Paraboloids (Conjectures 4.3, 4.4); here `ℝⁿ = ℝ^{m} × ℝ` with `n = m + 1` -/

/-- The point `(ξ̲, ξₙ)` of `ℝ^{m+1}` with `ξ̲ ∈ ℝᵐ` and `ξₙ ∈ ℝ`. -/
noncomputable def mkPoint {m : ℕ} (u : E m) (t : ℝ) : E (m + 1) :=
  (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.snoc (fun i => u i) t)

/-- The horizontal part `ξ̲ ∈ ℝᵐ` of `ξ ∈ ℝ^{m+1}`. -/
noncomputable def horiz {m : ℕ} (ξ : E (m + 1)) : E m :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm (fun i => ξ (Fin.castSucc i))

/-- The last coordinate `ξₙ` of `ξ ∈ ℝ^{m+1}`. -/
def vert {m : ℕ} (ξ : E (m + 1)) : ℝ := ξ (Fin.last m)

/-- The parabolic Bochner–Riesz operator `S̃^δ` of Conjecture 4.3, with symbol
`η(ξ)(ξₙ - ½|ξ̲|²)₊^δ`. -/
noncomputable def parabolicBochnerRiesz {m : ℕ} (η : E (m + 1) → ℝ) (δ : ℝ)
    (f : E (m + 1) → ℂ) : E (m + 1) → ℂ :=
  multiplier (fun ξ => (η ξ * plusPow δ (vert ξ - ‖horiz ξ‖ ^ 2 / 2) : ℝ)) f

/-- Conjecture 4.3 (parabolic Bochner–Riesz): for every smooth compactly supported `η`,
`S̃^δ` is bounded on `Lᵖ` whenever `1 ≤ p ≤ ∞` and `δ > δ(p)`. -/
def ParabolicBochnerRieszConjecture (m : ℕ) : Prop :=
  ∀ η : E (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
    ∀ p : ℝ≥0∞, 1 ≤ p → ∀ δ : ℝ, critIndex (m + 1) p < δ → ∃ C : ℝ≥0, ∀ f : 𝓢(E (m + 1), ℂ),
      eLpNorm (parabolicBochnerRiesz η δ f) p volume ≤ C * eLpNorm f p volume

/-- The restriction of `f̂` to the piece `S = {(ξ̲, ½|ξ̲|²) : |ξ̲| ≤ 1}` of the paraboloid,
parametrized by `ξ̲`. -/
noncomputable def paraboloidRestriction {m : ℕ} (f : E (m + 1) → ℂ) (u : E m) : ℂ :=
  𝓕 f (mkPoint u (‖u‖ ^ 2 / 2))

/-- Conjecture 4.4 (parabolic restriction), with the critical exponent `2n/(n+1)`:
`‖f̂|_S‖_{Lᵖ(S)} ≲ ‖f‖_p` for all `1 ≤ p < 2n/(n+1)`, `n = m + 1`; `S` carries the measure `dξ̲`
on `|ξ̲| ≤ 1`. -/
def ParabolicRestrictionConjecture (m : ℕ) : Prop :=
  ∀ p : ℝ≥0∞, 1 ≤ p → p < ENNReal.ofReal (2 * (m + 1) / (m + 2)) → ∃ C : ℝ≥0,
    ∀ f : 𝓢(E (m + 1), ℂ),
      eLpNorm (paraboloidRestriction f) p (volume.restrict (closedBall (0 : E m) 1)) ≤
        C * eLpNorm f p volume

/-! ## Kakeya and Nikodym (Conjectures 4.5–4.8) -/

/-- The `1 × δ` tube with centre `c` and axis direction `ω`: the cylinder of length `1` and
radius `δ` around the segment `c + [-1/2, 1/2] ω`. -/
def tube {n : ℕ} (δ : ℝ) (ω c : E n) : Set (E n) :=
  {x | |inner ℝ (x - c) ω| ≤ 1 / 2 ∧ ‖x - c - inner ℝ (x - c) ω • ω‖ ≤ δ}

/-- The Kakeya maximal function `f*_δ(ω) = sup_{T ∥ ω} |T|⁻¹ ∫_T f` on `S^{n-1}`
(Conjecture 4.5): the supremum over the `1 × δ` tubes oriented in the direction `ω`. -/
noncomputable def kakeyaMaximal {n : ℕ} (δ : ℝ) (f : E n → ℝ) (ω : sphere (0 : E n) 1) : ℝ :=
  ⨆ c : E n, (volume (tube δ (ω : E n) c)).toReal⁻¹ * ∫ x in tube δ (ω : E n) c, f x

/-- `K(p, α)`, Conjecture 4.5: `‖f*_δ‖_{Lᵖ(S^{n-1})} ≲ δ^{1 - n/p - α} ‖f‖_p` for compactly
supported Schwartz `f` and `0 < δ ≪ 1`. -/
def KakeyaMaximalEstimate (n : ℕ) (p α : ℝ) : Prop :=
  ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ f : 𝓢(E n, ℝ), HasCompactSupport f →
    eLpNorm (kakeyaMaximal δ f) (ENNReal.ofReal p) (sphereMeasure n) ≤
      ENNReal.ofReal (C * δ ^ (1 - (n : ℝ) / p - α)) * eLpNorm f (ENNReal.ofReal p) volume

/-- Conjecture 4.5 (Kakeya maximal function): `K(p, α)` for all `1 ≤ p ≤ n` and `α > 0`. -/
def KakeyaMaximalConjecture (n : ℕ) : Prop :=
  ∀ p : ℝ, 1 ≤ p → p ≤ n → ∀ α : ℝ, 0 < α → KakeyaMaximalEstimate n p α

/-- The Nikodym maximal function `f**_δ(x) = sup_{T ∋ x} |T|⁻¹ ∫_T f` on `ℝⁿ`
(Conjecture 4.7): the supremum over all `1 × δ` tubes containing `x`. -/
noncomputable def nikodymMaximal {n : ℕ} (δ : ℝ) (f : E n → ℝ) (x : E n) : ℝ :=
  ⨆ T : {T : E n × E n // ‖T.1‖ = 1 ∧ x ∈ tube δ T.1 T.2},
    (volume (tube δ T.1.1 T.1.2)).toReal⁻¹ * ∫ y in tube δ T.1.1 T.1.2, f y

/-- `N(p, α)`, Conjecture 4.7: `‖f**_δ‖_p ≲ δ^{1 - n/p - α} ‖f‖_p` for compactly supported
Schwartz `f` and `0 < δ ≪ 1`. -/
def NikodymMaximalEstimate (n : ℕ) (p α : ℝ) : Prop :=
  ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ f : 𝓢(E n, ℝ), HasCompactSupport f →
    eLpNorm (nikodymMaximal δ f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (C * δ ^ (1 - (n : ℝ) / p - α)) * eLpNorm f (ENNReal.ofReal p) volume

/-- Conjecture 4.7 (Nikodym maximal function): `N(p, α)` for all `1 ≤ p ≤ n` and `α > 0`. -/
def NikodymMaximalConjecture (n : ℕ) : Prop :=
  ∀ p : ℝ, 1 ≤ p → p ≤ n → ∀ α : ℝ, 0 < α → NikodymMaximalEstimate n p α

/-- The `r`-covering number of `A`: the least number of open balls of radius `r` covering `A`
(`0` if there is no finite cover). -/
noncomputable def coveringNumber {n : ℕ} (A : Set (E n)) (r : ℝ) : ℕ :=
  sInf {k : ℕ | ∃ c : Fin k → E n, A ⊆ ⋃ i, ball (c i) r}

/-- The lower Minkowski dimension `liminf_{r → 0⁺} log N(A, r) / log (1/r)`. -/
noncomputable def lowerMinkowskiDim {n : ℕ} (A : Set (E n)) : ℝ :=
  Filter.liminf (fun r : ℝ => Real.log (coveringNumber A r) / Real.log (1 / r))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

/-- The upper Minkowski dimension `limsup_{r → 0⁺} log N(A, r) / log (1/r)`. -/
noncomputable def upperMinkowskiDim {n : ℕ} (A : Set (E n)) : ℝ :=
  Filter.limsup (fun r : ℝ => Real.log (coveringNumber A r) / Real.log (1 / r))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

/-- Conjecture 4.6 (Kakeya set), read for bounded sets: every bounded subset of `ℝⁿ` containing
a unit line segment in each direction has Minkowski dimension `n`. -/
def KakeyaSetConjecture (n : ℕ) : Prop :=
  ∀ K : Set (E n), Bornology.IsBounded K → FCP.Kakeya.IsKakeya K →
    lowerMinkowskiDim K = n ∧ upperMinkowskiDim K = n

/-- A Nikodym set (Conjecture 4.8): for every `x ∈ ℝⁿ` there is a line `l` through `x` such that
`E ∩ l` contains a unit line segment. -/
def IsNikodymSet {n : ℕ} (S : Set (E n)) : Prop :=
  ∀ x : E n, ∃ v : E n, ‖v‖ = 1 ∧ ∃ s : ℝ, segment ℝ (x + s • v) (x + (s + 1) • v) ⊆ S

/-- Conjecture 4.8 (Nikodym set), read for bounded sets: every bounded Nikodym set has
Minkowski dimension `n`. -/
def NikodymSetConjecture (n : ℕ) : Prop :=
  ∀ S : Set (E n), Bornology.IsBounded S → IsNikodymSet S →
    lowerMinkowskiDim S = n ∧ upperMinkowskiDim S = n

end TaoBR


