-- Prove2me | Definitions.Def_NeymanPearsonClassification_Basic
-- name    : NeymanPearsonClassification_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T17:40:45.622851+00:00
-- url     : https://prove2.me/theorems/717d30b8-9482-4281-989b-41fb7dd62a37
-- title:
--   Convexified Neyman-Pearson classification: surrogates, errors, NP classifier, chance constrained programs
-- statement:
--   Objects of Rigollet and Tong (2011), Sections 2-6.
--
--   1. **Convex surrogate (Definition 2.1).** A function $\varphi:[-1,1]\to\mathbb{R}_+$ that is non-decreasing, continuous and convex with $\varphi(0)=1$.
--   2. **Base classifiers and their convex hull (Section 2.1).** Measurable functions $h_1,\dots,h_M:\mathcal X\to[-1,1]$. For $\lambda$ in the flat simplex $\Lambda=\{\lambda\in\mathbb{R}^M:\lambda_j\ge0,\ \sum_j\lambda_j=1\}$, $\mathsf h_\lambda=\sum_j\lambda_jh_j$, and $\mathcal H^{\mathrm{conv}}=\{\mathsf h_\lambda:\lambda\in\Lambda\}$.
--   3. **Errors (Section 2.2).** Let $P^-$ and $P^+$ be the laws of $X$ given $Y=-1$ and $Y=1$. The type I error is $R^-(h)=P^-(h(X)\ge0)$ and the type II error is $R^+(h)=P^+(h(X)\le0)$. The $\varphi$-type I and II errors are $R^-_\varphi(h)=\int\varphi(h)\,dP^-$ and $R^+_\varphi(h)=\int\varphi(-h)\,dP^+$.
--   4. **Empirical errors (Sections 3.1-3.2).** For a sample $X^-_1,\dots,X^-_{n^-}$ the empirical type I error is $\hat R^-(h)=\frac1{n^-}\sum_i\mathbf 1(h(X^-_i)\ge0)$. The empirical $\varphi$-errors are $\hat R^-_\varphi(h)=\frac1{n^-}\sum_i\varphi(h(X^-_i))$ and $\hat R^+_\varphi(h)=\frac1{n^+}\sum_i\varphi(-h(X^+_i))$.
--   5. **Constraint sets.** $\mathcal H^{\varphi,a}=\{h\in\mathcal H^{\mathrm{conv}}:R^-_\varphi(h)\le a\}$ and $\mathcal H^{\varphi,a}_{n^-}=\{h\in\mathcal H^{\mathrm{conv}}:\hat R^-_\varphi(h)\le a\}$. The optimal value is $\gamma(a)=\inf_{h\in\mathcal H^{\varphi,a}}R^+_\varphi(h)$, written $\min_{h\in\mathcal H^{\varphi,a}}R^+_\varphi(h)$ in the paper.
--   6. **Convexified NP classifier (eq. 3.4).** $\tilde h^\tau$ is any solution of $\min\{\hat R^+_\varphi(h):h\in\mathcal H^{\mathrm{conv}},\ \hat R^-_\varphi(h)\le\alpha-\tau/\sqrt{n^-}\}$.
--   7. **Constants (Section 4).** $\kappa=4\sqrt2\,L\sqrt{\log(2M/\delta)}$. $\bar\varepsilon$ is the smallest $\varepsilon$ with $\mathcal H^{\varphi,\varepsilon\alpha}\ne\emptyset$, and $n_0=\lceil(4\kappa/((1-\bar\varepsilon)\alpha))^2\rceil$ (eq. 4.3).
--   8. **Label split (Section 4.3).** For labels $Y_1,\dots,Y_n$, the index sets $\{i:Y_i=-1\}$ and $\{i:Y_i=1\}$ have sizes $N^-$ and $N^+$.
--   9. **Binomial tail (Section 6.6).** $P(N\ge t)=\sum_{t\le j\le n}\binom nj q^j(1-q)^{n-j}$ for $N\sim\mathrm{Bin}(n,q)$.
--   10. **Chance constrained programs (Section 5).** With $F(\lambda,\xi)=\sum_j\lambda_jg_j(\xi)$ and $g_j:\Xi\to[-1,1]$: $\lambda$ is feasible for (5.1) if $\lambda\in\Lambda$ and $P\{F(\lambda,\xi)\le0\}\ge1-\alpha$. $\tilde\lambda$ solves $\min_{\lambda\in\Lambda}f(\lambda)$ subject to $\sum_{i=1}^n\varphi(F(\lambda,\xi_i))\le n\alpha-\kappa\sqrt n$. $f^*_\varphi=\inf\{f(\lambda):\lambda\in\Lambda,\ E\varphi(F(\lambda,\xi))\le\alpha\}$ is the optimal value of (5.7).
--
--   **Formalization Note** The covariate space $\mathcal X\subset\mathbb{R}^d$ is taken to be $\mathbb{R}^d$ (`EuclideanSpace ℝ (Fin d)`). Classifiers on a measurable $\mathcal X$ extend by $0$, and laws on $\mathcal X$ are laws on $\mathbb{R}^d$ carried by $\mathcal X$. A surrogate is a function $\mathbb{R}\to\mathbb{R}$ whose properties are required only on $[-1,1]$, the only arguments ever used. Infima are real infima ($\inf\emptyset=0$ in Lean). Every statement that uses $\gamma(a)$, $\bar\varepsilon$ or $f^*_\varphi$ assumes or proves that the set involved is nonempty. An empirical average over an empty sample is $0$ in Lean. Theorems 4.1 and 4.2 assume nonempty samples; Corollary 4.1 guards the empty case explicitly in part 1, while part 2 includes it, where it is covered by the stated failure probability.
-- source:
--   Rigollet and Tong, Neyman-Pearson classification, convexity and stochastic constraints, arXiv:1102.5750v1 (2011), Definition 2.1 (p. 2), Sections 2.1-2.2 (pp. 3-4), 3.1-3.2 and eq. (3.4) (pp. 5-7), 4.1-4.3 with Assumption 1 and eq. (4.3) (pp. 8-10), Section 5 eqs. (5.1), (5.7) (pp. 11-12), Section 6.6 (pp. 19-20)

import Mathlib

/-!
Rigollet and Tong, *Neyman-Pearson classification, convexity and stochastic constraints*,
arXiv:1102.5750v1 (2011): convex surrogates (Definition 2.1), the convex hull of base classifiers
(Section 2.1), type I/II errors and their convexified versions (Section 2.2), empirical errors and
the convexified NP classifier (Sections 3.1-3.2, eq. (3.4)), the constants of Section 4
(`κ`, `ε̄`, `n₀` of eq. (4.3)), the label-split samples of Section 4.3, the binomial tails of
Section 6.6 and the chance constrained programs (5.1), (5.7) of Section 5.
-/

open MeasureTheory

noncomputable section

namespace NeymanPearsonClassification

/-- Definition 2.1 (p. 2): `φ : [-1,1] → ℝ₊` is a convex surrogate if it is non-negative,
non-decreasing, continuous and convex on `[-1,1]` and `φ(0) = 1`. Values of `φ` outside
`[-1,1]` are never used. -/
def IsConvexSurrogate (φ : ℝ → ℝ) : Prop :=
  (∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ φ x) ∧ MonotoneOn φ (Set.Icc (-1) 1) ∧
    ContinuousOn φ (Set.Icc (-1) 1) ∧ ConvexOn ℝ (Set.Icc (-1) 1) φ ∧ φ 0 = 1

/-- Section 2.1 (p. 3): base classifiers `h₁, …, h_M : 𝒳 → [-1,1]` (measurable, the standing
convention). The same structure serves the functions `g_j : Ξ → [-1,1]` of Section 5 (p. 11). -/
def IsBaseFamily {X : Type*} [MeasurableSpace X] {M : ℕ} (h : Fin M → X → ℝ) : Prop :=
  ∀ j, Measurable (h j) ∧ ∀ x, h j x ∈ Set.Icc (-1 : ℝ) 1

/-- Section 2.1 (p. 3): the convex combination `h_λ = ∑_j λ_j h_j`; in Section 5 (p. 11) this is
`F(λ, ξ) = ∑_j λ_j g_j(ξ)`. -/
def convComb {X : Type*} {M : ℕ} (h : Fin M → X → ℝ) (lam : Fin M → ℝ) : X → ℝ :=
  fun x => ∑ j, lam j * h j x

/-- Section 2.1 (p. 3): `H^conv = {h_λ : λ ∈ Λ}`, with `Λ` the flat simplex of `ℝ^M`. -/
def HConv {X : Type*} {M : ℕ} (h : Fin M → X → ℝ) : Set (X → ℝ) :=
  convComb h '' stdSimplex ℝ (Fin M)

/-- Section 2.2 (p. 3): type I error `R⁻(h) = P⁻(h(X) ≥ 0)`, `P⁻` the law of `X` given `Y = -1`. -/
def typeI {X : Type*} [MeasurableSpace X] (Pm : Measure X) (f : X → ℝ) : ℝ :=
  (Pm {x | 0 ≤ f x}).toReal

/-- Section 2.2 (p. 3): type II error `R⁺(h) = P⁺(h(X) ≤ 0)`, `P⁺` the law of `X` given `Y = 1`. -/
def typeII {X : Type*} [MeasurableSpace X] (Pp : Measure X) (f : X → ℝ) : ℝ :=
  (Pp {x | f x ≤ 0}).toReal

/-- Section 2.2 (p. 4): `φ`-type I error `R⁻_φ(h) = E[φ(-Y h(X)) | Y = -1] = ∫ φ(h) dP⁻`. -/
def phiTypeI {X : Type*} [MeasurableSpace X] (Pm : Measure X) (φ : ℝ → ℝ) (f : X → ℝ) : ℝ :=
  ∫ x, φ (f x) ∂Pm

/-- Section 2.2 (p. 4): `φ`-type II error `R⁺_φ(h) = E[φ(-Y h(X)) | Y = 1] = ∫ φ(-h) dP⁺`. -/
def phiTypeII {X : Type*} [MeasurableSpace X] (Pp : Measure X) (φ : ℝ → ℝ) (f : X → ℝ) : ℝ :=
  ∫ x, φ (-f x) ∂Pp

open Classical in
/-- Section 3.1 (p. 5): empirical type I error `R̂⁻(h) = (1/n⁻) ∑_i 1(h(X⁻_i) ≥ 0)` of the
sample points `x i`, `i ∈ s`. -/
def empTypeI {ι X : Type*} (s : Finset ι) (x : ι → X) (f : X → ℝ) : ℝ :=
  ((s.filter fun i => 0 ≤ f (x i)).card : ℝ) / s.card

/-- Section 3.2 (p. 7): empirical `φ`-type I error `R̂⁻_φ(h) = (1/n⁻) ∑_i φ(h(X⁻_i))` of the sample
points `x i`, `i ∈ s`. -/
def empPhiTypeI {ι X : Type*} (φ : ℝ → ℝ) (s : Finset ι) (x : ι → X) (f : X → ℝ) : ℝ :=
  (∑ i ∈ s, φ (f (x i))) / s.card

/-- Section 3.2 (p. 7): empirical `φ`-type II error `R̂⁺_φ(h) = (1/n⁺) ∑_i φ(-h(X⁺_i))` of the
sample points `x i`, `i ∈ s`. -/
def empPhiTypeII {ι X : Type*} (φ : ℝ → ℝ) (s : Finset ι) (x : ι → X) (f : X → ℝ) : ℝ :=
  (∑ i ∈ s, φ (-f (x i))) / s.card

/-- Section 3.2 (p. 7): `H^{φ,a} = {h ∈ H^conv : R⁻_φ(h) ≤ a}`. -/
def Hphi {X : Type*} [MeasurableSpace X] {M : ℕ} (h : Fin M → X → ℝ) (Pm : Measure X)
    (φ : ℝ → ℝ) (a : ℝ) : Set (X → ℝ) :=
  {f | f ∈ HConv h ∧ phiTypeI Pm φ f ≤ a}

/-- Section 3.2 (p. 7): `H^{φ,a}_{n⁻} = {h ∈ H^conv : R̂⁻_φ(h) ≤ a}`. -/
def HphiEmp {ι X : Type*} {M : ℕ} (h : Fin M → X → ℝ) (φ : ℝ → ℝ) (s : Finset ι) (x : ι → X)
    (a : ℝ) : Set (X → ℝ) :=
  {f | f ∈ HConv h ∧ empPhiTypeI φ s x f ≤ a}

/-- Section 4.2 (p. 8) and Lemma 6.2 (p. 16): `γ(a) = inf_{h ∈ H^{φ,a}} R⁺_φ(h)`, written
`min_{h ∈ H^{φ,a}} R⁺_φ(h)` in the paper. Statements use it only where `H^{φ,a} ≠ ∅`. -/
def minPhiTypeII {X : Type*} [MeasurableSpace X] {M : ℕ} (h : Fin M → X → ℝ)
    (Pm Pp : Measure X) (φ : ℝ → ℝ) (a : ℝ) : ℝ :=
  sInf (phiTypeII Pp φ '' Hphi h Pm φ a)

/-- Eq. (3.4) (p. 7): `f` is a convexified NP classifier `h̃^τ`, i.e. a solution of
`min { R̂⁺_φ(h) : h ∈ H^conv, R̂⁻_φ(h) ≤ α - τ/√n⁻ }`, where the class `-1` sample is
`(xm i)_{i ∈ sm}` (`n⁻ = |sm|`) and the class `+1` sample is `(xp i)_{i ∈ sp}`. -/
def IsNPClassifier {ι ι' X : Type*} {M : ℕ} (h : Fin M → X → ℝ) (φ : ℝ → ℝ) (α τ : ℝ)
    (sm : Finset ι) (xm : ι → X) (sp : Finset ι') (xp : ι' → X) (f : X → ℝ) : Prop :=
  f ∈ HphiEmp h φ sm xm (α - τ / Real.sqrt sm.card) ∧
    ∀ g ∈ HphiEmp h φ sm xm (α - τ / Real.sqrt sm.card),
      empPhiTypeII φ sp xp f ≤ empPhiTypeII φ sp xp g

/-- Theorem 4.1 (p. 8) and Theorem 5.1 (p. 12): `κ = 4√2 L √(log(2M/δ))`. -/
def kappa (L : ℝ) (M : ℕ) (δ : ℝ) : ℝ :=
  4 * Real.sqrt 2 * L * Real.sqrt (Real.log (2 * M / δ))

/-- Section 4.2 (p. 9): `ε̄`, the smallest `ε` such that `H^{φ, εα} ≠ ∅` (defined under
Assumption 1). -/
def epsBar {X : Type*} [MeasurableSpace X] {M : ℕ} (h : Fin M → X → ℝ) (Pm : Measure X)
    (φ : ℝ → ℝ) (α : ℝ) : ℝ :=
  sInf {ε : ℝ | (Hphi h Pm φ (ε * α)).Nonempty}

/-- Eq. (4.3) (p. 9): `n₀`, the smallest integer with `n₀ ≥ (4κ / ((1 - ε̄)α))²`. -/
def nZero (κ εbar α : ℝ) : ℕ :=
  ⌈(4 * κ / ((1 - εbar) * α)) ^ 2⌉₊

open Classical in
/-- Section 4.3 (p. 10): the indices `i` with label `Y_i = c`; for `c = -1` its cardinality is
`N⁻ = card{Y_i : Y_i = -1}`, for `c = 1` it is `N⁺`. -/
def labelIdx {n : ℕ} (y : Fin n → ℝ) (c : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => y i = c

open Classical in
/-- Section 6.6 (pp. 19-20): `P(N ≥ t)` for `N` binomial with parameters `n` and `q`,
`∑_{j ≤ n, j ≥ t} C(n,j) q^j (1-q)^(n-j)`. -/
def binomTail (n : ℕ) (q t : ℝ) : ℝ :=
  ∑ j ∈ (Finset.range (n + 1)).filter (fun j : ℕ => t ≤ (j : ℝ)),
    (n.choose j : ℝ) * q ^ j * (1 - q) ^ (n - j)

/-- Eq. (5.1) (p. 11): `λ` is feasible for the chance constrained program, i.e. `λ ∈ Λ` and
`P{F(λ, ξ) ≤ 0} ≥ 1 - α`, with `F(λ, ξ) = ∑_j λ_j g_j(ξ)` and `ξ ∼ Pxi`. -/
def IsChanceFeasible {Xi : Type*} [MeasurableSpace Xi] {M : ℕ} (g : Fin M → Xi → ℝ)
    (Pxi : Measure Xi) (α : ℝ) (lam : Fin M → ℝ) : Prop :=
  lam ∈ stdSimplex ℝ (Fin M) ∧ ENNReal.ofReal (1 - α) ≤ Pxi {x | convComb g lam x ≤ 0}

/-- Section 5 (p. 12): `λ̃` solves the sampled convexified program
`min_{λ ∈ Λ} f(λ)` s.t. `∑_{i=1}^n φ(F(λ, ξ_i)) ≤ nα - κ√n`. -/
def IsScenarioSolution {Xi : Type*} {M n : ℕ} (g : Fin M → Xi → ℝ) (φ : ℝ → ℝ)
    (f : (Fin M → ℝ) → ℝ) (α κ : ℝ) (xs : Fin n → Xi) (lam : Fin M → ℝ) : Prop :=
  lam ∈ stdSimplex ℝ (Fin M) ∧
    ∑ i, φ (convComb g lam (xs i)) ≤ n * α - κ * Real.sqrt n ∧
    ∀ l ∈ stdSimplex ℝ (Fin M), ∑ i, φ (convComb g l (xs i)) ≤ n * α - κ * Real.sqrt n →
      f lam ≤ f l

/-- Eq. (5.7) (p. 12): `f*_φ`, the optimal value of `min_{λ ∈ Λ} f(λ)` s.t.
`E[φ(F(λ, ξ))] ≤ α` (an infimum; used only where the constraint is feasible). -/
def ccpOptValue {Xi : Type*} [MeasurableSpace Xi] {M : ℕ} (g : Fin M → Xi → ℝ)
    (Pxi : Measure Xi) (φ : ℝ → ℝ) (f : (Fin M → ℝ) → ℝ) (α : ℝ) : ℝ :=
  sInf (f '' {l | l ∈ stdSimplex ℝ (Fin M) ∧ phiTypeI Pxi φ (convComb g l) ≤ α})

end NeymanPearsonClassification


