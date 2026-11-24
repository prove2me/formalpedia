-- Prove2me | Definitions.Def_WirtingerFlow_Basic
-- name    : WirtingerFlow_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T20:36:06.530401+00:00
-- url     : https://prove2.me/theorems/b4cd6e22-1192-4c8a-97f8-bf29e1004a00
-- title:
--   Wirtinger flow: phaseless measurements, objective and Wirtinger gradient, spectral initialization, phase distance, Gaussian and coded diffraction models, Hessian, regularity condition
-- statement:
--   Objects of Sections 2-7 of Candès, Li and Soltanolkotabi (2015).
--
--   1. **Signals and samples (eq. 1.1).** Signals $x,z\in\mathbb{C}^n$ carry the Euclidean norm and the inner product $\langle u,v\rangle=u^*v$. Given sampling vectors $a_r\in\mathbb{C}^n$, indexed by a finite set of size $m$, the phaseless samples are $y_r=|a_r^*x|^2$.
--   2. **Objective and Wirtinger gradient (eqs. 2.1, 2.2; Section 7.2).** The objective is $f(z)=\frac1{2m}\sum_r(y_r-|a_r^*z|^2)^2$, and its Wirtinger gradient is
--   $$\nabla f(z)=\frac1m\sum_{r=1}^m\big(|a_r^*z|^2-y_r\big)\,a_ra_r^*z.$$
--   3. **Distance (Definition 3.2).** $\operatorname{dist}(z,x)=\min_{\varphi\in[0,2\pi]}\|z-e^{i\varphi}x\|$. A minimising phase is written $\varphi(z)$.
--   4. **Iterations.** The gradient iteration of Lemma 7.10 is $z_{\tau+1}=z_\tau-\mu\nabla f(z_\tau)$. The Wirtinger flow with constant learning parameter $\mu$ (eq. 2.2) is $z_{\tau+1}=z_\tau-\frac{\mu}{\|z_0\|^2}\nabla f(z_\tau)$.
--   5. **Spectral initialization (Algorithm 1, Theorem 3.3).** $Y=\frac1m\sum_ry_ra_ra_r^*$. An initial estimate is $z_0=\sqrt{m^{-1}\sum_ry_r}\;v$, where $v$ is a unit eigenvector of $Y$ for its largest eigenvalue.
--   6. **Regularity condition (Condition 7.9).** $\mathrm{RC}(\alpha,\beta,\varepsilon)$ holds if, for every $z$ with $\operatorname{dist}(z,x)\le\varepsilon$ and every minimising phase $\varphi(z)$,
--   $$\operatorname{Re}\langle\nabla f(z),z-xe^{i\varphi(z)}\rangle\ge\tfrac1\alpha\operatorname{dist}^2(z,x)+\tfrac1\beta\|\nabla f(z)\|^2,$$
--   where $f$ uses the data $y=|Ax|^2$.
--   7. **Hessian (Sections 6, 7.2).** In conjugate coordinates,
--   $$\nabla^2f(z)=\frac1m\sum_r\begin{bmatrix}(2|a_r^*z|^2-y_r)a_ra_r^*&(a_r^*z)^2a_ra_r^T\\\overline{(a_r^*z)}^2\bar a_ra_r^*&(2|a_r^*z|^2-y_r)\bar a_ra_r^T\end{bmatrix}\in\mathbb{C}^{2n\times2n}.$$
--   The matrix of Lemma 7.1 is $I_{2n}+\frac32\begin{bmatrix}x\\\bar x\end{bmatrix}[x^*,x^T]-\frac12\begin{bmatrix}x\\-\bar x\end{bmatrix}[x^*,-x^T]$. The stacked vector $\begin{bmatrix}h\\\bar h\end{bmatrix}$ is written $[h;\bar h]$. $\|M\|$ is the operator norm, and $m^{-1}\sum_ra_ra_r^*$ is the sample covariance.
--   8. **Gaussian model (Definition 3.1).** The vectors $a_1,\dots,a_m$ are i.i.d., and each has i.i.d. coordinates with law $\mathcal N(0,\frac12)+i\,\mathcal N(0,\frac12)$ (independent real and imaginary parts).
--   9. **Coded diffraction model (Section 4.1, eqs. 4.1-4.2).** A law $\nu$ of a complex random variable $d$ is admissible with bound $M$ if $d$ is symmetric, $|d|\le M$, $\mathbb E d=0$, $\mathbb E d^2=0$ and $\mathbb E|d|^4=2(\mathbb E|d|^2)^2$. The patterns $d_1,\dots,d_L\in\mathbb{C}^n$ are i.i.d. with i.i.d. entries of law $\nu$. The sampling vectors are $a_{(\ell,k)}(t)=d_\ell(t)e^{i2\pi kt/n}$ for $1\le\ell\le L$ and $0\le k,t\le n-1$, so $m=nL$ and $y_{(\ell,k)}=\big|\sum_tx[t]\bar d_\ell(t)e^{-i2\pi kt/n}\big|^2$.
--
--   **Formalization Note** The minimum in Definition 3.2 is written as an infimum over the compact interval $[0,2\pi]$, where it is attained. Since $\varphi(z)$ need not be unique (the phase $e^{i\varphi(z)}$ is unique once $\operatorname{dist}(z,x)<\|x\|$, but on $[0,2\pi]$ the endpoints $0$ and $2\pi$ give the same phase, so $\varphi$ itself is unique only modulo $2\pi$), $\mathrm{RC}$ is required for every minimising phase. The leading eigenvector is characterised by comparison with every real eigenvalue, which is enough because $Y$ is Hermitian. A sample of either model is the array of coordinates of the random vectors, and its law is a finite product measure.
-- source:
--   Candès, Li and Soltanolkotabi, Phase Retrieval via Wirtinger Flow: Theory and Algorithms, arXiv:1407.1065v3 (2015), Sections 1-2 (eqs. (1.1), (2.1), (2.2), Algorithm 1), Section 3.1 (Definitions 3.1-3.2), Section 4.1 (eqs. (4.1)-(4.2)), Section 6, Sections 7.1-7.4 (Lemma 7.1, Condition 7.9)

import Mathlib

/-!
Candès, Li and Soltanolkotabi, *Phase Retrieval via Wirtinger Flow: Theory and Algorithms*,
arXiv:1407.1065v3 (2015): the phaseless measurements of eq. (1.1), the objective and Wirtinger
gradient of eqs. (2.1)-(2.2) and Section 7.2, the spectral initialization of Algorithm 1, the
distance of Definition 3.2, the Gaussian model of Definition 3.1, the admissible coded diffraction
model of Section 4.1 (eqs. (4.1)-(4.2)), the complex Hessian of Sections 6 and 7.2 with its
expectation from Lemma 7.1, and the regularity condition of Condition 7.9.
-/

open MeasureTheory ProbabilityTheory Complex

noncomputable section

namespace WirtingerFlow

/-- Signals and sampling vectors live in `ℂⁿ` with its Euclidean norm and the inner product
`⟨u, v⟩ = u^* v` (conjugate-linear in the first argument), as throughout the paper. -/
abbrev Sig (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- A coordinate vector `(v(0), …, v(n-1))` viewed as an element of `ℂⁿ`. -/
def toSig {n : ℕ} (v : Fin n → ℂ) : Sig n := WithLp.toLp 2 v

variable {R : Type*} [Fintype R] {n : ℕ}

/-- Eq. (1.1): the phaseless samples `y_r = |⟨a_r, x⟩|² = |a_r^* x|²`, indexed by a finite set of
`m = |R|` sampling vectors `a_r`. -/
def meas (a : R → Sig n) (x : Sig n) (r : R) : ℝ := ‖inner ℂ (a r) x‖ ^ 2

/-- Eq. (2.1) with the quadratic loss `ℓ(x, y) = (x - y)²`:
`f(z) = (1/2m) ∑_r (y_r - |a_r^* z|²)²`. -/
def loss (a : R → Sig n) (y : R → ℝ) (z : Sig n) : ℝ :=
  1 / (2 * (Fintype.card R : ℝ)) * ∑ r, (y r - ‖inner ℂ (a r) z‖ ^ 2) ^ 2

/-- Eq. (2.2) and Section 7.2: the Wirtinger gradient
`∇f(z) = (1/m) ∑_r (|a_r^* z|² - y_r) (a_r a_r^*) z`. -/
def grad (a : R → Sig n) (y : R → ℝ) (z : Sig n) : Sig n :=
  ((1 / (Fintype.card R : ℝ) : ℝ) : ℂ) •
    ∑ r, ((((‖inner ℂ (a r) z‖ ^ 2 - y r : ℝ)) : ℂ) * inner ℂ (a r) z) • a r

/-- Definition 3.2: `dist(z, x) = min_{φ ∈ [0, 2π]} ‖z - e^{iφ} x‖` (the minimum is attained, so it
is written as an infimum over the compact interval). -/
def phaseDist (z x : Sig n) : ℝ :=
  sInf ((fun φ : ℝ => ‖z - Complex.exp ((φ : ℂ) * I) • x‖) '' Set.Icc 0 (2 * Real.pi))

/-- Section 7.1: `φ` is a phase `φ(z) ∈ [0, 2π]` attaining `dist(z, x) = ‖z - e^{iφ(z)} x‖`. -/
def IsMinPhase (z x : Sig n) (φ : ℝ) : Prop :=
  φ ∈ Set.Icc 0 (2 * Real.pi) ∧ ‖z - Complex.exp ((φ : ℂ) * I) • x‖ = phaseDist z x

/-- Lemma 7.10: the gradient iteration `z_{τ+1} = z_τ - μ ∇f(z_τ)` started at `z_0`. -/
def gdSeq (a : R → Sig n) (y : R → ℝ) (μ : ℝ) (z0 : Sig n) : ℕ → Sig n
  | 0 => z0
  | τ + 1 => gdSeq a y μ z0 τ - (μ : ℂ) • grad a y (gdSeq a y μ z0 τ)

/-- Eq. (2.2) with a constant learning parameter `μ_τ = μ`:
the Wirtinger flow iterates `z_{τ+1} = z_τ - (μ / ‖z_0‖²) ∇f(z_τ)`. -/
def wfSeq (a : R → Sig n) (y : R → ℝ) (μ : ℝ) (z0 : Sig n) : ℕ → Sig n :=
  gdSeq a y (μ / ‖z0‖ ^ 2) z0

/-- Algorithm 1: the matrix `Y = (1/m) ∑_r y_r a_r a_r^*`, acting on `v` as
`Y v = (1/m) ∑_r y_r (a_r^* v) a_r`. -/
def specOp (a : R → Sig n) (y : R → ℝ) (v : Sig n) : Sig n :=
  ((1 / (Fintype.card R : ℝ) : ℝ) : ℂ) • ∑ r, ((y r : ℂ) * inner ℂ (a r) v) • a r

/-- Algorithm 1: `v` is an eigenvector of `Y` for its largest eigenvalue. Since `Y` is Hermitian
when `y` is real, every eigenvalue is real, so the comparison ranges over real eigenvalues. -/
def IsLeadingEigvec (Y : Sig n → Sig n) (v : Sig n) : Prop :=
  v ≠ 0 ∧ ∃ c : ℝ, Y v = (c : ℂ) • v ∧
    ∀ (c' : ℝ) (w : Sig n), w ≠ 0 → Y w = (c' : ℂ) • w → c' ≤ c

/-- Theorem 3.3: the Wirtinger flow initial estimates, i.e. every leading eigenvector of `Y` of unit
norm rescaled to squared Euclidean norm `m^{-1} ∑_r y_r`. -/
def initSet (a : R → Sig n) (y : R → ℝ) : Set (Sig n) :=
  {z | ∃ v : Sig n, IsLeadingEigvec (specOp a y) v ∧ ‖v‖ = 1 ∧
    z = ((Real.sqrt ((∑ r, y r) / (Fintype.card R : ℝ)) : ℝ) : ℂ) • v}

/-- Condition 7.9, `RC(α, β, ε)` for the objective `f` with data `y = |A x|²`: for every `z` with
`dist(z, x) ≤ ε` and every phase `φ(z)` attaining `dist(z, x)`,
`Re ⟨∇f(z), z - x e^{iφ(z)}⟩ ≥ (1/α) dist²(z, x) + (1/β) ‖∇f(z)‖²`. -/
def RegCond (a : R → Sig n) (x : Sig n) (α β ε : ℝ) : Prop :=
  ∀ z : Sig n, phaseDist z x ≤ ε → ∀ φ : ℝ, IsMinPhase z x φ →
    1 / α * phaseDist z x ^ 2 + 1 / β * ‖grad a (meas a x) z‖ ^ 2 ≤
      (inner ℂ (grad a (meas a x) z) (z - Complex.exp ((φ : ℂ) * I) • x)).re

/-- Sections 6 and 7.2: the complex Hessian of `f` in conjugate coordinates,
`∇²f(z) = (1/m) ∑_r [[(2|a_r^* z|² - y_r) a_r a_r^*, (a_r^* z)² a_r a_r^T],
[(conj(a_r^* z))² ā_r a_r^*, (2|a_r^* z|² - y_r) ā_r a_r^T]]`, a `2n × 2n` matrix. -/
def hess (a : R → Sig n) (y : R → ℝ) (z : Sig n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  ((1 / (Fintype.card R : ℝ) : ℝ) : ℂ) • ∑ r, Matrix.fromBlocks
    ((((2 * ‖inner ℂ (a r) z‖ ^ 2 - y r : ℝ)) : ℂ) •
      Matrix.vecMulVec (WithLp.ofLp (a r)) (star (WithLp.ofLp (a r))))
    ((inner ℂ (a r) z) ^ 2 • Matrix.vecMulVec (WithLp.ofLp (a r)) (WithLp.ofLp (a r)))
    ((starRingEnd ℂ (inner ℂ (a r) z)) ^ 2 •
      Matrix.vecMulVec (star (WithLp.ofLp (a r))) (star (WithLp.ofLp (a r))))
    ((((2 * ‖inner ℂ (a r) z‖ ^ 2 - y r : ℝ)) : ℂ) •
      Matrix.vecMulVec (star (WithLp.ofLp (a r))) (WithLp.ofLp (a r)))

/-- Section 6: the conjugate-coordinate vector `[h; h̄] ∈ ℂ^{2n}`. -/
def stack (h : Sig n) : Fin n ⊕ Fin n → ℂ :=
  Sum.elim (WithLp.ofLp h) (star (WithLp.ofLp h))

/-- Lemma 7.1: the matrix
`I_{2n} + (3/2) [x; x̄][x^*, x^T] - (1/2) [x; -x̄][x^*, -x^T]`. -/
def expHess (x : Sig n) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  1 + (3 / 2 : ℂ) • Matrix.vecMulVec (stack x) (star (stack x)) -
    (1 / 2 : ℂ) • Matrix.vecMulVec (Sum.elim (WithLp.ofLp x) (-star (WithLp.ofLp x)))
      (star (Sum.elim (WithLp.ofLp x) (-star (WithLp.ofLp x))))

/-- Lemma 7.8: the sample covariance matrix `m^{-1} ∑_r a_r a_r^*`. -/
def covMat (a : R → Sig n) : Matrix (Fin n) (Fin n) ℂ :=
  ((1 / (Fintype.card R : ℝ) : ℝ) : ℂ) •
    ∑ r, Matrix.vecMulVec (WithLp.ofLp (a r)) (star (WithLp.ofLp (a r)))

/-- The operator (spectral) norm `‖M‖` of a complex square matrix acting on Euclidean space, used
in Lemmas 7.4 and 7.8. -/
def opNorm {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖

/-- Definition 3.1: the standard complex Gaussian `N(0, 1/2) + i N(0, 1/2)` on `ℂ`. -/
def stdCGauss : Measure ℂ :=
  ((gaussianReal 0 (1 / 2 : NNReal)).prod (gaussianReal 0 (1 / 2 : NNReal))).map
    fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I

/-- Definition 3.1: a sampling vector `a ∼ N(0, I/2) + i N(0, I/2)` in `ℂⁿ`, in coordinates. -/
def cnGauss (n : ℕ) : Measure (Fin n → ℂ) :=
  Measure.pi fun _ : Fin n => stdCGauss

/-- Definition 3.1: the Gaussian model, `m` i.i.d. sampling vectors `a_1, …, a_m`; the sample is the
`m × n` array of their coordinates. -/
def gaussModel (m n : ℕ) : Measure (Fin m → Fin n → ℂ) :=
  Measure.pi fun _ : Fin m => cnGauss n

/-- The sampling vectors `a_r ∈ ℂⁿ`, `r = 1, …, m`, read off a sample of the Gaussian model. -/
def rows {m : ℕ} (A : Fin m → Fin n → ℂ) : Fin m → Sig n :=
  fun r => toSig (A r)

/-- Section 4.1, eq. (4.2): `ν`, the law of a complex random variable `d`, is admissible with bound
`M`: `d` is symmetric (`-d` has the law of `d`), `|d| ≤ M`, `E d = 0`, `E d² = 0` and
`E|d|⁴ = 2 (E|d|²)²`. -/
def IsAdmissible (ν : Measure ℂ) (M : ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ ν.map (fun d : ℂ => -d) = ν ∧ (∀ᵐ d ∂ν, ‖d‖ ≤ M) ∧
    ∫ d, d ∂ν = 0 ∧ ∫ d, d ^ 2 ∂ν = 0 ∧ ∫ d, ‖d‖ ^ 4 ∂ν = 2 * (∫ d, ‖d‖ ^ 2 ∂ν) ^ 2

/-- Section 4.1: `L` i.i.d. modulation patterns `d_ℓ = (d_ℓ(0), …, d_ℓ(n-1))` with i.i.d. entries
of law `ν`. -/
def cdpModel (ν : Measure ℂ) (L n : ℕ) : Measure (Fin L → Fin n → ℂ) :=
  Measure.pi fun _ : Fin L => Measure.pi fun _ : Fin n => ν

/-- Eq. (4.1) and Appendix A: the coded diffraction sampling vectors `a_r = D_ℓ f_k`,
`r = (ℓ, k)`, with entries `a_r(t) = d_ℓ(t) e^{i 2π k t / n}`, so that
`y_r = |∑_t x[t] d̄_ℓ(t) e^{-i 2π k t / n}|² = |a_r^* x|²`. -/
def cdpVecs {L : ℕ} (d : Fin L → Fin n → ℂ) : Fin L × Fin n → Sig n :=
  fun r => toSig fun t =>
    d r.1 t * Complex.exp (2 * Real.pi * I * (r.2 : ℂ) * (t : ℂ) / (n : ℂ))

end WirtingerFlow


