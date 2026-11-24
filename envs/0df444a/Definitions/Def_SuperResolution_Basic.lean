-- Prove2me | Definitions.Def_SuperResolution_Basic
-- name    : SuperResolution_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T23:11:24.256797+00:00
-- url     : https://prove2.me/theorems/1869cd4b-7e20-4dc0-a8ee-f60b1f58ac27
-- title:
--   Complex measures, minimum separation, the total-variation program and the dual polynomial of super-resolution
-- statement:
--   Objects of Sections 1–3 and Appendix A of Candès and Fernandez-Granda (2012).
--
--   1. **Circle and measures.** $\mathbb{T}=[0,1)$ with endpoints identified, and $\mathbb{T}^2$, both with their Borel $\sigma$-algebras. A finite complex measure $\nu$ integrates a bounded continuous function $f$ as $\int f(t)\,\nu(\mathrm{d}t)$. Its total-variation norm is $\|\nu\|_{\mathrm{TV}}=|\nu|(\mathbb{T})$, where $|\nu|(B)=\sup\sum_j|\nu(B_j)|$ over finite partitions of $B$ into disjoint measurable sets (Appendix A). The atomic measure with amplitudes $a_t$ on a finite set $T$ is $x=\sum_{t\in T}a_t\delta_t$ (eq. 1.2).
--   2. **Minimum separation (Definition 1.1).** For a finite family $T$ of points, $\Delta(T)=\inf_{t\ne t'\in T}|t-t'|$. On $\mathbb{T}$ the distance wraps around, and on $\mathbb{T}^2$ it is the maximum of the wrap-around distances of the two coordinates ($\ell_\infty$). The infimum is $+\infty$ when $T$ has fewer than two points.
--   3. **Data and the convex program.** $y(k)=\int_{\mathbb{T}}e^{-i2\pi kt}\,x(\mathrm{d}t)$ for $k\in\mathbb{Z}$, $|k|\le f_c$ (eq. 1.3), and on $\mathbb{T}^2$, $y(k)=\int e^{-i2\pi\langle k,t\rangle}x(\mathrm{d}t)$ for $|k_1|,|k_2|\le f_c$ (eq. 1.7). $x$ is the *unique solution* of $\min\|\tilde x\|_{\mathrm{TV}}$ subject to $\mathcal{F}_n\tilde x=y$ (eq. 1.4) if every finite complex measure $\tilde x\ne x$ with the same coefficients has $\|\tilde x\|_{\mathrm{TV}}>\|x\|_{\mathrm{TV}}$. In two dimensions the competitors are restricted to real measures (Theorem 1.3).
--   4. **Low-frequency polynomials (eq. 2.1).** $q(t)=\sum_{k=-f_c}^{f_c}c_ke^{i2\pi kt}$.
--   5. **Kernel and dual polynomial (eqs. 2.3–2.6).** $K(t)=\Big[\dfrac{\sin((f_c/2+1)\pi t)}{(f_c/2+1)\sin(\pi t)}\Big]^4$, with $K=1$ where $\sin(\pi t)=0$. For spike locations $T\subset[0,1)$ and coefficients $\alpha,\beta$ indexed by $T$, $q(t)=\sum_{t_j\in T}\alpha_jK(t-t_j)+\beta_jK'(t-t_j)$ and $q'(t)=\sum_{t_j\in T}\alpha_jK'(t-t_j)+\beta_jK''(t-t_j)$. The coefficients *interpolate* $v$ when $q(t_k)=v_k$ and $q'(t_k)=0$ for every $t_k\in T$.
--   6. **Discrete model (Sections 1.4–1.6, 3).** For $x\in\mathbb{C}^N$: its support $T=\{t:x_t\ne0\}$ and the grid points $t/N\in\mathbb{T}$; $(F_nx)_k=\sum_{t=0}^{N-1}x_te^{-i2\pi kt/N}$ (eq. 1.9); $\|x\|_1=\sum_t|x_t|$; the low-pass projection $P_n=N^{-1}F_n^*F_n$, i.e. $(P_nx)_t=N^{-1}\sum_{|k|\le f_c}e^{i2\pi kt/N}(F_nx)_k$; the super-resolution factor $\mathrm{SRF}=N/n$ with $n=2f_c+1$ (eq. 1.12); and $P_T$, which keeps the entries indexed by $T$ and zeroes the others.
--
--   **Formalization Note** The integral against a complex measure and the total variation are Mathlib's `VectorMeasure.integral` (with complex multiplication as the pairing) and `VectorMeasure.variation`; the total variation is valued in $[0,\infty]$. The paper defines $K$ on $(0,1)$ with $K(0)=1$. The formula is used on all of $\mathbb{R}$, which for even $f_c$ is the $1$-periodic extension. The dual polynomial is written as a function of a real variable, and distances to spikes are wrap-around distances on $\mathbb{T}$.
-- source:
--   Candès and Fernandez-Granda, Towards a Mathematical Theory of Super-Resolution, arXiv:1203.5871v3 (2012), Section 1.2 (Definition 1.1, eqs. (1.2)–(1.5)), Section 1.3 (eq. (1.7)), Sections 1.4–1.5 (eqs. (1.9)–(1.15)), Section 2.2 (eqs. (2.1)–(2.6)), Section 3, Appendix A

import Mathlib

/-!
Candès and Fernandez-Granda, *Towards a Mathematical Theory of Super-Resolution*,
arXiv:1203.5871v3 (2012): complex measures on the circle and their total variation (Section 1.2,
Appendix A), low-frequency Fourier data (eqs. (1.3), (1.7)), the minimum separation
(Definition 1.1), the total-variation program (1.4), low-frequency trigonometric polynomials
(eq. (2.1)), the interpolation kernel and dual polynomial of Section 2 (eqs. (2.3)–(2.6)), and the
discrete model of Sections 1.4–1.6 (eqs. (1.9)–(1.15)).
-/

open MeasureTheory

noncomputable section

namespace SuperResolution

section Measures

variable {X : Type*} [MeasurableSpace X]

/-- Integral `∫ f(t) ν(dt)` of a complex function against a complex measure `ν`, as used in
eqs. (1.3), (1.7) and Appendix A. It is Mathlib's integral against a vector measure, with the
pairing `(f, ν) ↦ f · ν` given by complex multiplication. -/
def cIntegral (ν : ComplexMeasure X) (f : X → ℂ) : ℂ :=
  VectorMeasure.integral ν f (ContinuousLinearMap.mul ℝ ℂ)

/-- Appendix A: the total-variation norm `‖ν‖_TV = |ν|(𝕋)`, where `|ν|(B)` is the supremum of
`∑ⱼ |ν(Bⱼ)|` over finite partitions of `B` into disjoint measurable sets (Mathlib's
`VectorMeasure.variation`). -/
def tvNorm (ν : ComplexMeasure X) : ENNReal :=
  ν.variation Set.univ

/-- Eq. (1.2): the atomic measure `x = ∑ⱼ aⱼ δ_{tⱼ}` with amplitude `a t` at each point `t ∈ T`. -/
def atomicMeasure (T : Finset X) (a : X → ℂ) : ComplexMeasure X :=
  ∑ t ∈ T, VectorMeasure.dirac t (a t)

end Measures

/-- Definition 1.1, eq. (1.5): the minimum separation `Δ(T) = inf_{t ≠ t'} |t - t'|` of a finite
family of points. On `𝕋 = UnitAddCircle` the distance is the wrap-around distance, and on
`𝕋 × 𝕋` it is the `ℓ∞` (maximum) wrap-around distance. The infimum over an empty family (fewer
than two points) is `+∞`. -/
def minSep {X : Type*} [PseudoMetricSpace X] (T : Finset X) : ENNReal :=
  ⨅ t ∈ T, ⨅ t' ∈ T, ⨅ (_ : t ≠ t'), ENNReal.ofReal (dist t t')

/-- Eq. (1.3): the Fourier coefficient `y(k) = ∫ e^{-i2πkt} ν(dt)` of a complex measure on the
circle `𝕋 = [0,1)`. -/
def fourierCoeff (ν : ComplexMeasure UnitAddCircle) (k : ℤ) : ℂ :=
  cIntegral ν (fun t => fourier (-k) t)

/-- Eq. (1.4): `x` is the unique solution of `min ‖x̃‖_TV` subject to `F_n x̃ = y`, where
`y = F_n x` collects the Fourier coefficients `|k| ≤ f_c` and `x̃` ranges over all finite complex
measures on `𝕋`: every other feasible measure has strictly larger total variation. -/
def IsUniqueTVSolution (fc : ℕ) (x : ComplexMeasure UnitAddCircle) : Prop :=
  ∀ ν : ComplexMeasure UnitAddCircle,
    (∀ k : ℤ, |k| ≤ fc → fourierCoeff ν k = fourierCoeff x k) → ν ≠ x → tvNorm x < tvNorm ν

/-- Eq. (1.7): the two-dimensional Fourier coefficient
`y(k) = ∫ e^{-i2π⟨k,t⟩} ν(dt)`, `k = (k₁, k₂)`, of a complex measure on `𝕋²`. -/
def fourierCoeff2 (ν : ComplexMeasure (UnitAddCircle × UnitAddCircle)) (k : ℤ × ℤ) : ℂ :=
  cIntegral ν (fun t => fourier (-k.1) t.1 * fourier (-k.2) t.2)

/-- Theorem 1.3: `x` is the unique minimum total-variation solution among all real measures on
`𝕋²` (complex measures with zero imaginary part) obeying the data constraints (1.7),
`|k₁|, |k₂| ≤ f_c`. -/
def IsUniqueRealTVSolution2D (fc : ℕ) (x : ComplexMeasure (UnitAddCircle × UnitAddCircle)) :
    Prop :=
  ∀ ν : ComplexMeasure (UnitAddCircle × UnitAddCircle), ComplexMeasure.im ν = 0 →
    (∀ k : ℤ × ℤ, |k.1| ≤ fc → |k.2| ≤ fc → fourierCoeff2 ν k = fourierCoeff2 x k) →
    ν ≠ x → tvNorm x < tvNorm ν

/-- Eq. (2.1): the low-frequency trigonometric polynomial `q(t) = ∑_{k=-f_c}^{f_c} c_k e^{i2πkt}`. -/
def trigPoly (fc : ℕ) (c : ℤ → ℂ) (t : UnitAddCircle) : ℂ :=
  ∑ k ∈ Finset.Icc (-(fc : ℤ)) fc, c k * fourier k t

/-- Eq. (2.3): the interpolation kernel
`K(t) = [sin((f_c/2+1)πt) / ((f_c/2+1) sin(πt))]⁴` for `0 < t < 1`, with `K(0) = 1`. It is
written on all of `ℝ` by the same formula, with value `1` where `sin(πt) = 0`; for even `f_c` this
is the `1`-periodic extension (the square of the Fejér kernel, normalised to `K(0) = 1`). -/
def kernel (fc : ℕ) (t : ℝ) : ℝ :=
  if Real.sin (Real.pi * t) = 0 then 1
  else (Real.sin (((fc : ℝ) / 2 + 1) * Real.pi * t) /
    (((fc : ℝ) / 2 + 1) * Real.sin (Real.pi * t))) ^ 4

/-- Eq. (2.4): the dual polynomial `q(t) = ∑_{tⱼ ∈ T} αⱼ K(t - tⱼ) + βⱼ K'(t - tⱼ)`, for spike
locations `T ⊂ [0,1)` and coefficient sequences `α, β` indexed by `T`. -/
def dualPoly (fc : ℕ) (T : Finset ℝ) (α β : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑ s ∈ T, (α s * ((kernel fc (t - s) : ℝ) : ℂ) +
    β s * ((deriv (kernel fc) (t - s) : ℝ) : ℂ))

/-- Eq. (2.6): `q'(t) = ∑_{tⱼ ∈ T} αⱼ K'(t - tⱼ) + βⱼ K''(t - tⱼ)`. -/
def dualPolyDeriv (fc : ℕ) (T : Finset ℝ) (α β : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑ s ∈ T, (α s * ((deriv (kernel fc) (t - s) : ℝ) : ℂ) +
    β s * ((deriv (deriv (kernel fc)) (t - s) : ℝ) : ℂ))

/-- Eqs. (2.5)–(2.6): the coefficients `α, β` make the dual polynomial interpolate `v` on `T`
with zero derivative there: `q(t_k) = v_k` and `q'(t_k) = 0` for all `t_k ∈ T`. -/
def IsInterpCoeff (fc : ℕ) (T : Finset ℝ) (v α β : ℝ → ℂ) : Prop :=
  ∀ t ∈ T, dualPoly fc T α β t = v t ∧ dualPolyDeriv fc T α β t = 0

/-- Section 2: spike locations `T ⊂ [0,1)` viewed as points of the circle `𝕋`. -/
def circlePts (T : Finset ℝ) : Finset UnitAddCircle :=
  T.image (fun t : ℝ => (t : UnitAddCircle))

/-- Section 1.4: the fine-grid point `t/N ∈ 𝕋` of an index `t ∈ {0, …, N-1}`. -/
def gridPt (N : ℕ) (t : Fin N) : UnitAddCircle :=
  (((t : ℕ) : ℝ) / N : ℝ)

open Classical in
/-- Corollary 1.4: the support `T = {t : x_t ≠ 0}` of a discrete signal `x ∈ ℂ^N`. -/
def gridSupport {N : ℕ} (x : Fin N → ℂ) : Finset (Fin N) :=
  Finset.univ.filter (fun t => x t ≠ 0)

/-- Eq. (1.9): the low-frequency data `(F_n x)_k = ∑_{t=0}^{N-1} x_t e^{-i2πkt/N}` of a discrete
signal (used for `|k| ≤ f_c`). -/
def partialFourier {N : ℕ} (x : Fin N → ℂ) (k : ℤ) : ℂ :=
  ∑ t : Fin N, x t * Complex.exp (-(2 * Real.pi * Complex.I * k * ((t : ℕ) : ℂ) / N))

/-- The `ℓ₁` norm `‖x‖₁ = ∑_t |x_t|` of a discrete signal. -/
def l1norm {N : ℕ} (x : Fin N → ℂ) : ℝ :=
  ∑ t : Fin N, ‖x t‖

/-- Section 1.5: the low-pass projection `P_n = N⁻¹ F_n^* F_n` onto the `n = 2f_c + 1` lowest
Fourier modes: `(P_n x)_t = N⁻¹ ∑_{|k| ≤ f_c} e^{i2πkt/N} (F_n x)_k`. -/
def lowPass (N fc : ℕ) (x : Fin N → ℂ) : Fin N → ℂ :=
  fun t => (N : ℂ)⁻¹ * ∑ k ∈ Finset.Icc (-(fc : ℤ)) fc,
    Complex.exp (2 * Real.pi * Complex.I * k * ((t : ℕ) : ℂ) / N) * partialFourier x k

/-- Eq. (1.12): the super-resolution factor `SRF = N/n`, `n = 2f_c + 1`. -/
def srf (N fc : ℕ) : ℝ :=
  (N : ℝ) / (2 * fc + 1)

/-- Section 3: `P_T`, the orthogonal projector onto vectors supported on `T`:
`(P_T x)_i = x_i` for `i ∈ T` and `0` otherwise. -/
def projT {N : ℕ} (T : Finset (Fin N)) (x : Fin N → ℂ) : Fin N → ℂ :=
  fun t => if t ∈ T then x t else 0

end SuperResolution


