-- Prove2me | Definitions.Def_Arxivcond_mat_0004049_Basic
-- name    : Arxivcond_mat_0004049_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T20:08:39.845806+00:00
-- url     : https://prove2.me/theorems/5edf78a8-3ad0-5f06-b103-8b96227a1d2d
-- title:
--   Localized-regime random-matrix model of single-mode delay times: Laguerre ensemble, spectral moments and the distributions of eqs. (13)-(20)
-- statement:
--   Objects of Schomerus, van Bemmel and Beenakker (2000), eqs. (1)-(20).
--
--   1. **Localized-regime model (pp. 1-2).** For $N\ge1$ modes and $\gamma>0$, the sample is $\omega=(g,v,\mu)$ with three independent parts. $g$ and $v$ are complex Gaussian vectors in $\mathbb{C}^N$ with independent circular entries of variance $\langle|g_i|^2\rangle=\langle|v_i|^2\rangle=1/N$. The rates $\mu=(\mu_1,\dots,\mu_N)$ follow the Laguerre ensemble, eq. (7): the probability density proportional to $\prod_{i<j}|\mu_i-\mu_j|\prod_k\Theta(\mu_k)e^{-\gamma(N+1)\mu_k}$ on $\mathbb{R}^N$.
--   2. **Observables.** The incident-mode column of the Haar-distributed unitary $U$ is $u=g/\|g\|_2$ (uniform on the unit sphere of $\mathbb{C}^N$). For $n\ne m$ the detected-mode column is $v$, in the large-$N$ Gaussian form of p. 2. The Wigner-Smith delay times are $\tau_i=1/\mu_i$. Eq. (6): $A_k=\sum_i\tau_i^ku_iv_i$, $\varphi'=\mathrm{Re}\,A_1/A_0$, $I=|A_0|^2$ ($n\ne m$). Eq. (19): $C_k=\sum_i\tau_i^ku_i^2$, $\varphi'=\mathrm{Re}\,C_1/C_0$, $I=|C_0|^2$ ($n=m$). Eq. (11): $B_k=\sum_i|u_i|^2\tau_i^k$.
--   3. **Closed forms.** Eq. (13): $K_{13}(B_1,B_2;I,\varphi')=\Theta(I)(N^3I/\pi)^{1/2}e^{-NI}(B_2-B_1^2)^{-1/2}\exp\!\big(-NI(\varphi'-B_1)^2/(B_2-B_1^2)\big)$. Eq. (16): $K_{16}(B_1,B_2;\varphi')=(B_2-B_1^2)/\big(2(B_2+\varphi'^2-2B_1\varphi')^{3/2}\big)$. Eq. (15): $P(B_1,B_2)=\Theta(B_1)\Theta(B_2)e^{-NB_1^2/B_2}\big[\frac{B_1^2\gamma N^3}{B_2^4}(B_2+\gamma N^2B_1)e^{-2\gamma N/B_1}-\frac{\gamma^3N^5}{4B_2^5}(2B_2^2-4B_1^2B_2N+B_1^4N^2)\,\mathrm{Ei}(-2\gamma N/B_1)\big]$ with $\mathrm{Ei}(x)=-\int_{-x}^\infty e^{-t}t^{-1}\,dt$ for $x<0$. Eq. (17): $P_{\rm diff}(\varphi')=(Q/2\bar\varphi')[Q+(\varphi'/\bar\varphi'-1)^2]^{-3/2}$. Eq. (20) at leading order in $N$, in the variables $c_0=N^{1/2}C_0$, $c_1=C_1/(\gamma N)$: the weight $w(c_0,c_1)=e^{-|c_0|^2/2}\int_0^\infty x^2e^{-x}(1+|c_1|^2x^2)^{-5/2}\,dx$.
--   4. **Convergence in law.** For observables $X_N$ of the model with parameter $\gamma$, "$X_N\to\rho$ in law" means $E_N f(X_N)\to\int f\,d\rho$ for every bounded continuous $f$.
--
--   **Formalization Note** The paper takes $u$ and $v$ to be columns of a Haar unitary and replaces them, for large $N$, by independent Gaussian vectors. The model keeps $u$ exactly on the unit sphere, as eq. (12) requires ($\sum_i|u_i|^2=1$), and uses the Gaussian form for $v$. $\Theta(0)$, which the paper leaves undefined, is taken as $0$; this only changes the densities on a null set.
-- source:
--   H. Schomerus, K. J. H. van Bemmel and C. W. J. Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), pp. 1-3: eqs. (5)-(7) (model and Laguerre ensemble), (11) (spectral moments), (13), (15)-(17), (19)-(20)

import Mathlib

/-!
H. Schomerus, K. J. H. van Bemmel and C. W. J. Beenakker, *Coherent backscattering effect on wave
dynamics in a random medium*, arXiv:cond-mat/0004049v1 (2000): the random-matrix model of
single-mode delay times in reflection from a disordered waveguide in the localized regime
(eqs. (5)-(7), (11), (19)), and the closed-form distributions of eqs. (13), (15)-(17), (20).
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxivcond_mat_0004049

/-- The complex Gaussian vector of p. 2 ("independent Gaussian random numbers with vanishing mean
and variance `N⁻¹`"): `N` independent circular complex Gaussian entries with `E|z_i|² = 1/N`, i.e.
real and imaginary parts independent `N(0, 1/(2N))`. -/
def gaussVec (N : ℕ) : Measure (Fin N → ℂ) :=
  (Measure.pi fun _ : Fin N =>
      (gaussianReal 0 ((N : NNReal)⁻¹ / 2)).prod (gaussianReal 0 ((N : NNReal)⁻¹ / 2))).map
    (fun x i => Complex.measurableEquivRealProd.symm (x i))

/-- The unnormalised weight of the Laguerre ensemble, eq. (7), for the rates `μ_i = 1/τ_i`:
`∏_{i<j} |μ_i - μ_j| ∏_k Θ(μ_k) exp(-γ (N+1) μ_k)`. -/
def laguerreWeight (N : ℕ) (γ : ℝ) (μ : Fin N → ℝ) : ENNReal :=
  ENNReal.ofReal ((∏ i, ∏ j, if i < j then |μ i - μ j| else 1) *
    ∏ k, if 0 < μ k then Real.exp (-γ * ((N : ℝ) + 1) * μ k) else 0)

/-- The Laguerre ensemble, eq. (7): the probability law of the rates `μ_1, …, μ_N` with density
proportional to `laguerreWeight` with respect to Lebesgue measure on `ℝ^N`. -/
def laguerreEnsemble (N : ℕ) (γ : ℝ) : Measure (Fin N → ℝ) :=
  (∫⁻ μ, laguerreWeight N γ μ)⁻¹ • (volume : Measure (Fin N → ℝ)).withDensity (laguerreWeight N γ)

/-- The sample space of the localized-regime model: `ω = (g, v, μ)`, where `g` generates the
incident-mode column `u` of `U`, `v` is the detected-mode column, and `μ` are the rates. -/
abbrev Sample (N : ℕ) : Type := (Fin N → ℂ) × (Fin N → ℂ) × (Fin N → ℝ)

/-- The localized-regime model of pp. 1-2: `g` and `v` independent complex Gaussian vectors
(`gaussVec N`), independent of the rates `μ` drawn from the Laguerre ensemble (eq. (7)). -/
def localizedModel (N : ℕ) (γ : ℝ) : Measure (Sample N) :=
  (gaussVec N).prod ((gaussVec N).prod (laguerreEnsemble N γ))

/-- The column `u_i = U_{im}` of the matrix `U`, uniformly distributed in the unitary group
(p. 2): `u = g / ‖g‖₂`, which for a complex Gaussian `g` is uniform on the unit sphere of `ℂ^N`,
the law of a column of a Haar-distributed unitary matrix. -/
def uVec {N : ℕ} (ω : Sample N) : Fin N → ℂ :=
  fun i => ω.1 i / ((Real.sqrt (∑ j, Complex.normSq (ω.1 j)) : ℝ) : ℂ)

/-- The detected-mode column `v_i = U_{in}` for `n ≠ m`, in the large-`N` Gaussian form of p. 2. -/
def vVec {N : ℕ} (ω : Sample N) : Fin N → ℂ := ω.2.1

/-- The Wigner-Smith delay times `τ_i = 1/μ_i` (eqs. (4), (7)). -/
def tau {N : ℕ} (ω : Sample N) : Fin N → ℝ := fun i => (ω.2.2 i)⁻¹

/-- Eq. (6): `A_k = ∑_i τ_i^k u_i v_i` (different incident and detected modes, `n ≠ m`). -/
def ampA {N : ℕ} (k : ℕ) (ω : Sample N) : ℂ :=
  ∑ i, ((tau ω i : ℂ)) ^ k * uVec ω i * vVec ω i

/-- Eq. (19): `C_k = ∑_i τ_i^k u_i²` (equal incident and detected modes, `n = m`). -/
def ampC {N : ℕ} (k : ℕ) (ω : Sample N) : ℂ :=
  ∑ i, ((tau ω i : ℂ)) ^ k * uVec ω i ^ 2

/-- Eq. (11): the spectral moments `B_k = ∑_i |u_i|² τ_i^k`. -/
def specMoment {N : ℕ} (k : ℕ) (ω : Sample N) : ℝ :=
  ∑ i, Complex.normSq (uVec ω i) * tau ω i ^ k

/-- Eq. (6): the single-mode delay time `φ' = Re (A_1/A_0)` for `n ≠ m`. -/
def delayNe {N : ℕ} (ω : Sample N) : ℝ := (ampA 1 ω / ampA 0 ω).re

/-- Eq. (6): the reflected intensity `I = |A_0|²` for `n ≠ m`. -/
def intensityNe {N : ℕ} (ω : Sample N) : ℝ := Complex.normSq (ampA 0 ω)

/-- Eq. (19): the single-mode delay time `φ' = Re (C_1/C_0)` for `n = m`. -/
def delayEq {N : ℕ} (ω : Sample N) : ℝ := (ampC 1 ω / ampC 0 ω).re

/-- Eq. (19): the reflected intensity `I = |C_0|²` for `n = m`. -/
def intensityEq {N : ℕ} (ω : Sample N) : ℝ := Complex.normSq (ampC 0 ω)

/-- The integrand of eq. (13): `Θ(I) (N³ I/π)^{1/2} e^{-NI} (B_2 - B_1²)^{-1/2}
exp(-N I (φ' - B_1)²/(B_2 - B_1²))`. -/
def eq13Kernel (N : ℕ) (B1 B2 I φ : ℝ) : ℝ :=
  if 0 < I then
    Real.sqrt ((N : ℝ) ^ 3 * I / Real.pi) * Real.exp (-(N : ℝ) * I) *
      (Real.sqrt (B2 - B1 ^ 2))⁻¹ * Real.exp (-(N : ℝ) * I * (φ - B1) ^ 2 / (B2 - B1 ^ 2))
  else 0

/-- The integrand of eq. (16): `(B_2 - B_1²) / (2 (B_2 + φ'² - 2 B_1 φ')^{3/2})`. -/
def eq16Kernel (B1 B2 φ : ℝ) : ℝ :=
  (B2 - B1 ^ 2) / (2 * (B2 + φ ^ 2 - 2 * B1 * φ) ^ ((3 : ℝ) / 2))

/-- The exponential integral `Ei(x) = -∫_{-x}^∞ e^{-t}/t dt` for `x < 0` (used in eq. (15) only at
negative arguments; for `x ≥ 0` the integral is not convergent and the value is a junk value). -/
def expIntegralEi (x : ℝ) : ℝ := -∫ t in Set.Ioi (-x), Real.exp (-t) / t

/-- Eq. (15): the joint density of the spectral moments `B_1, B_2` (for `n ≠ m`, large `N`),
`Θ(B_1)Θ(B_2) e^{-N B_1²/B_2} [ (B_1² γ N³/B_2⁴)(B_2 + γ N² B_1) e^{-2γN/B_1}
 - (γ³ N⁵/(4 B_2⁵))(2 B_2² - 4 B_1² B_2 N + B_1⁴ N²) Ei(-2γN/B_1) ]`. -/
def eq15Density (N : ℕ) (γ B1 B2 : ℝ) : ℝ :=
  if 0 < B1 ∧ 0 < B2 then
    Real.exp (-(N : ℝ) * B1 ^ 2 / B2) *
      (B1 ^ 2 * γ * (N : ℝ) ^ 3 / B2 ^ 4 * (B2 + γ * (N : ℝ) ^ 2 * B1) *
          Real.exp (-2 * γ * (N : ℝ) / B1) -
        γ ^ 3 * (N : ℝ) ^ 5 / (4 * B2 ^ 5) *
          (2 * B2 ^ 2 - 4 * B1 ^ 2 * B2 * (N : ℝ) + B1 ^ 4 * (N : ℝ) ^ 2) *
          expIntegralEi (-2 * γ * (N : ℝ) / B1))
  else 0

/-- Eq. (17): the diffusion-theory distribution of the single-mode delay time,
`P_diff(φ') = (Q/2φ̄') [Q + (φ'/φ̄' - 1)²]^{-3/2}`, with parameters `Q`, `φ̄'` (`phibar`). -/
def pDiff (Q phibar φ : ℝ) : ℝ :=
  Q / (2 * phibar) * (Q + (φ / phibar - 1) ^ 2) ^ (-(3 : ℝ) / 2)

/-- Eq. (20) at leading order in `N`, in the rescaled variables `c_0 = N^{1/2} C_0`,
`c_1 = C_1/(γN)`: the unnormalised weight `exp(-|c_0|²/2) ∫_0^∞ x² e^{-x} (1 + |c_1|² x²)^{-5/2} dx`
(the cross term `(2x/γN) Re C_0 C_1^*` of eq. (20) equals `2x Re(c_0 c̄_1)/N^{1/2}`). -/
def eq20LimitWeight (c0 c1 : ℂ) : ℝ :=
  Real.exp (-‖c0‖ ^ 2 / 2) *
    ∫ x in Set.Ioi (0 : ℝ), x ^ 2 * Real.exp (-x) * (1 + ‖c1‖ ^ 2 * x ^ 2) ^ (-(5 : ℝ) / 2)

/-- Convergence in distribution as `N → ∞` in the localized-regime model: the laws of the
observables `X N` under `localizedModel N γ` converge weakly to `ρ`, i.e. `E_N f(X_N) → ∫ f dρ`
for every bounded continuous `f`. -/
def LawTendsto {E : Type*} [TopologicalSpace E] [MeasurableSpace E] (γ : ℝ)
    (X : ∀ N : ℕ, Sample N → E) (ρ : Measure E) : Prop :=
  ∀ f : BoundedContinuousFunction E ℝ,
    Filter.Tendsto (fun N => ∫ ω, f (X N ω) ∂(localizedModel N γ)) Filter.atTop
      (nhds (∫ x, f x ∂ρ))

end Arxivcond_mat_0004049


