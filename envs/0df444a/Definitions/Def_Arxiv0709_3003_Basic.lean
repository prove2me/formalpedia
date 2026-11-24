-- Prove2me | Definitions.Def_Arxiv0709_3003_Basic
-- name    : Arxiv0709_3003_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T09:20:53.640135+00:00
-- url     : https://prove2.me/theorems/8cf7bd36-e638-4cb3-98f4-4d70c3af4cc0
-- title:
--   Gaussian random-mode model of passive coherent backscattering
-- statement:
--   Objects of the first experiment of Larose, Lobkis and Weaver (2007), Eqs. (2)-(5).
--
--   1. **Bessel function.** $J_0(x)=\frac1\pi\int_0^\pi\cos(x\sin\theta)\,d\theta$.
--   2. **One mode.** The values $(u_n(S_i),u_n(S_j),u_n(R))$ of a mode at the two sources and at the receiver form a centred Gaussian vector with covariance matrix
--   $$\begin{pmatrix}s&\rho&0\\\rho&s&0\\0&0&s\end{pmatrix},$$
--   where $s=\langle u^2\rangle>0$ is the common mean modal intensity, $\rho=\langle u_n(S_i)u_n(S_j)\rangle$, and the distant receiver is uncorrelated with both sources.
--   3. **Eq. (3).** The contribution of one mode is $\langle u_n(S_i)^2u_n(S_j)^2u_n(R)^4\rangle$. For $N$ modes, all with intensity $s$ and with source-source correlation coefficient $J_0(2\pi fr/c)$ at frequency $f$, source separation $r$ and wave speed $c$, the model mean squared correlation is
--   $$\langle C_{ij}^2\rangle(f,r)=\sum_{n=1}^N\big\langle u_n(S_i)^2u_n(S_j)^2u_n(R)^4\big\rangle,\qquad \rho=s\,J_0(2\pi fr/c).$$
--   4. **Eq. (2).** $\mathrm{CBE}_{\rm spatial}(f,r)=\langle C_{ij}^2\rangle(f,r)\big/\lim_{r'\to\infty}\langle C_{ij}^2\rangle(f,r')$.
--   5. **Band average.** $\overline{\mathrm{CBE}}(f,\Delta f,r)=\frac1{\Delta f}\int_{f-\Delta f/2}^{f+\Delta f/2}\mathrm{CBE}_{\rm spatial}(f',r)\,df'$.
--
--   **Formalization Note** The paper writes $\langle u_n(S_i)u_n(S_j)\rangle=J_0(2\pi fr/c)$ and keeps $\langle u^2\rangle$ general. These agree only if $\langle u^2\rangle=1$. The definitions read $J_0$ as the correlation coefficient, so the covariance is $\langle u^2\rangle J_0$; for $\langle u^2\rangle=1$ this is the paper's literal statement. The denominator $\langle C_{ij}^2(r\gg\lambda)\rangle$ of Eq. (2) is the limit as $r\to\infty$. The Lean name of $\Delta f$ is `bw`.
-- source:
--   Larose, Lobkis and Weaver, Coherent backscattering of ultrasound without a source, arXiv:0709.3003v1 (2007), first experiment, Eqs. (2)-(5), PDF pp. 3-4

import Mathlib

/-!
Larose, Lobkis and Weaver, *Coherent backscattering of ultrasound without a source*,
arXiv:0709.3003v1 (2007): the Gaussian random-mode model of the first experiment
(Eqs. (2)-(5), PDF pp. 3-4) behind the passive spatial coherent backscattering enhancement.
-/

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace Arxiv0709_3003

/-- The Bessel function of the first kind of order zero, `J_0(x) = (1/π) ∫_0^π cos(x sin θ) dθ`
(Bessel's integral). The paper uses `J_0` as the spatial correlation of the modes
(first experiment, text after Eq. (3), PDF p. 4) without defining it. -/
def besselJ0 (x : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, Real.cos (x * Real.sin θ)

/-- Covariance matrix of one mode `u_n` sampled at the two sources and at the receiver,
coordinates `0 ↦ u_n(S_i)`, `1 ↦ u_n(S_j)`, `2 ↦ u_n(R)` (text after Eq. (3), PDF p. 4):
every coordinate has mean intensity `⟨u²⟩ = s`, the two sources have covariance
`⟨u_n(S_i) u_n(S_j)⟩ = ρ`, and the distant receiver is uncorrelated with both sources,
`⟨u_n(R) u_n(S_i)⟩ = ⟨u_n(R) u_n(S_j)⟩ = 0`. -/
def modeCov (s ρ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![s, ρ, 0; ρ, s, 0; 0, 0, s]

/-- The law of one mode `(u_n(S_i), u_n(S_j), u_n(R))`: a centred Gaussian vector ("the modes are
random gaussian variables", text after Eq. (3), PDF p. 4) with covariance `modeCov s ρ`. -/
def modeLaw (s ρ : ℝ) : Measure (EuclideanSpace ℝ (Fin 3)) :=
  multivariateGaussian 0 (modeCov s ρ)

/-- The ensemble average `⟨u_n(S_i)² u_n(S_j)² u_n(R)⁴⟩` of the contribution of one mode to
Eq. (3) (PDF p. 3), for a mode with law `modeLaw s ρ`. -/
def modeTerm (s ρ : ℝ) : ℝ :=
  ∫ x, x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 4 ∂(modeLaw s ρ)

/-- The model mean squared correlation `⟨C_ij²⟩` of Eq. (3) (PDF p. 3) at frequency `f` and source
separation `r`, for `N` modes each of mean intensity `s`, whose source-source correlation is
`J_0(2π f r / c)` (text after Eq. (3), PDF p. 4), read as the correlation coefficient, i.e.
covariance `s · J_0(2π f r / c)`; `c` is the wave speed. -/
def meanSqCorr (N : ℕ) (s c f r : ℝ) : ℝ :=
  ∑ _n : Fin N, modeTerm s (s * besselJ0 (2 * Real.pi * f * r / c))

/-- Eq. (2) (PDF p. 3), in the model at frequency `f`: the spatial enhancement
`CBE_spatial(r) = ⟨C_ij²(r)⟩ / ⟨C_ij²(r ≫ λ)⟩`, the denominator being the limit of
`⟨C_ij²(r')⟩` as `r' → ∞`. -/
def cbeSpatial (N : ℕ) (s c f r : ℝ) : ℝ :=
  meanSqCorr N s c f r / limUnder atTop (fun r' => meanSqCorr N s c f r')

/-- The normalized CBE averaged over the frequency band `[f - bw/2, f + bw/2]` of width `bw = Δf`
(text before Eq. (5), PDF p. 4): `(1/bw) ∫_{f-bw/2}^{f+bw/2} CBE_spatial(r) at f' df'`. -/
def cbeBandAvg (N : ℕ) (s c f bw r : ℝ) : ℝ :=
  (1 / bw) * ∫ f' in (f - bw / 2)..(f + bw / 2), cbeSpatial N s c f' r

end Arxiv0709_3003


