-- Prove2me | Definitions.Def_SphereGRF_HeatEq_Setting
-- name    : SphereGRF_HeatEq_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:04.720261+00:00
-- url     : https://prove2.me/theorems/a9052a91-0fb5-4630-b6de-6a59bb60b69d
-- title:
--   §2, §7, pp. 4–5, 33–39 — spherical harmonics, the spectral solution X(t) = Σ X_ℓ(t) of the stochastic heat equation (2) and its truncation X^κ
-- statement:
--   This file sets up the objects of §7 of Lang–Schwab: the stochastic heat equation on the unit sphere driven by an isotropic $Q$-Wiener process, its spectral solution and the truncated approximation.
--
--   **Sphere, measure, norms.** $\mathbb S^2\subset\mathbb R^3$ is the unit sphere and $\sigma$ its surface measure, of total mass $4\pi$ (so $d\sigma=\sin\vartheta\,d\vartheta\,d\varphi$). For $f:\mathbb S^2\to\mathbb R$,
--   $$\|f\|^2_{L^2(\mathbb S^2)}=\int_{\mathbb S^2}|f(y)|^2\,d\sigma(y),$$
--   and for a random field $Z$ on a probability space $(\Omega,\mathcal A,\mathbb P)$ and $p>0$,
--   $$\|Z\|_{L^p(\Omega;L^2(\mathbb S^2))}=\Big(\mathbb E\,\|Z\|^p_{L^2(\mathbb S^2)}\Big)^{1/p}.$$
--   Both are computed as extended nonnegative reals, so they may equal $+\infty$.
--
--   **Spherical harmonics (p. 4).** $P_\ell(\mu)=2^{-\ell}(\ell!)^{-1}\frac{d^\ell}{d\mu^\ell}(\mu^2-1)^\ell$ is the Legendre polynomial. For $0\le m\le\ell$ the real and imaginary parts of the spherical harmonic
--   $$Y_{\ell m}=\sqrt{\tfrac{2\ell+1}{4\pi}\tfrac{(\ell-m)!}{(\ell+m)!}}\,P_{\ell m}(\cos\vartheta)e^{im\varphi},\qquad P_{\ell m}(\mu)=(-1)^m(1-\mu^2)^{m/2}P_\ell^{(m)}(\mu),$$
--   are written in Cartesian coordinates $y=(y_1,y_2,y_3)$:
--   $$\operatorname{Re}Y_{\ell m}(y)=c_{\ell m}(-1)^mP_\ell^{(m)}(y_3)\operatorname{Re}\big((y_1+iy_2)^m\big),\qquad \operatorname{Im}Y_{\ell m}(y)=c_{\ell m}(-1)^mP_\ell^{(m)}(y_3)\operatorname{Im}\big((y_1+iy_2)^m\big),$$
--   with $c_{\ell m}$ the normalising square root. The real orthonormal basis of the degree-$\ell$ harmonics consists of $Y_{\ell0}$ and $\sqrt2\operatorname{Re}Y_{\ell m}$, $\sqrt2\operatorname{Im}Y_{\ell m}$ for $1\le m\le\ell$.
--
--   **Noise and the stochastic convolution (pp. 33–36).** The $Q$-Wiener process is driven by independent real Brownian motions $\beta^i_{\ell m}$, $\ell\ge0$, $0\le m\le\ell$, $i=1,2$, with angular power spectrum $(A_\ell)$. For $r\in\mathbb R$ and a path $b$ with $b(0)=0$ the stochastic convolution is written pathwise as
--   $$\int_0^te^{-r(t-s)}\,db(s)=b(t)-r\int_0^te^{-r(t-s)}b(s)\,ds .$$
--
--   **The solution (p. 36) and its truncation (p. 39).** With $\lambda_\ell=\ell(\ell+1)$ (the eigenvalue of $-\Delta_{\mathbb S^2}$ on degree-$\ell$ harmonics), the $\ell$-th mode of the solution is
--   $$X_\ell(t)=\sum_{m=-\ell}^{\ell}e^{-\lambda_\ell t}(X_0,Y_{\ell m})Y_{\ell m}+\sqrt{A_\ell}\Big(\int_0^te^{-\lambda_\ell(t-s)}d\beta^1_{\ell0}(s)\,Y_{\ell0}+\sqrt2\sum_{m=1}^{\ell}\Big(\int_0^te^{-\lambda_\ell(t-s)}d\beta^1_{\ell m}(s)\operatorname{Re}Y_{\ell m}+\int_0^te^{-\lambda_\ell(t-s)}d\beta^2_{\ell m}(s)\operatorname{Im}Y_{\ell m}\Big)\Big),$$
--   the approximation is $X^\kappa(t)=\sum_{\ell=0}^{\kappa}X_\ell(t)$, and the solution is $X(t)=\lim_{\kappa\to\infty}X^\kappa(t)$, the limit taken pointwise in $(\omega,y)$.
--
--   These are the objects about which Lemmas 7.1, 7.2 and Corollary 7.3 make their error statements.
--
--   **Formalization Note.** (1) The harmonics are written in Cartesian form: for $y=(\sin\vartheta\cos\varphi,\sin\vartheta\sin\varphi,\cos\vartheta)$ one has $(y_1+iy_2)^m=\sin^m\vartheta\,e^{im\varphi}$ and $(1-\cos^2\vartheta)^{m/2}=\sin^m\vartheta$, so $P_{\ell m}(\cos\vartheta)e^{im\varphi}=(-1)^mP_\ell^{(m)}(y_3)(y_1+iy_2)^m$; this is the paper's function, also at the poles. Lean's coordinates are 0-based. (2) For real $X_0$, $\sum_{m=-\ell}^{\ell}(X_0,Y_{\ell m})Y_{\ell m}$ equals the expansion of $X_0$ in the real basis above; the file uses the real form, with coefficients $\int X_0\,u\,d\sigma$. (3) The stochastic convolution is replaced by its pathwise form: for a Brownian path (continuous, $b(0)=0$ almost surely) Itô's product rule applied to the deterministic $C^1$ integrand $s\mapsto e^{-r(t-s)}$ gives exactly this identity almost surely; this is the one place where a stochastic integral is replaced. For $r=0$ ($\ell=0$) it is $b(t)$, as on p. 37. (4) The infinite sum $X(t)$ is a pointwise limit (`limUnder`); where the partial sums diverge the value is an unspecified junk value, which for $t>0$ only happens on a $\mathbb P\otimes\sigma$-null set and is invisible to the norms. (5) The Laplace–Beltrami operator is not defined: the mission takes the paper's spectral solution formula of p. 36 as the definition of $X$. Brownian motions are Mathlib's `IsBrownianReal` processes indexed by $\mathbb R_{\ge0}$, and $\beta^1,\beta^2$ are indices $i=0,1$.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, §2 pp. 4–5 (Legendre polynomials, spherical harmonics, dσ); §7 pp. 33–34 (Q-Wiener process), p. 35 (equation (2)), p. 36 (solution formula, display (3)), p. 39 (X^κ)

import Mathlib
import Definitions.Def_SphereGRF_Spectral_Legendre

namespace SphereGRF.HeatEq

open MeasureTheory Filter
open scoped ENNReal NNReal

/-- The unit sphere `S² ⊂ ℝ³`. Coordinate `i : Fin 3` of a point `y` (0-based) is the paper's `y_{i+1}`. -/
abbrev S2 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The surface measure `σ` on `S²` (total mass `4π`), `dσ = sin ϑ dϑ dφ` (p. 5). -/
noncomputable def sigma : Measure S2 :=
  (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere

/-- Normalising constant `√((2ℓ+1)/(4π) · (ℓ-m)!/(ℓ+m)!)` of `Y_ℓm` (p. 4), used for `m ≤ ℓ`. -/
noncomputable def shNorm (ℓ m : ℕ) : ℝ :=
  Real.sqrt ((2 * ℓ + 1) / (4 * Real.pi) * (ℓ - m).factorial / (ℓ + m).factorial)

/-- `Re Y_ℓm` for `0 ≤ m ≤ ℓ`, in Cartesian form:
`shNorm ℓ m · (-1)^m · P_ℓ^{(m)}(y₃) · Re((y₁ + i y₂)^m)` (= `L_ℓm(ϑ) cos(mφ)`). -/
noncomputable def shC (ℓ m : ℕ) (y : S2) : ℝ :=
  shNorm ℓ m * (-1) ^ m *
    (Polynomial.derivative^[m] (SphereGRF.Spectral.legendreP ℓ)).eval ((y : EuclideanSpace ℝ (Fin 3)) 2) *
    (((y : EuclideanSpace ℝ (Fin 3)) 0 + Complex.I * (y : EuclideanSpace ℝ (Fin 3)) 1) ^ m).re

/-- `Im Y_ℓm` for `0 ≤ m ≤ ℓ`, in Cartesian form (= `L_ℓm(ϑ) sin(mφ)`). -/
noncomputable def shS (ℓ m : ℕ) (y : S2) : ℝ :=
  shNorm ℓ m * (-1) ^ m *
    (Polynomial.derivative^[m] (SphereGRF.Spectral.legendreP ℓ)).eval ((y : EuclideanSpace ℝ (Fin 3)) 2) *
    (((y : EuclideanSpace ℝ (Fin 3)) 0 + Complex.I * (y : EuclideanSpace ℝ (Fin 3)) 1) ^ m).im

/-- The real orthonormal basis of the degree-`ℓ` spherical harmonics:
`Y_ℓ0` for `m = 0, i = 0`; `√2 Re Y_ℓm` (`i = 0`) and `√2 Im Y_ℓm` (`i = 1`) for `1 ≤ m ≤ ℓ`; `0` otherwise. -/
noncomputable def realSH (ℓ m : ℕ) (i : Fin 2) (y : S2) : ℝ :=
  if m = 0 then (if i = 0 then shC ℓ 0 y else 0)
  else if m ≤ ℓ then (if i = 0 then Real.sqrt 2 * shC ℓ m y else Real.sqrt 2 * shS ℓ m y)
  else 0

/-- Squared `L²(S²)` norm `‖f‖²_{L²(S²)} = ∫ |f|² dσ`, in `ℝ≥0∞`. -/
noncomputable def l2S2Sq (f : S2 → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ‖f y‖ₑ ^ 2 ∂sigma

/-- `‖Z‖_{L^p(Ω; L²(S²))} = (E ‖Z‖^p_{L²(S²)})^{1/p}`, in `ℝ≥0∞` (a quasi-norm for `p < 1`). -/
noncomputable def lpL2Norm {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p : ℝ)
    (Z : Ω → S2 → ℝ) : ℝ≥0∞ :=
  (∫⁻ ω, l2S2Sq (Z ω) ^ (p / 2) ∂P) ^ (1 / p)

/-- The eigenvalue `ℓ(ℓ+1)` of `-Δ_{S²}` on the degree-`ℓ` harmonics (p. 5). -/
def lam (ℓ : ℕ) : ℝ := ℓ * (ℓ + 1)

/-- Pathwise form of the stochastic convolution `∫₀ᵗ e^{-r(t-s)} db(s)`:
`b(t) - r ∫₀ᵗ e^{-r(t-s)} b(s) ds` (integration by parts, valid when `b(0) = 0`). -/
noncomputable def ouConv (r : ℝ) (b : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  b t - r * ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-r * ((t : ℝ) - s)) * b s.toNNReal

/-- The real coefficient `∫_{S²} X₀(ω, y) · realSH ℓ m i (y) dσ(y)` of the initial condition. -/
noncomputable def coef {Ω : Type*} (X₀ : Ω → S2 → ℝ) (ω : Ω) (ℓ m : ℕ) (i : Fin 2) : ℝ :=
  ∫ y, X₀ ω y * realSH ℓ m i y ∂sigma

/-- The `ℓ`-th mode `X_ℓ(t)` of the solution of the stochastic heat equation (p. 36):
`e^{-ℓ(ℓ+1)t} Σ_{m,i} coef · realSH + √A_ℓ (OU_{ℓ00}(t) Y_ℓ0
 + √2 Σ_{m=1}^ℓ (OU_{ℓm0}(t) Re Y_ℓm + OU_{ℓm1}(t) Im Y_ℓm))`. -/
noncomputable def heatMode {Ω : Type*} (A : ℕ → ℝ) (B : ℕ → ℕ → Fin 2 → ℝ≥0 → Ω → ℝ)
    (X₀ : Ω → S2 → ℝ) (ℓ : ℕ) (t : ℝ≥0) (ω : Ω) (y : S2) : ℝ :=
  Real.exp (-lam ℓ * t) *
      ∑ m ∈ Finset.range (ℓ + 1), ∑ i : Fin 2, coef X₀ ω ℓ m i * realSH ℓ m i y
    + Real.sqrt (A ℓ) *
      (ouConv (lam ℓ) (fun s => B ℓ 0 0 s ω) t * shC ℓ 0 y
        + Real.sqrt 2 * ∑ m ∈ Finset.Icc 1 ℓ,
            (ouConv (lam ℓ) (fun s => B ℓ m 0 s ω) t * shC ℓ m y
              + ouConv (lam ℓ) (fun s => B ℓ m 1 s ω) t * shS ℓ m y))

/-- The spectral approximation `X^κ(t) = Σ_{ℓ=0}^κ X_ℓ(t)` (p. 39). -/
noncomputable def heatTrunc {Ω : Type*} (A : ℕ → ℝ) (B : ℕ → ℕ → Fin 2 → ℝ≥0 → Ω → ℝ)
    (X₀ : Ω → S2 → ℝ) (κ : ℕ) (t : ℝ≥0) (ω : Ω) (y : S2) : ℝ :=
  ∑ ℓ ∈ Finset.range (κ + 1), heatMode A B X₀ ℓ t ω y

/-- The solution `X(t) = Σ_{ℓ=0}^∞ X_ℓ(t)` of the stochastic heat equation (2), as the pointwise limit
of the partial sums (junk value where they diverge). -/
noncomputable def heatSol {Ω : Type*} (A : ℕ → ℝ) (B : ℕ → ℕ → Fin 2 → ℝ≥0 → Ω → ℝ)
    (X₀ : Ω → S2 → ℝ) (t : ℝ≥0) (ω : Ω) (y : S2) : ℝ :=
  limUnder atTop (fun κ : ℕ => heatTrunc A B X₀ κ t ω y)

end SphereGRF.HeatEq


