-- Prove2me | Definitions.Def_SpikedWishart_SoftEdge_Kernels
-- name    : SpikedWishart_SoftEdge_Kernels
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T05:39:12.671179+00:00
-- url     : https://prove2.me/theorems/ebe549a3-bdbd-41b8-a7e2-11b0033bf365
-- title:
--   §2–§3, pp. 1655–1663 — K_{M,N} (62), the density (61), µ, ν, p_c, f, g, q, 𝓗, 𝓙, Z_M, 𝓗∞, 𝓙∞
-- statement:
--   This file defines the auxiliary objects of the proof of Theorem 1.1(a) that the milestones refer to. Throughout, $\pi_j=\ell_j^{-1}$ and contours are counterclockwise circles $C(c,\rho)$ with real centre $c$ and radius $\rho$.
--
--   1. The **finite-$N$ kernel** (62): for $0<q$, a circle $\Gamma$ and a circle $\Sigma$,
--   $$
--   K_{M,N}(\eta,\zeta)=\frac{M}{(2\pi i)^2}\oint_\Gamma dz\oint_\Sigma dw\; e^{-\eta M(z-q)+\zeta M(w-q)}\frac{1}{w-z}\Big(\frac zw\Big)^M\prod_{k=1}^N\frac{\pi_k-w}{\pi_k-z}.
--   $$
--   2. The **unnormalised eigenvalue density** (61): $\dfrac{\det(e^{-M\pi_j\lambda_k})_{j,k}}{V(\pi)}\,V(\lambda)\prod_j\lambda_j^{M-N}$, with $V(x)=\prod_{i<j}(x_j-x_i)$.
--   3. The scaling constants (101), (105): $\mu=\big(\frac{1+\gamma}{\gamma}\big)^2$, $\nu=\frac{(1+\gamma)^{4/3}}{\gamma}$, $p_c=\frac{\gamma}{\gamma+1}$.
--   4. The phase function (106), $f(z)=-\mu(z-q)+\log z-\frac1{\gamma^2}\log(1-z)$ with the principal branch of $\log$, and (107), $g(z)=\frac1{(1-z)^r}\prod_{\ell=k+1}^r(\pi_\ell-z)$.
--   5. $q=p_c-\dfrac{\varepsilon}{\nu M^{1/3}}$ (118) and $Z_M=\dfrac{g(p_c)}{(-\nu M^{1/3})^k e^{Mf(p_c)}}$ (116).
--   6. The rescaled functions (103)–(104):
--   $$
--   \mathcal H(u)=\frac{\nu M^{1/3}}{2\pi}\oint_\Gamma e^{-\nu M^{1/3}u(z-q)}e^{Mf(z)}\frac{dz}{(p_c-z)^kg(z)},\qquad
--   \mathcal J(v)=\frac{\nu M^{1/3}}{2\pi}\oint_\Sigma e^{\nu M^{1/3}v(z-q)}e^{-Mf(z)}(p_c-z)^kg(z)\,dz .
--   $$
--   7. Their limits (120), (122):
--   $$
--   \mathcal H_\infty(u)=\frac{e^{-\varepsilon u}}{2\pi}\int_{\Gamma_\infty}e^{-ua+\frac13a^3}\frac{da}{a^k},\qquad
--   \mathcal J_\infty(v)=\frac{e^{\varepsilon v}}{2\pi}\int_{\Sigma_\infty}e^{va-\frac13a^3}a^k\,da,
--   $$
--   where $\Gamma_\infty$ comes in from $\infty e^{i\pi/3}$ to a real vertex and goes out to $\infty e^{-i\pi/3}$, and $\Sigma_\infty$ comes in from $\infty e^{-2i\pi/3}$ to a real vertex and goes out to $\infty e^{2i\pi/3}$.
--
--   These are the ingredients of Proposition 2.1 (the exact Fredholm formula at finite $M,N$) and of the steepest-descent analysis (Lemmas 3.1–3.2, Proposition 3.1, (200)).
--
--   **Formalization Note** The paper's contours $\Gamma,\Sigma$ of §2 are arbitrary simple closed curves; they are encoded as circles with real centres (the integrals do not depend on the choice by Cauchy's theorem, which is not stated). $K_{M,N}$ is real for real centres and its real part is taken. The ray contours $\Gamma_\infty,\Sigma_\infty$ are two-ray broken lines with a vertex that the theorems constrain. $\pi_1,\dots,\pi_r$ are indexed from $0$ and the product in $g$ runs over the indices $j\ge k$.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1655, (61), (62); pp. 1661–1663, (101), (103)–(107), (116), (118), (120), (122)

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Airy

namespace SpikedWishart.SoftEdge

open MeasureTheory Complex

/-- The finite-`N` kernel `K_{M,N}(η, ζ)` of Proposition 2.1, (62):
`M/(2πi)² ∮_Γ dz ∮_Σ dw e^{-ηM(z-q)+ζM(w-q)} (w-z)⁻¹ (z/w)^M Π_k (π_k - w)/(π_k - z)`,
with `Γ` the counterclockwise circle of centre `cΓ` and radius `ρΓ` and `Σ` the counterclockwise
circle of centre `cS` and radius `ρS`. Real part taken (the kernel is real for real centres). -/
noncomputable def kernelKMN {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (q cΓ ρΓ cS ρS : ℝ) (η ζ : ℝ) : ℝ :=
  ((M : ℂ) / (2 * (Real.pi : ℂ) * I) ^ 2 *
    ∮ z in C((cΓ : ℂ), ρΓ), ∮ w in C((cS : ℂ), ρS),
      exp (-(η : ℂ) * M * (z - q) + (ζ : ℂ) * M * (w - q)) * (1 / (w - z)) * (z / w) ^ M *
        ∏ j, (((π j : ℂ) - w) / ((π j : ℂ) - z))).re

/-- The unnormalised joint eigenvalue density (61) for distinct `π_j`:
`det(e^{-Mπ_jλ_k})_{j,k} / V(π) · V(λ) · Π_j λ_j^{M-N}`, with `V(x) = Π_{i<j} (x_j - x_i)` the
Vandermonde determinant. -/
noncomputable def eigDensity {N : ℕ} (M : ℕ) (π : Fin N → ℝ) (lam : Fin N → ℝ) : ℝ :=
  (Matrix.of fun j k => Real.exp (-(M : ℝ) * π j * lam k)).det / (Matrix.vandermonde π).det *
    (Matrix.vandermonde lam).det * ∏ j, lam j ^ (M - N)

/-- `µ(γ) = ((1 + γ)/γ)²`, (101). -/
noncomputable def mu (γ : ℝ) : ℝ := ((1 + γ) / γ) ^ 2

/-- `ν(γ) = (1 + γ)^{4/3}/γ`, (101). -/
noncomputable def nu (γ : ℝ) : ℝ := (1 + γ) ^ (4 / 3 : ℝ) / γ

/-- The critical point `p_c = γ/(γ + 1)`, (105). -/
noncomputable def pc (γ : ℝ) : ℝ := γ / (γ + 1)

/-- `f(z) = -µ(z - q) + log z - γ⁻² log(1 - z)`, (106), principal branch of `log`. -/
noncomputable def fFn (γ q : ℝ) (z : ℂ) : ℂ :=
  -(mu γ : ℂ) * (z - q) + log z - (1 / (γ : ℂ) ^ 2) * log (1 - z)

/-- `g(z) = (1 - z)^{-r} Π_{ℓ=k+1}^{r} (π_ℓ - z)`, (107); `π : Fin r → ℝ` lists `π_1, …, π_r`
(0-based), and the product runs over the indices `j` with `k ≤ j`. -/
noncomputable def gFn {r : ℕ} (k : ℕ) (π : Fin r → ℝ) (z : ℂ) : ℂ :=
  (1 / (1 - z) ^ r) * ∏ j ∈ Finset.univ.filter (fun j : Fin r => k ≤ (j : ℕ)), ((π j : ℂ) - z)

/-- `q = p_c - ε/(ν M^{1/3})`, (118). -/
noncomputable def qM (γ ε : ℝ) (M : ℕ) : ℝ := pc γ - ε / (nu γ * (M : ℝ) ^ (1 / 3 : ℝ))

/-- `𝓗(u)`, (103): `(νM^{1/3}/2π) ∮_Γ e^{-νM^{1/3}u(z-q)} e^{Mf(z)} ((p_c - z)^k g(z))⁻¹ dz`,
with `Γ` the counterclockwise circle of centre `cΓ` and radius `ρΓ`. -/
noncomputable def Hcal {r : ℕ} (γ q : ℝ) (M k : ℕ) (π : Fin r → ℝ) (cΓ ρΓ : ℝ) (u : ℝ) : ℂ :=
  ((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) / (2 * Real.pi) : ℝ) : ℂ) *
    ∮ z in C((cΓ : ℂ), ρΓ),
      exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * (z - q)) * exp ((M : ℂ) * fFn γ q z) *
        (1 / (((pc γ : ℂ) - z) ^ k * gFn k π z))

/-- `𝓙(v)`, (104): `(νM^{1/3}/2π) ∮_Σ e^{νM^{1/3}v(z-q)} e^{-Mf(z)} (p_c - z)^k g(z) dz`,
with `Σ` the counterclockwise circle of centre `cS` and radius `ρS`. -/
noncomputable def Jcal {r : ℕ} (γ q : ℝ) (M k : ℕ) (π : Fin r → ℝ) (cS ρS : ℝ) (v : ℝ) : ℂ :=
  ((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) / (2 * Real.pi) : ℝ) : ℂ) *
    ∮ z in C((cS : ℂ), ρS),
      exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (z - q)) * exp (-(M : ℂ) * fFn γ q z) *
        (((pc γ : ℂ) - z) ^ k * gFn k π z)

/-- `Z_M = g(p_c) / ((-νM^{1/3})^k e^{M f(p_c)})`, (116). -/
noncomputable def ZM {r : ℕ} (γ q : ℝ) (M k : ℕ) (π : Fin r → ℝ) : ℂ :=
  gFn k π (pc γ) /
    ((-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ)) ^ k * exp ((M : ℂ) * fFn γ q (pc γ)))

/-- `𝓗_∞(u)`, (120): `(e^{-εu}/2π) ∫_{Γ_∞} e^{-ua + a³/3} a^{-k} da`, where `Γ_∞` comes in from
`∞e^{iπ/3}` to the real vertex `c` and goes out to `∞e^{-iπ/3}`. -/
noncomputable def Hinf (ε : ℝ) (k : ℕ) (c : ℝ) (u : ℝ) : ℂ :=
  ((Real.exp (-ε * u) / (2 * Real.pi) : ℝ) : ℂ) *
    rayIntegral c (Real.pi / 3) (-Real.pi / 3)
      (fun a => exp (-(u : ℂ) * a + a ^ 3 / 3) * (1 / a ^ k))

/-- `𝓙_∞(v)`, (122): `(e^{εv}/2π) ∫_{Σ_∞} e^{va - a³/3} a^k da`, where `Σ_∞` comes in from
`∞e^{-2iπ/3}` to the real vertex `c` and goes out to `∞e^{2iπ/3}`. -/
noncomputable def Jinf (ε : ℝ) (k : ℕ) (c : ℝ) (v : ℝ) : ℂ :=
  ((Real.exp (ε * v) / (2 * Real.pi) : ℝ) : ℂ) *
    rayIntegral c (-2 * Real.pi / 3) (2 * Real.pi / 3)
      (fun a => exp ((v : ℂ) * a - a ^ 3 / 3) * a ^ k)

end SpikedWishart.SoftEdge


