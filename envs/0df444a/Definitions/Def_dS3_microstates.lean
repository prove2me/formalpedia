-- Prove2me | Definitions.Def_dS3_microstates
-- name    : dS3_microstates
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-26T02:10:37.657641+00:00
-- url     : https://prove2.me/theorems/f3cad8b1-bc2e-45a7-a4a2-5b69126ae3b5
-- title:
--   dS$_3$ microstate counting: eigenvalue density $\rho_0$, $E_0$, $N_{\mathrm{eff}}$, ZZ tension, $C_{S^2}$
-- statement:
--   Definitions for §4.4 and Appendix C of Collier–Eberhardt–Mühlmann, *A microscopic realization of dS$_3$*. All objects are functions of a complex Liouville parameter $b$ (and of a real parameter $S_0$).
--
--   - **Regime** (footnote 2): $b$ is admissible if $-ib^2\in\mathbb{R}_{>0}$, i.e. $b^2 = i\beta$ for some real $\beta>0$.
--   - **Eigenvalue density** (eq. (C.4)): for real $E$, $\rho_0(E) = \frac{2}{\pi}\sinh(-i\pi b^2)\sin\big(-ib^2\operatorname{arccosh}(E/2)\big)$, with $\operatorname{arccosh}x = \log(x+\sqrt{x^2-1})$.
--   - **First zero** (§4.4): $E_0 = 2\cos(\pi b^{-2})$, where $b^{-2} = (b^2)^{-1}$.
--   - **Effective number of eigenvalues** (eq. (4.32)): $N_{\mathrm{eff}} = \int_2^{\operatorname{Re}E_0} e^{S_0}\rho_0(E)\,dE$ (in the admissible regime $E_0$ is real).
--   - **Microscopic entropy** (eq. (4.33)): $S^{\mathrm{micro}}_{\mathrm{dS}} = 2\log N_{\mathrm{eff}}$, with the complex principal logarithm.
--   - **Tension of the first ZZ-instanton** (eq. (4.34)): $\widehat T_{1,1} = \frac{8b^2\sin(\pi b^2)\sin(\pi b^{-2})}{1-b^4}$ and $T_{1,1} = e^{S_0}\widehat T_{1,1}$.
--   - **Sphere normalization** (eq. (4.4)): $C_{S^2} = 32\pi^4\left(\frac{\sin(\pi b^2)\sin(\pi b^{-2})}{b^2-b^{-2}}\right)^2$.
-- source:
--   S. Collier, L. Eberhardt, B. Mühlmann, *A microscopic realization of dS$_3$*, arXiv:2501.01486v1 [hep-th] (2 Jan 2025), https://arxiv.org/abs/2501.01486; footnote 2 (p. 6), eqs. (4.4) (p. 27), (4.32)–(4.34) (pp. 36–37), (C.4) (p. 60).

import Mathlib

/-!
# Microstate counting in dS₃ (Collier–Eberhardt–Mühlmann, arXiv:2501.01486)

Definitions for §4.4 and Appendix C of "A microscopic realization of dS₃".
The Liouville parameter `b` is a complex number with `-i b² ∈ ℝ_{>0}` (footnote 2),
so that the central charge `c = 1 + 6 (b + b⁻¹)²` lies in `13 + iℝ`.
-/

noncomputable section

namespace DS3Micro

open Complex

/-- The parameter regime of the paper (footnote 2): `-i b² ∈ ℝ_{>0}`, i.e. `b² = i β`
for some real `β > 0`. -/
def InRegime (b : ℂ) : Prop :=
  ∃ β : ℝ, 0 < β ∧ b ^ 2 = Complex.I * (β : ℂ)

/-- Leading density of eigenvalues of the first matrix, eq. (C.4):
`ρ₀(E) = (2/π) sinh(-iπ b²) sin(-i b² arccosh(E/2))`. -/
def rho0 (b : ℂ) (E : ℝ) : ℂ :=
  (2 / (Real.pi : ℂ)) * Complex.sinh (-Complex.I * (Real.pi : ℂ) * b ^ 2) *
    Complex.sin (-Complex.I * b ^ 2 * (Real.arcosh (E / 2) : ℂ))

/-- The first zero of the eigenvalue density, `E₀ = 2 cos(π b⁻²)` (§4.4, Appendix C). -/
def E0 (b : ℂ) : ℂ :=
  2 * Complex.cos ((Real.pi : ℂ) * (b ^ 2)⁻¹)

/-- Effective number of eigenvalues, eq. (4.32): `N_eff = ∫_2^{E₀} e^{S₀} ρ₀(E) dE`.
The upper limit is the real part of `E₀` (which is real in the regime `InRegime b`). -/
def Neff (b : ℂ) (S0 : ℝ) : ℂ :=
  ∫ E in (2 : ℝ)..(E0 b).re, (Real.exp S0 : ℂ) * rho0 b E

/-- Microscopic de Sitter entropy, eq. (4.33): `S_dS^micro = 2 log N_eff`
(complex principal logarithm). -/
def SdSMicro (b : ℂ) (S0 : ℝ) : ℂ :=
  2 * Complex.log (Neff b S0)

/-- Reduced tension of the first ZZ-instanton, eq. (4.34):
`T̂₁,₁ = 8 b² sin(π b²) sin(π b⁻²) / (1 - b⁴)`. -/
def tensionHat (b : ℂ) : ℂ :=
  8 * b ^ 2 * Complex.sin ((Real.pi : ℂ) * b ^ 2) * Complex.sin ((Real.pi : ℂ) * (b ^ 2)⁻¹) /
    (1 - b ^ 4)

/-- Tension of the first ZZ-instanton, eq. (4.34): `T₁,₁ = e^{S₀} T̂₁,₁`. -/
def tension (b : ℂ) (S0 : ℝ) : ℂ :=
  (Real.exp S0 : ℂ) * tensionHat b

/-- Normalization of the string path integral on the sphere, eq. (4.4):
`C_{S²} = 32 π⁴ (sin(π b²) sin(π b⁻²) / (b² - b⁻²))²`. -/
def CS2 (b : ℂ) : ℂ :=
  32 * (Real.pi : ℂ) ^ 4 *
    (Complex.sin ((Real.pi : ℂ) * b ^ 2) * Complex.sin ((Real.pi : ℂ) * (b ^ 2)⁻¹) /
      (b ^ 2 - (b ^ 2)⁻¹)) ^ 2

end DS3Micro

end


