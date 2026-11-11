-- Prove2me | Definitions.Def_ShamirLLR_finFourier
-- name    : ShamirLLR_finFourier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:26:05.896881+00:00
-- url     : https://prove2.me/theorems/fb4619ff-7086-46d4-9a34-76a55dc73c22
-- title:
--   Characters $e_p$, constant $M_p$, finite Fourier coefficients and weights $\mu$
-- statement:
--   For $z\in\mathbb F_p$ let $e_p(z)=\exp(2\pi i\tilde z/p)$ for any integer representative $\tilde z$, and put
--   $$
--   M_p=\frac{1}{p\sin(\pi/(2p))}.
--   $$
--   For a finite $\mathbb F_p$-vector space $E$, $A:E\to\mathbb R$ and $\gamma\in E^*=\mathrm{Hom}_{\mathbb F_p}(E,\mathbb F_p)$, the normalized Fourier coefficient is
--   $$
--   \widehat A(\gamma)=\mathbb E_{v\in E}A(v)\,e_p(-\gamma(v)),
--   $$
--   and the combined weights are $\mu(0)=1$ and $\mu(\gamma)=2|\widehat A(\gamma)|$ for $\gamma\neq0$.
--
--   $M_p=2/\pi+O(p^{-2})$ is the sharp bound on nonzero weights that gives the base $2/\pi$.
--
--   **Formalization Note** The representative is $z.\mathrm{val}\in\{0,\dots,p-1\}$.
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), §2.3, p.17; Eq. (56), (58), p.55; §9, p.63 (PDF pp.18, 56, 64)

import Mathlib

set_option autoImplicit false

namespace ShamirLLR

/-- The additive character `e_p(z) = e(z̃/p) = exp(2πi z̃/p)` of `𝔽_p`, where `z̃` is any integer
representative of `z` (§2.3, p.17; Eq. (56), p.55).

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
§2.3, p.17.

**Formalization Note.** The representative is `z.val ∈ {0, …, p−1}`; any other representative
gives the same value. -/
noncomputable def ep {p : ℕ} (z : ZMod p) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((z.val : ℂ) / (p : ℂ)))

/-- The finite-field constant `M_p = 1 / (p sin(π/(2p)))` of §9, p.63. -/
noncomputable def Mp (p : ℕ) : ℝ :=
  1 / ((p : ℝ) * Real.sin (Real.pi / (2 * (p : ℝ))))

/-- The normalized finite Fourier coefficient on a finite `𝔽_p`-vector space `E`, Eq. (56),
p.55: `Â(γ) = 𝔼_{v ∈ E} A(v) e_p(−γ(v))` for `γ ∈ E^* = Hom_{𝔽_p}(E, 𝔽_p)`. -/
noncomputable def finFourier {p : ℕ} {E : Type*} [AddCommGroup E] [Module (ZMod p) E]
    [Fintype E] (A : E → ℝ) (γ : Module.Dual (ZMod p) E) : ℂ :=
  (Fintype.card E : ℂ)⁻¹ * ∑ v : E, (A v : ℂ) * ep (-γ v)

/-- The combined Fourier weights of Eq. (58), p.55: `μ(0) = 1` and `μ(γ) = 2 |Â(γ)|` for
`γ ≠ 0`. -/
noncomputable def fourierWeight {p : ℕ} {E : Type*} [AddCommGroup E] [Module (ZMod p) E]
    [Fintype E] (A : E → ℝ) (γ : Module.Dual (ZMod p) E) : ℝ :=
  open Classical in
  if γ = 0 then 1 else 2 * ‖finFourier A γ‖

end ShamirLLR


