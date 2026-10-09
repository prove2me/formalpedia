-- Prove2me | Definitions.Def_QuantumZipper_ReverseCoupling_ZipperFields
-- name    : QuantumZipper_ReverseCoupling_ZipperFields
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:21.051412+00:00
-- url     : https://prove2.me/theorems/78e9d772-d8fd-48a0-9591-4be71f48392a
-- title:
--   Theorem 1.2 and §4.1, pp. 13, 44–47 — Q, 𝔥₀, 𝔥_t, C_t, G_t, E_t, the driving function √κ B_t and the Brownian filtration
-- statement:
--   Fix $\kappa>0$ and a reverse Loewner flow $f_t=g_t-W_t$. Define
--
--   1. $Q=\dfrac{2}{\sqrt\kappa}+\dfrac{\sqrt\kappa}{2}$;
--   2. $\mathfrak h_0(z)=\dfrac{2}{\sqrt\kappa}\log|z|$;
--   3. $\mathfrak h_t(z)=\mathfrak h_0(f_t(z))+Q\log|f_t'(z)|=\operatorname{Re}\mathfrak h^*_t(z)$, where $\mathfrak h^*_t(z)=\frac{2}{\sqrt\kappa}\log f_t(z)+Q\log f'_t(z)$;
--   4. $C_t(z)=-\log\operatorname{Im} f_t(z)-\operatorname{Re}\log f'_t(z)=-\log\operatorname{Im}f_t(z)-\log|f'_t(z)|$;
--   5. $G_t(y,z)=G(f_t(y),f_t(z))$ with the free boundary Green's function $G(y,z)=-\log|y-z|-\log|y-\bar z|$;
--   6. $E_t(\rho_1,\rho_2)=\int_{\mathbb H}\int_{\mathbb H}\rho_1(y)\,G_t(y,z)\,\rho_2(z)\,dy\,dz$, and $E_t(\rho)=E_t(\rho,\rho)$.
--
--   The fraktur $\mathfrak h_t$ are deterministic functions of the flow, not the random field $h$. For a real process $B=(B_t)_{t\ge0}$ the driving function of the sample $\omega$ is $W_t=\sqrt\kappa\,B_t(\omega)$, and the filtration is the natural filtration $\mathcal F_t=\sigma(B_s:s\le t)$. These are the processes whose martingale properties §4.1 establishes in the proof of Theorem 1.2.
--
--   **Formalization Note** $f_t$ is holomorphic, injective and has nonvanishing derivative on $\mathbb H$, and $f_t(\mathbb H)\subseteq\mathbb H$, so $\mathfrak h_t$, $C_t$ and $G_t$ (off the diagonal) are smooth on $\mathbb H$ and their pairings with test functions supported in $\mathbb H$ are genuine integrals. The Brownian filtration is Mathlib's `Filtration.natural`, which needs measurable coordinates $B_t$.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, Theorem 1.2, p. 13; §4.1, tables on p. 44 (Q, 𝔥*_t, 𝔥_t), p. 46 (C_t), p. 47 (G, G_t, E_t); (4.2), p. 49

import Mathlib
import Definitions.Def_QuantumZipper_ReverseCoupling_FreeBoundaryGFF
import Definitions.Def_QuantumZipper_ReverseCoupling_ReverseLoewnerFlow

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace QuantumZipper.ReverseCoupling

/-- `Q = 2/√κ + √κ/2` (arXiv:1012.4797v2, Theorem 1.2, p. 13; table on p. 44). -/
noncomputable def Q (κ : ℝ) : ℝ :=
  2 / Real.sqrt κ + Real.sqrt κ / 2

/-- `𝔥₀(z) = (2/√κ) log |z|` (Theorem 1.2, p. 13). (Fraktur `𝔥`: a deterministic function, not the
field `h`.) -/
noncomputable def frakH0 (κ : ℝ) (z : ℂ) : ℝ :=
  2 / Real.sqrt κ * Real.log ‖z‖

/-- `𝔥_t(z) = 𝔥₀(f_t(z)) + Q log |f′_t(z)|` (Theorem 1.2, p. 13), which is `Re 𝔥*_t(z)` with
`𝔥*_t(z) = (2/√κ) log f_t(z) + Q log f′_t(z)` (reverse column of the table on p. 44), for the reverse
Loewner flow `f_t = g_t − W_t`. -/
noncomputable def frakH (κ : ℝ) (W : ℝ≥0 → ℝ) (g : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (z : ℂ) : ℝ :=
  frakH0 κ (revF W g t z) + Q κ * Real.log ‖revFDeriv W g t z‖

/-- `C_t(z) = −log Im f_t(z) − Re log f′_t(z) = −log Im f_t(z) − log |f′_t(z)|`
(reverse column of the table on p. 46). -/
noncomputable def Cfun (W : ℝ≥0 → ℝ) (g : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (z : ℂ) : ℝ :=
  -Real.log (revF W g t z).im - Real.log ‖revFDeriv W g t z‖

/-- `G_t(y, z) = G(f_t(y), f_t(z))` with the free boundary Green's function `G = G^{ℍ_F}`
(reverse column of the table on p. 47). -/
noncomputable def Gt (W : ℝ≥0 → ℝ) (g : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (y z : ℂ) : ℝ :=
  greenFree (revF W g t y) (revF W g t z)

/-- `E_t(ρ₁, ρ₂) = ∫_ℍ ∫_ℍ ρ₁(y) G_t(y, z) ρ₂(z) dy dz` (table on p. 47, where `E_t(ρ) = E_t(ρ, ρ)`;
the bilinear form appears in (4.2), p. 49).

**Formalization Note** A Bochner integral over `ℂ × ℂ`; for test functions supported in `ℍ` the
integrand is integrable (logarithmic singularity on the diagonal, `f_t` injective and smooth on `ℍ`). -/
noncomputable def Et (W : ℝ≥0 → ℝ) (g : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (ρ₁ ρ₂ : ℂ → ℝ) : ℝ :=
  ∫ p : ℂ × ℂ, ρ₁ p.1 * Gt W g t p.1 p.2 * ρ₂ p.2

/-- The natural filtration `(σ(B_s : s ≤ t))_{t ≥ 0}` of a real process `B` with measurable
coordinates; the martingales of §4.1 (pp. 44–50) are with respect to it. -/
noncomputable def brownianFiltration {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (hB : ∀ t, Measurable (B t)) : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) :=
  Filtration.natural (fun t => B t) (fun t => (hB t).stronglyMeasurable)

/-- The driving function `W_t = √κ B_t` of the sample `ω` (p. 43). -/
noncomputable def drive {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 → ℝ :=
  fun t => Real.sqrt κ * B t ω

end QuantumZipper.ReverseCoupling


