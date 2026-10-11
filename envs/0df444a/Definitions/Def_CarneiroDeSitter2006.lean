-- Prove2me | Definitions.Def_CarneiroDeSitter2006
-- name    : CarneiroDeSitter2006
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T02:07:37.309975+00:00
-- url     : https://prove2.me/theorems/08d1d410-fe54-4b07-9710-f1d807dd6580
-- title:
--   Carneiro (2006): plane wave, vacuum term $(m+H)^4-m^4$, dust scale factor, deceleration parameter
-- statement:
--   Basic objects of S. Carneiro's decaying-vacuum cosmology (all quantities in Planck units).
--
--   1. **Wave number and damping rate** (Eqs. (7)–(8)). For a frequency $\omega$ and a Hubble parameter $H$,
--   $$
--   k(\omega,H)=\frac{\sqrt2\,\omega}{2}\Big(1+\sqrt{1+(3H/\omega)^2}\Big)^{1/2},\qquad
--   b(\omega,H)=\frac{3\sqrt2\,H}{2}\Big(1+\sqrt{1+(3H/\omega)^2}\Big)^{-1/2}.
--   $$
--   2. **Damped radial plane wave** (Eq. (6)). For a complex amplitude $\phi_0$ and real $b,\omega,k$,
--   $$
--   \phi(t,r)=\phi_0\,e^{-br}\,e^{-i(\omega t-kr)} .
--   $$
--   3. **Renormalized vacuum term** (Eq. (11)). For a cutoff $m$ and Hubble parameter $H$,
--   $$
--   \Lambda(m,H)=(m+H)^4-m^4 .
--   $$
--   4. **Dust-phase scale factor** (Eq. (14)). For constants $C,\sigma$,
--   $$
--   a(t)=C\,\big(e^{\sigma t/2}-1\big)^{2/3}.
--   $$
--   5. **Deceleration parameter.** For a Hubble function $H(t)$, $q(t)=-1-\dot H(t)/H(t)^2$, which equals $-a\ddot a/\dot a^2$ when $H=\dot a/a$.
--
--   These definitions are shared by all statements of the mission.
--
--   **Formalization Note** The power $2/3$ in item 4 is the real power function; it agrees with the intended value whenever $e^{\sigma t/2}-1\ge 0$, i.e. for $\sigma t\ge 0$. Division by $\omega=0$ or $H=0$ returns $0$ in Lean; every theorem using items 1 or 5 assumes $\omega>0$ or $H(t)\neq 0$, respectively.
-- source:
--   S. Carneiro, "From de Sitter to de Sitter: a non-singular inflationary universe driven by vacuum", Int. J. Mod. Phys. D 15 (2006) 2241-2247, https://doi.org/10.1142/S0218271806009510, pp. 2243-2245, Eqs. (6), (7), (8), (11), (14); deceleration factor q on p. 2245

import Mathlib

/-!
# Definitions for Carneiro (2006), "From de Sitter to de Sitter"

S. Carneiro, *From de Sitter to de Sitter: a non-singular inflationary universe driven by
vacuum*, Int. J. Mod. Phys. D 15 (2006) 2241–2247. All quantities are in Planck units.
-/

namespace CarneiroDeSitter

/-- Eq. (7): the wave number `k` of the radial plane-wave solution of the massless
Klein–Gordon equation in a background with Hubble parameter `H`, for frequency `ω`:
`k = (√2 ω / 2) · (1 + √(1 + (3H/ω)²))^{1/2}`. -/
noncomputable def waveNumber (ω H : ℝ) : ℝ :=
  Real.sqrt 2 * ω / 2 * Real.sqrt (1 + Real.sqrt (1 + (3 * H / ω) ^ 2))

/-- Eq. (8): the damping rate `b` (inverse depth length) of the radial plane wave:
`b = (3√2 H / 2) · (1 + √(1 + (3H/ω)²))^{-1/2}`. -/
noncomputable def dampingRate (ω H : ℝ) : ℝ :=
  3 * Real.sqrt 2 * H / 2 / Real.sqrt (1 + Real.sqrt (1 + (3 * H / ω) ^ 2))

/-- Eq. (6): the damped radial plane wave `φ(t, r) = φ₀ e^{-b r} e^{-i(ω t - k r)}`. -/
noncomputable def planeWave (φ₀ : ℂ) (b ω k : ℝ) (t r : ℝ) : ℂ :=
  φ₀ * Complex.exp (-((b * r : ℝ) : ℂ)) * Complex.exp (-Complex.I * ((ω * t - k * r : ℝ) : ℂ))

/-- Eq. (11): the renormalized vacuum term `Λ = (m + H)⁴ - m⁴` (cutoff `m`, Hubble
parameter `H`). -/
def vacuumTerm (m H : ℝ) : ℝ := (m + H) ^ 4 - m ^ 4

/-- Eq. (14): the scale factor of the late-time dust phase,
`a(t) = C (e^{σ t / 2} - 1)^{2/3}` (meaningful for `σ > 0`, `t > 0`). -/
noncomputable def dustScaleFactor (C σ t : ℝ) : ℝ :=
  C * (Real.exp (σ * t / 2) - 1) ^ ((2 : ℝ) / 3)

/-- The deceleration parameter of a flat FLRW expansion with Hubble parameter `H(t)`,
`q = -1 - Ḣ / H²` (equivalently `q = -a ä / ȧ²` when `H = ȧ / a`). -/
noncomputable def decelerationParameter (H : ℝ → ℝ) (t : ℝ) : ℝ :=
  -1 - deriv H t / H t ^ 2

end CarneiroDeSitter


