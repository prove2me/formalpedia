-- Prove2me | Definitions.Def_MagnonCode_AQEDC_omega
-- name    : MagnonCode_AQEDC_omega
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:37:34.653501+00:00
-- url     : https://prove2.me/theorems/e665003f-aae7-448f-a7a2-c0b0d44a361e
-- title:
--   The root of unity $\omega=e^{2\pi i/n}$
-- statement:
--   The primitive $n$-th root of unity $\omega=e^{2\pi i/n}$, which gives the one-magnon state its momentum $2\pi/n$.
-- source:
--   Gschwendtner, König, Şahinoğlu, Tang, Quantum Error-Detection at Low Energies, arXiv:1902.02115v2, Eq. (81), p. 54

import Mathlib

namespace MagnonCode.AQEDC

/-- **Eq. (81)** (Gschwendtner, König, Şahinoğlu, Tang, *Quantum Error-Detection at Low Energies*, arXiv:1902.02115v2, p. 54): the root of unity `ω = e^{2πi/n}`. -/
noncomputable def omega (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / n)

end MagnonCode.AQEDC


