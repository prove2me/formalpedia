-- Prove2me | Definitions.Def_QuantumNoise_Delta
-- name    : QuantumNoise_Delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:24:28.575368+00:00
-- url     : https://prove2.me/theorems/e81136b6-5d7e-4252-b6a8-ca2281eee082
-- title:
--   The function $\Delta[z]=(|1+z^2|-(1+|z|^2))/2$
-- statement:
--   For $z\in\mathbb C$,
--   $$
--   \Delta[z]=\frac{|1+z^2|-\big(1+|z|^2\big)}{2}.
--   $$
--   One has $\Delta[z]\le 0$, $1+\Delta[z]\ge 0$, and $\Delta[z]=0$ for real $z$. It measures how far the phase of the noise cross-correlation is from that of the gain in the quantum noise inequality (4.11).
-- source:
--   Clerk, Devoret, Girvin, Marquardt, Schoelkopf, Introduction to Quantum Noise, Measurement and Amplification, arXiv:0810.4729v2, Sec. IV.A.3, Eq. (4.12), p.23

import Mathlib

namespace QuantumNoise

/-- The correction term of the quantum noise inequality,
`Δ[z] = (|1 + z²| − (1 + |z|²)) / 2` for `z ∈ ℂ`.

Clerk et al., arXiv:0810.4729v2, Sec. IV.A.3, Eq. (4.12), p.23 (printed p.23, PDF p.23). The
parentheses around `1 + |z|²` are those of the printed page (the text layer loses them).
`Δ[z] ≤ 0`, `1 + Δ[z] ≥ 0`, and `Δ[z] = 0` for real `z`. -/
noncomputable def Delta (z : ℂ) : ℝ :=
  (‖1 + z ^ 2‖ - (1 + ‖z‖ ^ 2)) / 2

end QuantumNoise


