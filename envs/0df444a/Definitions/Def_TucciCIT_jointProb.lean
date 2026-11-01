-- Prove2me | Definitions.Def_TucciCIT_jointProb
-- name    : TucciCIT_jointProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:28:21.719925+00:00
-- url     : https://prove2.me/theorems/e9337f33-93d7-4d90-8d60-ed28a99df1cf
-- title:
--   Joint law $P(x,y) = |\psi(x,y)|^2$
-- statement:
--   For an amplitude $\psi$ on $S_x \times S_y$, define
--
--   $$
--   P(x, y) = |\psi(x, y)|^2 .
--   $$
--
--   For a unit amplitude this is a probability distribution on $S_x \times S_y$; it is the law of the classical mutual information $H(x:y)$ in eq. (4.8).
-- source:
--   Tucci, Quantum Entanglement and Conditional Information Transmission, arXiv:quant-ph/9909041v2, eq. (4.7), p.8

import Mathlib

namespace TucciCIT

/-- Tucci, *Quantum Entanglement and Conditional Information Transmission*,
arXiv:quant-ph/9909041v2, eq. (4.7), p.8 (PDF p.8).

The classical joint distribution `P(x, y) = |ψ(x, y)|²` of the amplitude `ψ`. It is a
probability distribution on `S_x × S_y` exactly when `Σ_{x,y} |ψ(x,y)|² = 1`. -/
noncomputable def jointProb {X Y : Type*} (ψ : Matrix X Y ℂ) (x : X) (y : Y) : ℝ :=
  ‖ψ x y‖ ^ 2

end TucciCIT


