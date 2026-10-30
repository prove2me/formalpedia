-- Prove2me | Definitions.Def_BBPSSW_Distill_halfPiRot
-- name    : BBPSSW_Distill_halfPiRot
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:38.136404+00:00
-- url     : https://prove2.me/theorems/f86929fa-4a1f-447e-8478-7556b1857545
-- title:
--   Spin rotation by $\pi/2$ about an axis
-- statement:
--   The rotation of one spin by $\pi/2$ about the axis $a\in\{x,y,z\}$ is
--
--   $$R_a=e^{-i\pi\sigma_a/4}=\frac{\sqrt2}{2}\,(1-i\,\sigma_a).$$
--
--   Applied to both particles of a pair it gives the bilateral rotations $B_x,B_y,B_z$ of the paper.
--
--   **Formalization Note** The paper does not fix the sense of rotation; the opposite sense permutes the Bell states in the same way up to phases.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 2, unnumbered bullet ("Bilateral π/2 rotations Bx, By, and Bz")

import Mathlib
import Definitions.Def_BBPSSW_Distill_pauli

namespace BBPSSW.Distill

/-- **The π/2 spin rotation about an axis.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 2 (unnumbered bullet: "Bilateral π/2 rotations Bx, By, and Bz of both particles in a
pair about the x, y, or z axis respectively").

`halfPiRot a = (√2/2)(1 − i σ_a) = exp(−i (π/4) σ_a)`, the rotation of one spin by π/2 about
axis `a`.

**Formalization Note.** The paper does not fix the sense of the rotation; the opposite sense
`(√2/2)(1 + i σ_a)` permutes the Bell states in the same way, up to phases. -/
noncomputable def halfPiRot (a : Axis) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 / 2 : ℝ) : ℂ) • (1 - Complex.I • pauli a)

end BBPSSW.Distill


