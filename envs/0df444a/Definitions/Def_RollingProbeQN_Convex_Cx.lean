-- Prove2me | Definitions.Def_RollingProbeQN_Convex_Cx
-- name    : RollingProbeQN_Convex_Cx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:03.899011+00:00
-- url     : https://prove2.me/theorems/474a184f-b842-4fee-a72a-e1d7adddf904
-- title:
--   The constant $C_x=1+\sigma/\sqrt{1-\sigma^2}$
-- statement:
--   For $\sigma\in(0,1)$,
--
--   $$C_x=1+\frac{\sigma}{\sqrt{1-\sigma^2}} .$$
--
--   It bounds the distance of the A-HPE iterates to a minimizer in units of $R$ (Lemma D.8) and depends only on $\sigma$.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Lemma D.8, p. 39

import Mathlib

namespace RollingProbeQN.Convex

/-- **The constant `C_x = 1 + σ/√(1 − σ²)`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Lemma D.8, p. 39: "`C_x := 1 + σ/√(1 − σ²)`". It depends only on `σ`. -/
noncomputable def Cx (σ : ℝ) : ℝ :=
  1 + σ / Real.sqrt (1 - σ ^ 2)

end RollingProbeQN.Convex


