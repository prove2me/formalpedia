-- Prove2me | Definitions.Def_UCalibDirichlet_Supplement_FE8
-- name    : UCalibDirichlet_Supplement_FE8
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:12:12.014892+00:00
-- url     : https://prove2.me/theorems/5f8f76f1-64ae-4d2a-8dbf-47b9b543bde1
-- title:
--   The potential $F(p)=(p-1/2)^2\log(e/|p-1/2|)$ of Theorem E.8
-- statement:
--   The binary potential
--   $$F(p)=\Big(p-\tfrac12\Big)^2\log\frac{e}{|p-\tfrac12|}\quad(p\ne\tfrac12),\qquad F(\tfrac12)=0,$$
--   with the natural logarithm. It is the continuous extension at $p=1/2$; it is convex on $[0,1]$ with $F''(p)=2\log(1/|p-1/2|)-1>0$, a logarithmic curvature singularity at $p=1/2$.
--
--   This is the potential of Theorem E.8 (Theorem 1.16), the example where the i.i.d. lower bound $L_F(T)\asymp\log T$ is off by a logarithmic factor from the minimax regret $(\log T)^2$.
--
--   **Formalization Note** The value at $p=1/2$ is defined explicitly by the case split.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Theorem E.8, p.46; Theorem 1.16, p.9

import Mathlib

namespace UCalibDirichlet.Supplement

/-- **The potential of Theorem E.8 (= Theorem 1.16).** Frongillo, Luo, Mehta & Schneider
(manuscript, STOC 2027 submission), Theorem E.8, p.46: "Let `F(p) = (p − 1/2)² log(e/|p − 1/2|)`,
`F(1/2) = 0`"; Theorem 1.16, p.9: "continuously extended at 1/2".

`FE8 p = (p − 1/2)² log(e/|p − 1/2|)` for `p ≠ 1/2`, and `FE8 (1/2) = 0`.

**Formalization Note.** The case `p = 1/2` is written explicitly rather than relying on
`Real.log` of `e/0 = 0`. `log` is the natural logarithm. Only the values on `[0, 1]` matter. -/
noncomputable def FE8 (p : ℝ) : ℝ :=
  if p = 1 / 2 then 0 else (p - 1 / 2) ^ 2 * Real.log (Real.exp 1 / |p - 1 / 2|)

end UCalibDirichlet.Supplement


