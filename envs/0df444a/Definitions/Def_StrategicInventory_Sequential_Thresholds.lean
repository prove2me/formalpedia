-- Prove2me | Definitions.Def_StrategicInventory_Sequential_Thresholds
-- name    : StrategicInventory_Sequential_Thresholds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T04:47:41.133153+00:00
-- url     : https://prove2.me/theorems/35302eac-59bf-464b-8ce5-77e178cfe095
-- title:
--   Region thresholds $x$, $w$, $s_3$, $h_7$, $h_{10}$, $h_{11}$ and the inventory level $I^*$, Appendix A
-- statement:
--   Appendix A of the paper partitions the $(h, s)$ plane into regions using threshold functions of the direct selling cost $s$, for a demand intercept $\alpha$. This file defines the thresholds used by the regions near $s = 5\alpha/6$:
--
--   $$
--   x = \sqrt{4\alpha s - \alpha^2 - 3 s^2}, \qquad
--   w = 11\alpha^2 + 24 s^2 - 32\alpha s + (8\alpha - 12 s)\,x,
--   $$
--
--   $$
--   s_3 = \Big(\frac{\sqrt{37 - 3\sqrt{65}}}{34} + \frac46\Big)\alpha \approx 0.7719\,\alpha,
--   $$
--
--   $$
--   h_7 = \frac{8(\alpha - s)^2 - 4\alpha^2 + 3(\alpha - 3s + x)^2}{8(3s - 2\alpha - x)} - \frac{\alpha}{2}, \qquad
--   h_{10} = h_7 - \frac{\sqrt{-w}}{2},
--   $$
--
--   $$
--   h_{11} = \frac{\alpha - \sqrt{17}\,\sqrt{3\alpha^2 + 6 s^2 - 8\alpha s + (4\alpha - 6 s)\,x}}{4},
--   $$
--
--   together with the Region 7 inventory level of Table A.3,
--
--   $$
--   I^* = \frac{2\alpha - 3 s + x}{2}.
--   $$
--
--   Here $w$ is a function of $s$, not a wholesale price; it is named `wDisc` in Lean to avoid the clash.
--
--   **Formalization Note.** The paper prints $s_3 = (\sqrt{(37 - 3\sqrt{65})/34} + 4/6)\alpha \approx 1.2806\,\alpha$. That value exceeds $5\alpha/6$ and would empty the regions that start at $s_3$. The value defined here moves $/34$ outside the square root. It gives $\approx 0.7719\,\alpha$, which matches the paper's own "≈0.77" in §4.1 (p. 542). Lean's `Real.sqrt` returns $0$ on negative arguments. The statements that use these thresholds only evaluate them for $2\alpha/3 < s < 5\alpha/6$. On that range, $x$ is real (the radicand $4\alpha s - \alpha^2 - 3s^2$ is positive), and the denominator $3s - 2\alpha - x$ of $h_7$ is negative; it vanishes only at $s = 5\alpha/6$. The quantities $h_{10}$ and $h_{11}$ are used only for $s_3 \le s < 5\alpha/6$. There $w \le 0$ and the radicand of $h_{11}$ is nonnegative, which was checked numerically.
-- source:
--   Guan, Gurnani, Geng & Luo, Strategic Inventory and Supplier Encroachment, MSOM 21(3) 2019, p. 551 (Appendix A: x, w, s3), p. 553 (h7, h10, h11), p. 552 (Table A.3 Note: I*)

import Mathlib

namespace StrategicInventory.Sequential

/-- Appendix A, p. 551: `x = √(4αs − α² − 3s²)` (real for `α/3 ≤ s ≤ α`). -/
noncomputable def xRoot (α s : ℝ) : ℝ :=
  Real.sqrt (4 * α * s - α ^ 2 - 3 * s ^ 2)

/-- Appendix A, p. 551: the quantity the paper calls `w`,
`w = 11α² + 24s² − 32αs + (8α − 12s)x` (a function of `s`, not a wholesale price). -/
noncomputable def wDisc (α s : ℝ) : ℝ :=
  11 * α ^ 2 + 24 * s ^ 2 - 32 * α * s + (8 * α - 12 * s) * xRoot α s

/-- Appendix A, p. 551, `s3`, **corrected**: `s3 = (√(37 − 3√65)/34 + 4/6)α ≈ 0.7719α`.
The page prints `(√((37 − 3√65)/34) + 4/6)α ≈ 1.2806α`, which exceeds `5α/6` and
would empty the regions that start at `s3`; the corrected value matches the
paper's "≈ 0.77" (§4.1, p. 542). -/
noncomputable def s3 (α : ℝ) : ℝ :=
  (Real.sqrt (37 - 3 * Real.sqrt 65) / 34 + 4 / 6) * α

/-- Appendix A, p. 553:
`h7 = (8(α − s)² − 4α² + 3(α − 3s + x)²) / (8(3s − 2α − x)) − α/2`. -/
noncomputable def h7 (α s : ℝ) : ℝ :=
  (8 * (α - s) ^ 2 - 4 * α ^ 2 + 3 * (α - 3 * s + xRoot α s) ^ 2) /
      (8 * (3 * s - 2 * α - xRoot α s)) - α / 2

/-- Appendix A, p. 553: `h10 = h7 − √(−w)/2`. -/
noncomputable def h10 (α s : ℝ) : ℝ :=
  h7 α s - Real.sqrt (-wDisc α s) / 2

/-- Appendix A, p. 553:
`h11 = (α − √17 · √(3α² + 6s² − 8αs + (4α − 6s)x)) / 4`. -/
noncomputable def h11 (α s : ℝ) : ℝ :=
  (α - Real.sqrt 17 * Real.sqrt (3 * α ^ 2 + 6 * s ^ 2 - 8 * α * s + (4 * α - 6 * s) * xRoot α s)) / 4

/-- Table A.3, Note, p. 552: the Region 7 inventory level `I* = (2α − 3s + x)/2`. -/
noncomputable def invStar (α s : ℝ) : ℝ :=
  (2 * α - 3 * s + xRoot α s) / 2

end StrategicInventory.Sequential


