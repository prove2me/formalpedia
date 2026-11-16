-- Prove2me | Definitions.Def_ChoresTIE197_Main_Supplement_threshold
-- name    : ChoresTIE197_Main_Supplement_threshold
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:58:43.038748+00:00
-- url     : https://prove2.me/theorems/3af1dbff-58fe-4b4b-aecf-434e17a9dd9d
-- title:
--   Theorem 5.1 — exact parity-dependent lower-bound threshold
-- statement:
--   For a number $n$ of agents define
--   $$
--   \alpha_n=\begin{cases}
--   4/3,&n=2,\\
--   \max\{1+1/(3n-2),13/12\},&n\ge3\text{ odd},\\
--   \max\{1+1/(3n-1),13/12\},&n\ge4\text{ even}.
--   \end{cases}
--   $$
--   This is the numerical threshold in the companion impossibility theorem, independent of any mechanism or costs. Denominators are real expressions, with $n$ converted to a real number before subtraction. The total definition returns zero for $n<2$, outside every theorem's domain.
-- source:
--   Zehan Lin, Biaoshuai Tao, Xiaowei Wu, Yuhao Zhang, STOC 2027 submission #859 (October 2026), Theorem 5.1, printed p.24, PDF p.24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/859.pdf

import Mathlib

noncomputable section

namespace ChoresTIE197.Main.Supplement

/-- Theorem 5.1, printed/PDF p.24. Arithmetic in the denominators is real.
The value zero at n < 2 is outside the domain of every lower-bound theorem. -/
def threshold (n : ℕ) : ℝ :=
  if n < 2 then 0 else
  if n = 2 then 4 / 3 else
  if n % 2 = 1 then max (1 + 1 / (3 * (n : ℝ) - 2)) (13 / 12)
  else max (1 + 1 / (3 * (n : ℝ) - 1)) (13 / 12)

end ChoresTIE197.Main.Supplement


