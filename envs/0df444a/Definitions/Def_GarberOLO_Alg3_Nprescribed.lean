-- Prove2me | Definitions.Def_GarberOLO_Alg3_Nprescribed
-- name    : GarberOLO_Alg3_Nprescribed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:53:40.57322+00:00
-- url     : https://prove2.me/theorems/040e0d03-87dd-47dd-a066-741de66e435b
-- title:
--   The prescribed number $N$ of Ellipsoid iterations
-- statement:
--   For the procedure constant $c$, a point $y$ and $\varepsilon > 0$,
--   $$N(y) = \max\Big\{1,\ \Big\lceil c\, d^2 \ln\frac{(\alpha+1)R + \|y\|}{\varepsilon}\Big\rceil\Big\},$$
--   the least positive integer with $N \ge c\, d^2 \ln\big(((\alpha+1)R + \|y\|)/\varepsilon\big)$, the requirement of Lemma 5.
--
--   Algorithm 2 runs the procedure at its current point with this $N$ ("$N$ is as prescribed in Lemma 5").
--
--   **Formalization Note** The ceiling of a negative number is taken to be $0$, so the outer maximum makes $N \ge 1$. The choice of the least admissible $N$ is a reading of "as prescribed".
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Lemma 5, p. 9; Algorithm 2, line 8, p. 12

import Mathlib
import Definitions.Def_GarberOLO_Alg3_Setting

namespace GarberOLO.Alg3

/-- **The number N of Ellipsoid iterations "as prescribed in Lemma 5"** (Reading 2).
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Lemma 5, p. 9: "a positive integer N ≥ c d² ln(((α + 1)R + ‖x‖)/ε), where c is a positive
universal constant"; Algorithm 2, line 8, p. 12: "where N is as prescribed in Lemma 5".

`Nprescribed S c ε y = max 1 ⌈c · d² · ln(((α + 1)R + ‖y‖)/ε)⌉`, the least positive integer
`N` with `N ≥ c d² ln(((α + 1)R + ‖y‖)/ε)`.

**Formalization Note.** (Reading 2.) Algorithm 2 runs the procedure at its current point `ỹ`
with this least admissible `N`; the constant `c` is a parameter. `⌈·⌉₊` is `Nat.ceil`, which is
`0` on negative reals; the outer `max 1` makes `N` a positive integer. `Real.log` is only
applied to positive arguments when `0 < ε`. -/
noncomputable def Nprescribed {d : ℕ} (S : Setting d) (c ε : ℝ)
    (y : EuclideanSpace ℝ (Fin d)) : ℕ :=
  max 1 ⌈c * (d : ℝ) ^ 2 * Real.log (((S.α + 1) * S.R + ‖y‖) / ε)⌉₊

end GarberOLO.Alg3


