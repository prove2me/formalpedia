-- Prove2me | Definitions.Def_GeomDRSub_drawLaw
-- name    : GeomDRSub_drawLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:13.151409+00:00
-- url     : https://prove2.me/theorems/020ff7a5-0236-434f-abcf-c6ef6feff9df
-- title:
--   Law of one round's draws $(I,S,U)$
-- statement:
--   The law of one round's randomness on $[d]\times\mathbb R\times\mathbb R$ is the product of the uniform distribution on the $d$ coordinates (for $I$), the uniform distribution on $[0,1]$ (for $S$), and the uniform distribution on $[0,1]$ (for the branch coin $U$ of the query point).
--
--   **Formalization Note** Coordinates are `Fin d`. For $d=0$ there is no coordinate to draw and this is the zero measure.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 5.1, p.17, Eq. (49)

import Mathlib

namespace GeomDRSub

open MeasureTheory ProbabilityTheory

/-- **The law of one round's draws `(I, S, U)`.** Aggarwal–Lu, arXiv:2610.00545, Eq. (49), p.17:
"Draw a coordinate `I` uniformly from `[d]` and a number `S` uniformly from `[0, 1]`", and the
branch of `Y` with probabilities `1 − p_I`, `p_I`.

`drawLaw d` is the product of the uniform law on `Fin d`, the uniform law on `[0,1]` (for `S`) and
the uniform law on `[0,1]` (for the branch coin `U`, see `queryPt`).

**Formalization Note.** Coordinates `[d]` are `Fin d`. For `d = 0` there is no coordinate to draw
and this measure is `0`; no probability space carries such a draw. -/
noncomputable def drawLaw (d : ℕ) : Measure (Fin d × ℝ × ℝ) :=
  (uniformOn (Set.univ : Set (Fin d))).prod
    ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))

end GeomDRSub


