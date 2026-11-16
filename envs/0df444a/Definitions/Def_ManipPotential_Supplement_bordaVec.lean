-- Prove2me | Definitions.Def_ManipPotential_Supplement_bordaVec
-- name    : ManipPotential_Supplement_bordaVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:58:17.059518+00:00
-- url     : https://prove2.me/theorems/f9a05445-b13d-4a53-aae0-f4ecde67ca71
-- title:
--   Normalized Borda vector $(1, \tfrac{m-2}{m-1}, \dots, \tfrac{1}{m-1}, 0)$
-- statement:
--   The **normalized Borda vector** is
--   $$s = \Bigl(1, \tfrac{m-2}{m-1}, \tfrac{m-3}{m-1}, \dots, \tfrac{1}{m-1}, 0\Bigr), \qquad s_j = \frac{m-j}{m-1}\ (j \in [m]).$$
--
--   **Formalization Note** 0-based: entry $j$ is $(m-1-j)/(m-1)$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.2, p.15

import Mathlib

namespace ManipPotential.Supplement

/-- The normalized Borda scoring vector `s = (1, (m−2)/(m−1), (m−3)/(m−1), …, 1/(m−1), 0)`
(Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.2, p.15).

**Formalization Note** 0-based: entry `j` is `(m − 1 − j)/(m − 1)`, the paper's
`s_{j+1} = (m − (j+1))/(m − 1)`. -/
noncomputable def bordaVec (m : ℕ) : Fin m → ℝ := fun j => ((m : ℝ) - 1 - j.val) / ((m : ℝ) - 1)

end ManipPotential.Supplement


