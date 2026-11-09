-- Prove2me | Definitions.Def_ManipPotential_delta
-- name    : ManipPotential_delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:42:39.668994+00:00
-- url     : https://prove2.me/theorems/a4482a4d-a01b-47cb-9aa9-155a17f366b7
-- title:
--   $\delta = (m-2)/(\lambda^6 + m - 2)$
-- statement:
--   With $\lambda = K + 1$,
--   $$
--   \delta = \frac{m - 2}{\lambda^6 + m - 2}.
--   $$
--   For $m \ge 3$ this is a positive lower bound on the share of the winning cyclic ranking in an L-profile (Lemma 6.6, (9)).
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.6, Eq. (9), p.29

import Mathlib

namespace ManipPotential

/-- `δ = (m − 2)/(λ⁶ + m − 2)` with `λ = K + 1` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.6, Eq. (9), p.29). -/
def delta (m K : ℕ) : ℚ := ((m : ℚ) - 2) / (((K : ℚ) + 1) ^ 6 + (m : ℚ) - 2)

end ManipPotential


