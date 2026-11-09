-- Prove2me | Definitions.Def_ManipPotential_kappa
-- name    : ManipPotential_kappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:42:39.279533+00:00
-- url     : https://prove2.me/theorems/881f2425-23d9-4c49-a0db-8e1b1cb5f6e7
-- title:
--   $\kappa = 2\,m!\,\lambda^m$
-- statement:
--   With $\lambda = K + 1$,
--   $$
--   \kappa = 2\, m!\, \lambda^m ,
--   $$
--   the scalar in the perturbed-junction bound of Lemma 6.10.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.10, p.32

import Mathlib

namespace ManipPotential

/-- `κ = 2 m! λ^m` with `λ = K + 1` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.10, p.32). -/
noncomputable def kappa (m K : ℕ) : ℝ := 2 * (m.factorial : ℝ) * ((K : ℝ) + 1) ^ m

end ManipPotential


