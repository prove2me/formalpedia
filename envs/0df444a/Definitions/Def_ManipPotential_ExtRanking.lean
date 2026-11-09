-- Prove2me | Definitions.Def_ManipPotential_ExtRanking
-- name    : ManipPotential_ExtRanking
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:44:42.306193+00:00
-- url     : https://prove2.me/theorems/af607650-d436-4b94-a40d-9ffe706474f2
-- title:
--   External rankings $\mathcal L(C) \setminus L$
-- statement:
--   The **external rankings** are the rankings in $\mathcal L(C) \setminus L$, that is, every ranking other than the $m$ cyclic rankings $\ell_1, \dots, \ell_m$. Their coefficients in a profile are its external coordinates $y \in \mathbb R^{m! - m}$; since the $\ell_j$ are pairwise distinct, there are $m! - m$ external rankings.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, p.30

import Mathlib
import Definitions.Def_ManipPotential_ell

namespace ManipPotential

/-- The external rankings `L(C) \ L` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, p.30): every ranking other than the `m`
cyclic rankings `ℓ_j`. -/
abbrev ExtRanking (m : ℕ) [NeZero m] : Type := {s : Ranking m // ∀ j : Fin m, ell j ≠ s}

end ManipPotential


