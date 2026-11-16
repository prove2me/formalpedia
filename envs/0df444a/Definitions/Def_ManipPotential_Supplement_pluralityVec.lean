-- Prove2me | Definitions.Def_ManipPotential_Supplement_pluralityVec
-- name    : ManipPotential_Supplement_pluralityVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:57:30.569812+00:00
-- url     : https://prove2.me/theorems/57e2e7e0-6e9d-4ecf-bcf3-964ca60a5959
-- title:
--   Plurality scoring vector $(1,0,\dots,0)$
-- statement:
--   The **plurality scoring vector** is $s = (1, 0, \dots, 0)$: one point for the top position and none for the others.
--
--   **Formalization Note** 0-based: entry $0$ is $1$, all other entries are $0$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.2, p.15

import Mathlib

namespace ManipPotential.Supplement

/-- The plurality scoring vector `s = (1, 0, …, 0)` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 4.2, p.15; Section 4.1.1,
p.11).

**Formalization Note** 0-based: entry `0` (the paper's `s₁`) is `1`, every other entry is `0`. -/
def pluralityVec (m : ℕ) : Fin m → ℝ := fun j => if j.val = 0 then 1 else 0

end ManipPotential.Supplement


