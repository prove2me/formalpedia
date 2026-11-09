-- Prove2me | Definitions.Def_ManipPotential_Omega
-- name    : ManipPotential_Omega
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:44:00.984321+00:00
-- url     : https://prove2.me/theorems/ee9e7205-9592-4e27-8f0f-32bb0e176d63
-- title:
--   $\Omega = \mathbb R^{m!}_{>0}$, full-support real profiles
-- statement:
--   $\Omega = \mathbb R^{m!}_{>0}$ is the set of real profiles in which every ranking has positive weight.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, "Common junctions and Sperner's lemma", p.30

import Mathlib
import Definitions.Def_ManipPotential_Ranking

namespace ManipPotential

/-- `Ω = ℝ^{m!}_{>0}`, the full-support real profiles (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, "Common junctions and
Sperner's lemma", p.30). -/
def Omega (m : ℕ) : Set (Ranking m → ℝ) := {P | ∀ r, 0 < P r}

end ManipPotential


