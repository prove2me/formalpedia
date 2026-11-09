-- Prove2me | Definitions.Def_ManipPotential_IsCommonJunction
-- name    : ManipPotential_IsCommonJunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:47:11.28774+00:00
-- url     : https://prove2.me/theorems/b911491e-d166-48ba-8302-4c7eb747cbaa
-- title:
--   Common junction
-- statement:
--   A **common junction** of a rule $g$ is a real profile lying in every winner closure: $P \in \bigcap_{j \in [m]} A_j$. Such a point (necessarily in $\Omega$) is approached arbitrarily closely by full-support rational profiles electing each candidate.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, "Common junctions and Sperner's lemma", p.30

import Mathlib
import Definitions.Def_ManipPotential_winnerClosure

namespace ManipPotential

/-- A common junction: a point of `⋂_j A_j` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Section 6, p.30). -/
def IsCommonJunction {m : ℕ} (g : (Ranking m → ℚ) → Fin m) (P : Ranking m → ℝ) : Prop :=
  ∀ j, P ∈ winnerClosure g j

end ManipPotential


