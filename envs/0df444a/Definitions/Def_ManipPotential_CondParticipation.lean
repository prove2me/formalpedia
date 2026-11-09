-- Prove2me | Definitions.Def_ManipPotential_CondParticipation
-- name    : ManipPotential_CondParticipation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:44:58.903441+00:00
-- url     : https://prove2.me/theorems/d5101e08-de1a-47e5-9482-160628e89f33
-- title:
--   Conditional participation of a rule on rational profiles
-- statement:
--   A rule $g$ on rational profiles satisfies **conditional participation** if for every profile $P \in \mathbb Q^{m!}_{\ge 0}$, ranking $r$ and rational $a > 0$,
--   $$
--   P_r > 0 \ \Longrightarrow\ g(P + a\,r) \ \succeq_r\ g(P).
--   $$
--   Adding weight to a ranking that is already present never hurts that ranking.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.2, p.26

import Mathlib
import Definitions.Def_ManipPotential_unitVec
import Definitions.Def_ManipPotential_Ranking_WeaklyPrefers

namespace ManipPotential

/-- Conditional participation of a rule `g` on rational profiles (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.2, p.26): for every
profile `P ≥ 0`, ranking `r` and rational `a > 0`, if `P_r > 0` then `g(P + a r) ⪰_r g(P)`. -/
def CondParticipation {m : ℕ} (g : (Ranking m → ℚ) → Fin m) : Prop :=
  ∀ P : Ranking m → ℚ, 0 ≤ P → ∀ (r : Ranking m) (a : ℚ), 0 < a → 0 < P r →
    Ranking.WeaklyPrefers r (g (P + a • unitVec r)) (g P)

end ManipPotential


