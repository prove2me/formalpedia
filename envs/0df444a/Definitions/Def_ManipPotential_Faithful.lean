-- Prove2me | Definitions.Def_ManipPotential_Faithful
-- name    : ManipPotential_Faithful
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:13.049992+00:00
-- url     : https://prove2.me/theorems/e64a8194-03d6-4afe-bbc9-1606c7088317
-- title:
--   Weighted faithfulness of a rule on rational profiles
-- statement:
--   Let $g$ assign a candidate to rational profiles $P \in \mathbb Q^{m!}_{\ge 0} \setminus \{0\}$. The rule $g$ is **(weighted) faithful** if for every ranking $r$ and every rational $a > 0$,
--   $$
--   g(a\,r) = \mathrm{top}_r C .
--   $$
--
--   **Formalization Note** $g$ is a total function on $\mathbb Q^{\mathcal L(C)}$; this axiom and the other two axioms of Lemma 6.2 query it only at nonnegative nonzero vectors, so its values elsewhere are irrelevant.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.2, p.26

import Mathlib
import Definitions.Def_ManipPotential_unitVec
import Definitions.Def_ManipPotential_Ranking_top

namespace ManipPotential

/-- (Weighted) faithfulness of a rule `g` on rational profiles (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Lemma 6.2, p.26): for every
ranking `r` and every rational `a > 0`, `g(a r) = top_r C`.

**Formalization Note** A rational profile is a vector `Ranking m → ℚ` (`P_r` = multiplicity of `r`);
`g` is total but only queried at nonnegative nonzero vectors. -/
def Faithful {m : ℕ} [NeZero m] (g : (Ranking m → ℚ) → Fin m) : Prop :=
  ∀ (r : Ranking m) (a : ℚ), 0 < a → g (a • unitVec r) = Ranking.top r

end ManipPotential


