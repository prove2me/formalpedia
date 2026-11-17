-- Prove2me | Definitions.Def_SecondBestBT_Supplement_Undominated
-- name    : SecondBestBT_Supplement_Undominated
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:35:42.183191+00:00
-- url     : https://prove2.me/theorems/ce7a2687-058a-49fe-8d54-2dfd424216a3
-- title:
--   Undominated state (Definition 5.2)
-- statement:
--   A state $\omega$ is **undominated** (for parameters $\alpha,\beta$) if no achievable state $\omega'$ satisfies $\omega\prec\omega'$.
--
--   The quantifier ranges over all achievable states: every $K$, every $\alpha$-weakly regular full-support seller, every buyer value, including ratio lists with infinite entries.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Definition 5.2, p.18

import Mathlib
import Definitions.Def_SecondBestBT_Supplement_IsAchievable
import Definitions.Def_SecondBestBT_Supplement_Dominated

open scoped ENNReal

namespace SecondBestBT.Supplement

/-- A state is **undominated** if no achievable state dominates it (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…, Definition 5.2,
p.18: "We call a state undominated if no other achievable state dominates it").

**Formalization Note** The quantifier ranges over every achievable state (any `K`, any
full-support `α`-weakly regular seller, any buyer value), not only those of one suffix class.
"Other" is automatic: `Dominated` is irreflexive. -/
def Undominated (α β : ℝ) (ω : ℝ × List ℝ≥0∞) : Prop :=
  ∀ ω' : ℝ × List ℝ≥0∞, IsAchievable α β ω' → ¬ Dominated ω ω'

end SecondBestBT.Supplement


