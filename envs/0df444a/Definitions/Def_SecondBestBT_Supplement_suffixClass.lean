-- Prove2me | Definitions.Def_SecondBestBT_Supplement_suffixClass
-- name    : SecondBestBT_Supplement_suffixClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:34:31.171748+00:00
-- url     : https://prove2.me/theorems/2aa2694e-9edf-476c-a6e9-13d08c625494
-- title:
--   Suffix class $\mathcal S_{\mathbf r}$
-- statement:
--   For a ratio list $\mathbf r=(r_t,\dots,r_m)$, the **suffix class** $\mathcal S_{\mathbf r}$ is the set of achievable states whose ratio component is exactly $\mathbf r$, i.e. the achievable states of the form $(y;r_t,\dots,r_m)$. In particular $\mathcal S_{(0,\mathbf r)}$ is the class of achievable states whose ratio list is $0$ followed by $\mathbf r$ (global threshold $0$).
--
--   Any two states in the same suffix class are comparable under the dominance order.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 5.1, p.19

import Mathlib
import Definitions.Def_SecondBestBT_Supplement_IsAchievable

open scoped ENNReal

namespace SecondBestBT.Supplement

/-- The **suffix class** `S_r` of a ratio list `r = (r_t, …, r_m)` (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…, Section 5.1,
p.19): the set of achievable states whose ratio component is exactly `r`, i.e. the achievable
states of the form `(y ; r_t, …, r_m)`. `S_{(0,r)}` is `suffixClass α β (0 :: r)`. -/
def suffixClass (α β : ℝ) (r : List ℝ≥0∞) : Set (ℝ × List ℝ≥0∞) :=
  {ω | IsAchievable α β ω ∧ ω.2 = r}

end SecondBestBT.Supplement


