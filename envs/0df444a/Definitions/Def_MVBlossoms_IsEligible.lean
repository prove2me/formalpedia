-- Prove2me | Definitions.Def_MVBlossoms_IsEligible
-- name    : MVBlossoms_IsEligible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:41:15.430474+00:00
-- url     : https://prove2.me/theorems/3c23bd84-7333-48d7-a4c1-8fefa5b75159
-- title:
--   Eligible tenacity
-- statement:
--   A natural number $t$ is an **eligible tenacity** if $t$ is odd and
--
--   $$
--   t_m\le t<l_m .
--   $$
--
--   Theorem 3 is proved by induction over the eligible tenacities. An eligible tenacity exists only when $t_m<l_m$.
-- source:
--   Vazirani, A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length, Math. Oper. Res. 49(3) (2024), Definition 17, p.2027

import Mathlib
import Definitions.Def_MVBlossoms_lm
import Definitions.Def_MVBlossoms_tm

namespace MVBlossoms

/-- **Eligible tenacity.** Vazirani, *A Theory of Alternating Paths and Blossoms from the Perspective of Minimum Length*,
Math. Oper. Res. 49(3) (2024), Definition 17, p.2027: "An odd number t, with
tm ≤ t < lm, will be said to be an eligible tenacity."

**Formalization Note.** `t` is a natural number; the comparisons with `t_m` and `l_m` are in
`ℕ∞`. An eligible `t` exists only if `t_m < l_m`, the paper's standing case (pp.2018, 2027). -/
def IsEligible {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (t : ℕ) : Prop :=
  Odd t ∧ tm M ≤ (t : ℕ∞) ∧ (t : ℕ∞) < lm M

end MVBlossoms


