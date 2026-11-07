-- Prove2me | Definitions.Def_SecondBestBT_IsSBB
-- name    : SecondBestBT_IsSBB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:40.915091+00:00
-- url     : https://prove2.me/theorems/996760b9-ba44-4104-80b5-3280051677db
-- title:
--   Strong (pointwise) budget balance on $T$
-- statement:
--   A mechanism is **strongly budget balanced** (SBB) on the type set $T$ if the payment collected from the buyer equals the revenue paid to the seller at every reported profile:
--   $$
--   p_B(s,b)=p_S(s,b)\qquad\text{for all } s,b\in T .
--   $$
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Definition 2.1, p.4

import Mathlib
import Definitions.Def_SecondBestBT_Mechanism

namespace SecondBestBT

/-- Strong (pointwise) budget balance on the type set `T` (Liu–Qin–Ren–Wang, arXiv:2606.03849,
held version sha256 17184930…, Definition 2.1, p.4): `p_B(s, b) = p_S(s, b)` for every reported
profile `(s, b)` of types in `T`. -/
def IsSBB (T : Set ℝ) (M : Mechanism) : Prop :=
  ∀ s ∈ T, ∀ b ∈ T, M.pB (s, b) = M.pS (s, b)

end SecondBestBT


