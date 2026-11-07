-- Prove2me | Definitions.Def_SecondBestBT_R3
-- name    : SecondBestBT_R3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:38.137707+00:00
-- url     : https://prove2.me/theorems/5b1bd1ca-575a-4b74-ba1f-3faff8fb62ed
-- title:
--   Allocation class $R_3(W)$: no trade at nonpositive surplus
-- statement:
--   $$
--   R_3(W)=\{x\in R_2(W)\ :\ x(s,b)=0\ \text{whenever } s\ge b\}.
--   $$
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 4.2, p.9

import Mathlib
import Definitions.Def_SecondBestBT_R2

namespace SecondBestBT

/-- The class `R3(W) := {x ∈ R2(W) : x(s, b) = 0 whenever s ≥ b}` of pointwise-monotone
allocations that never trade at nonpositive surplus (Liu–Qin–Ren–Wang, arXiv:2606.03849, held
version sha256 17184930…, Section 4.2, p.9). -/
def R3 (W : ℕ) : Set (ℕ → ℕ → ℝ) :=
  {x | x ∈ R2 W ∧ ∀ s ≤ W, ∀ b ≤ W, b ≤ s → x s b = 0}

end SecondBestBT


