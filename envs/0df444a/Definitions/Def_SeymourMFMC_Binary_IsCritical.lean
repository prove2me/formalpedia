-- Prove2me | Definitions.Def_SeymourMFMC_Binary_IsCritical
-- name    : SeymourMFMC_Binary_IsCritical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T03:06:03.560892+00:00
-- url     : https://prove2.me/theorems/f18c1a64-9d84-4db1-8d5e-d7ec3bc36b21
-- title:
--   Critical clutter: E(mb(L)) = E(L)
-- statement:
--   A clutter $\mathbf L$ is **critical** if
--
--   $$
--   E(mb(\mathbf L)) = E(\mathbf L),
--   $$
--
--   that is, every element of $E(\mathbf L)$ lies in some minimum-cardinality member of the blocker. Critical Mengerian binary clutters are the subject of Section 4 of the paper.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 202, Section 3

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_ground
import Definitions.Def_SeymourMFMC_Binary_mb

namespace SeymourMFMC.Binary

/-- `IsCritical L`: `L` is **critical** (Seymour 1977, p. 202), i.e. `E(mb(L)) = E(L)`: every
element of `E(L)` lies in some minimum-cardinality member of the blocker. -/
def IsCritical {α : Type*} [DecidableEq α] (L : Finset (Finset α)) : Prop :=
  ground (mb L) = ground L

end SeymourMFMC.Binary


