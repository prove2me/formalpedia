-- Prove2me | Definitions.Def_SeymourMFMC_Binary_mb
-- name    : SeymourMFMC_Binary_mb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T02:53:59.712911+00:00
-- url     : https://prove2.me/theorems/7ff68331-764d-431f-b54e-50ee88d917be
-- title:
--   mb(L) = {B ∈ b(L) : |B| = τ(L)}
-- statement:
--   The minimum-cardinality members of the blocker:
--
--   $$
--   mb(\mathbf L) = \{ B \in b(\mathbf L) : |B| = \tau(\mathbf L) \}.
--   $$
--
--   They define criticality and the relation $x \to y$.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 202, Section 3

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_blocker
import Definitions.Def_SeymourMFMC_Binary_tau

namespace SeymourMFMC.Binary

/-- `mb L` is `mb(L) = {B ∈ b(L) : |B| = τ(L)}` (Seymour 1977, p. 202), the minimum-cardinality
members of the blocker. -/
def mb {α : Type*} [DecidableEq α] (L : Finset (Finset α)) : Finset (Finset α) :=
  (blocker L).filter (fun B => B.card = tau L)

end SeymourMFMC.Binary


