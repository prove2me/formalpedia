-- Prove2me | Definitions.Def_SeymourMFMC_Binary_IsInitial
-- name    : SeymourMFMC_Binary_IsInitial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T03:28:47.25454+00:00
-- url     : https://prove2.me/theorems/c2a52832-87ad-4ff1-8c90-9859232deb15
-- title:
--   Initial element: no x ∈ E(L) with x → y
-- statement:
--   An element $y \in E(\mathbf L)$ of a critical binary clutter is **initial** if there is no $x \in E(\mathbf L)$ with $x \to y$.
--
--   Every nontrivial critical Mengerian binary clutter has a member made of initial elements (4.6), while $Q_6$ has no initial element; this is the structural distinction behind the paper's main theorem.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 203, Section 4

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_ground
import Definitions.Def_SeymourMFMC_Binary_Arrow

namespace SeymourMFMC.Binary

/-- `IsInitial L y`: `y ∈ E(L)` is **initial** (Seymour 1977, p. 203): there is no `x ∈ E(L)`
with `x → y`. -/
def IsInitial {α : Type*} [DecidableEq α] (L : Finset (Finset α)) (y : α) : Prop :=
  y ∈ ground L ∧ ∀ x ∈ ground L, ¬ Arrow L x y

end SeymourMFMC.Binary


