-- Prove2me | Definitions.Def_StaticCalendar_BinaryDemand
-- name    : StaticCalendar_BinaryDemand
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:52.131603+00:00
-- url     : https://prove2.me/theorems/819c4768-ffb8-4932-972b-949f2f764e3a
-- title:
--   $\{0,1\}$-valued demand
-- statement:
--   The demand is **integral** if under every law $D_S$, $S\in\mathcal S$, every quantity is almost surely $0$ or $1$. This is the setting of §2.1 and §2.2.1, and condition (i) of Theorem EC.1.
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, p.13; Theorem EC.1 (i), p.ec8; p.ec9

import Mathlib
import Definitions.Def_StaticCalendar_DemandModel

open MeasureTheory

namespace StaticCalendar

/-- `{0,1}`-demand, arXiv:1811.01077v5, p.13 and p.ec9 (condition (i) of Theorem EC.1): every demand
quantity is `0` or `1`. This is the integral case of the paper, covering single-purchase choice
(§2.1) and multiple purchases (§2.2.1). -/
def BinaryDemand {n m : ℕ} (I : DemandModel n m) : Prop :=
  ∀ S ∈ I.family, ∀ᵐ Q ∂I.D S, ∀ ij, Q ij = 0 ∨ Q ij = 1

end StaticCalendar


