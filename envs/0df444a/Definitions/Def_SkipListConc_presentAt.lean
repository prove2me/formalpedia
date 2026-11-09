-- Prove2me | Definitions.Def_SkipListConc_presentAt
-- name    : SkipListConc_presentAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:53.926318+00:00
-- url     : https://prove2.me/theorems/2e3d3e17-02c9-4572-bd8a-f25b3ee2a518
-- title:
--   Items present during the search of operation $t$
-- statement:
--   The items **present** during the search of operation $t$ of $\sigma$ are all items inserted at or before $t$, the target included. The target of an insertion sits at the conventional height $H_x(0)=1$ during its own search.
--
--   **Formalization Note** Positions are 0-based.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §1.1, pp.4–5

import Mathlib

namespace SkipListConc

/-- The items present during the search of operation `t` (0-based) of `σ` (Kapoor–Tanveer,
*Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript
(sha256 f82c3d35…6dab6c), §1.1, pp.4–5): every item inserted at or before position `t`.

**Formalization Note** The target of an insertion is included; it sits at the conventional height
`H_x(0) = 1` during its own search (p.5). -/
def presentAt {α : Type*} [DecidableEq α] (σ : List α) (t : ℕ) : Finset α :=
  (σ.take (t + 1)).toFinset

end SkipListConc


