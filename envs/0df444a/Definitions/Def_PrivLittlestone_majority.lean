-- Prove2me | Definitions.Def_PrivLittlestone_majority
-- name    : PrivLittlestone_majority
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:28:43.377189+00:00
-- url     : https://prove2.me/theorems/3e9294c9-ffa0-4e26-a4b2-15bc3f893bc3
-- title:
--   Majority aggregation $\mathrm{Maj}(h_1,\dots,h_m)$
-- statement:
--   **Majority aggregation** labels $x$ by $1$ exactly when strictly more than half of $h_1(x), \dots, h_m(x)$ equal $1$; for odd $m$ this is the strict majority vote.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §5, p.9

import Mathlib

namespace PrivLittlestone

/-- **Majority aggregation** `Maj(h_1, …, h_m)` (He–He, *Private Online Learning of Littlestone
Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), §5, p.9):
the label `1` exactly when strictly more than half of the `m` classifiers vote `1` (for odd `m`,
the strict majority). -/
def majority {X : Type*} {m : ℕ} (h : Fin m → X → Bool) (x : X) : Bool :=
  decide (m < 2 * (Finset.univ.filter fun i => h i x = true).card)

end PrivLittlestone


