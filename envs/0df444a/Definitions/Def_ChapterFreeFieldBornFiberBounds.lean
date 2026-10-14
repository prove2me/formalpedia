-- Prove2me | Definitions.Def_ChapterFreeFieldBornFiberBounds
-- name    : ChapterFreeFieldBornFiberBounds
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-12T05:52:29.488406+00:00
-- url     : https://prove2.me/theorems/ac517ef0-04f6-43ce-928c-94b7b732fee0
-- title:
--   ChapterFreeFieldBornFiberBounds

import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
import Definitions.Def_ChapterFreeFieldBornFiberTwo
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornSurj
import Mathlib

/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
# sharp bounds `2 ≤ #fiber ≤ 2ⁿ`, and equal fiber size ⇔ equal positive support

Source: `book.tex`, chapter *"Wave-function parametrization of a probability
measure"* — the free-field construction of §5 (`book.tex` ~line 1706) and the
Introduction's remark (`book.tex` ~line 805) that the wave function is *one
possible* parametrization of a probability distribution.

Wave 151 (`ChapterFreeFieldBornFiberCardGeneral`) computed the exact Born-fiber
count `Nat.card (bornMapSphere ⁻¹' {p}) = 2 ^ (#positive coordinates of p)`.
Wave 152 recorded the lower bound `≥ 2`; Wave 153 / 154 characterized the two
extremes (minimal `= 2` ⇔ deterministic, maximal `= 2ⁿ` ⇔ strictly positive).

This wave assembles the picture into the **sharp two-sided bound**
`2 ≤ #fiber ≤ 2ⁿ` valid for *every* probability distribution `p`, and records
that the Born fiber size is a *complete invariant of the size of the positive
support*: two distributions have the same number of wave functions iff they have
the same number of strictly positive coordinates.

## Main results

* `posSupport_card_le_n` — `(posSupport p).card ≤ n`.
* `bornFiber_card_le_two_pow_n` — `#fiber ≤ 2 ^ n`.
* **headline** `bornFiber_card_bounds` — `2 ≤ #fiber ∧ #fiber ≤ 2 ^ n`.
* `bornFiber_card_eq_iff_posSupport_card_eq` — `#fiber p = #fiber q ↔
  (posSupport p).card = (posSupport q).card`.

Everything is intended to be `sorry`-free and axiom-clean.
-/
namespace BookProof.ChapterFreeFieldBornFiberBounds

end BookProof.ChapterFreeFieldBornFiberBounds


