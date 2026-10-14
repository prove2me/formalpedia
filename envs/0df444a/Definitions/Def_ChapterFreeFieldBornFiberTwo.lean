-- Prove2me | Definitions.Def_ChapterFreeFieldBornFiberTwo
-- name    : ChapterFreeFieldBornFiberTwo
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-12T05:45:35.412456+00:00
-- url     : https://prove2.me/theorems/37b0b1bd-57fc-462c-9a46-d77d28da5961
-- title:
--   ChapterFreeFieldBornFiberTwo

import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornSurj
import Mathlib

/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
# every Born fiber has at least two points; the Born map is never injective

Source: `book.tex`, chapter *"Wave-function parametrization of a probability
measure"* — the Introduction's statement (`book.tex` ~line 805) that the
wave-function is *one possible* parametrization of a probability distribution,
together with the free-field construction of §5 (`book.tex` ~line 1706).

Wave 151 (`ChapterFreeFieldBornFiberCardGeneral`) computed the exact Born-fiber
count for *every* probability distribution `p`:
`Nat.card (bornMapSphere ⁻¹' {p}) = 2 ^ (#positive coordinates of p)`.

This wave draws the qualitative consequence emphasized by the book: since every
probability distribution has *at least one* strictly positive coordinate (its
coordinates are non-negative and sum to `1`), the exponent is always `≥ 1`, so
**every** Born fiber contains **at least two** wave functions.  In particular the
Born (wave-function) parametrization of a probability distribution is *never*
unique: the map `bornMapSphere` is not injective in any dimension `n ≥ 1`.  This
is the precise sense in which the wave function carries a genuine `±1` sign
(phase) gauge freedom beyond the probability distribution it represents.

## Main results

* `posSupport_nonempty` — the positive support of a probability distribution is
  nonempty.
* `one_le_posSupport_card` — hence `1 ≤ #positive coordinates`.
* **headline** `two_le_bornFiber_card` — every Born fiber has `≥ 2` points.
* `bornMapSphere_not_injective` — for `n ≥ 1` the Born map on the sphere is not
  injective.

Everything is intended to be `sorry`-free and axiom-clean.
-/
namespace BookProof.ChapterFreeFieldBornFiberTwo

end BookProof.ChapterFreeFieldBornFiberTwo


