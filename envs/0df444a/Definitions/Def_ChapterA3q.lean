-- Prove2me | Definitions.Def_ChapterA3q
-- name    : ChapterA3q
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T08:17:01.231231+00:00
-- url     : https://prove2.me/theorems/06a80769-99d3-4c2c-bfe4-e96043d2eaa7
-- title:
--   Chapter A3q
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA3q.lean`): generated def bundle for ChapterA3q. See BookProof/ChapterA3q.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA3q.lean

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3o
import Definitions.Def_ChapterA4
import Mathlib


/-!
# Chapter A, §A.3 — Note 50 / Lemma 52: general-`N` complete reducibility
(via the mixed-symmetry complement)

Source: `book.tex` §A.3, Note 50 (Weyl: finite-dimensional representations of
`SL(2,ℂ)` are completely reducible) and Lemma 52.

`ChapterA3n`/`ChapterA3o` built, for arbitrary `N`, the totally symmetric
projector `projSym N` and the totally antisymmetric projector `projAnti N`, both
full-Lorentz–invariant.  `ChapterA3p` recorded that at `N = 2` they are already
*complementary* (`projSym 2 + projAnti 2 = 1`), giving the concrete
`V ⊗ V = Sym²V ⊕ Λ²V`.

For `N ≥ 3` the symmetric and antisymmetric pieces no longer exhaust the tensor
power `V^{⊗N}`; the remainder carries the **mixed-symmetry** representations.
This file isolates that remainder as the complementary projector

  `projMixed N := 1 − projSym N − projAnti N`

and proves — *without* the `EXTERNAL` Weyl hypothesis — that the triple
`{projSym N, projAnti N, projMixed N}` is a **complete system of pairwise
orthogonal, idempotent, full-Lorentz–invariant projectors** for every `N ≥ 2`.
This is the general-`N` (mixed-symmetry) form of the complete-reducibility
payoff of Note 50, extending the `N = 2` headline of `ChapterA3p`.

## Deliverables

* `projMixed` — the mixed-symmetry complement `1 − projSym N − projAnti N`.
* Completeness `projSym_add_projAnti_add_projMixed` — the three sum to `1`.
* Orthogonality (`N ≥ 2`): `projSym_mul_projMixed`, `projMixed_mul_projSym`,
  `projAnti_mul_projMixed`, `projMixed_mul_projAnti` (all `= 0`).
* Idempotency (`N ≥ 2`): `projMixed_idem`.
* Full-Lorentz invariance: `projMixed_diagGen_comm`, `projMixed_uniform_comm`,
  and their §A.3 specializations `projMixed_spinGenDiag_comm`,
  `projMixed_parityDiag_comm`.
* `projMixed_two_eq_zero` — at `N = 2` the mixed piece is `0` (consistency with
  `ChapterA3p`).
* `tensorPow_complete_reducibility` — the bundled headline for arbitrary
  `N ≥ 2`: a complete orthogonal idempotent system realizing
  `V^{⊗N} = Sym^N V ⊕ Λ^N V ⊕ (mixed symmetry)`.

Everything is `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`), with **no `EXTERNAL` hypothesis**.
-/

open Matrix
open scoped BigOperators

namespace BookProof.ChapterA3q

open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o

/-- The **mixed-symmetry complement** `projMixed N = 1 − projSym N − projAnti N`
on the tensor power `V^{⊗N}`.  For `N = 2` it vanishes; for `N ≥ 3` it carries
the mixed-symmetry representations. -/
noncomputable def projMixed (N : ℕ) : MN N :=
  1 - projSym N - projAnti N

























end BookProof.ChapterA3q


