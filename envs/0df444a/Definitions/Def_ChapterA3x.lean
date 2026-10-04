-- Prove2me | Definitions.Def_ChapterA3x
-- name    : ChapterA3x
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T08:17:43.559986+00:00
-- url     : https://prove2.me/theorems/327cfdb8-709e-4d22-a95e-61d63b3993e2
-- title:
--   Chapter A3x
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA3x.lean`): generated def bundle for ChapterA3x. See BookProof/ChapterA3x.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA3x.lean

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3o
import Definitions.Def_ChapterA4
import Mathlib


/-!
# Chapter A, §A.3 — Note 50 at `N = 3`: the mixed-symmetry summand

Source: `book.tex` §A.3, Note 50 (Weyl: finite-dimensional representations are
completely reducible) and Lemma 52.

`ChapterA3p` proved the **`N = 2`** instance of Note 50 outright, with no
`EXTERNAL` hypothesis: the tensor square splits as `V ⊗ V = Sym²V ⊕ Λ²V`,
because at `N = 2` the symmetrizer and the antisymmetrizer are already
complementary (`projSym 2 + projAnti 2 = 1`).

From `N = 3` on that is *false*: symmetric plus antisymmetric no longer exhaust
the tensor power, and the leftover **mixed-symmetry** part is what makes the
general Weyl statement non-trivial.  This file lands the concrete `N = 3`
complete-reducibility witness the plan asks for, again with **no `EXTERNAL`
hypothesis**:

  `V ⊗ V ⊗ V  =  Sym³V ⊕ Λ³V ⊕ Mixed`,

realized by the three pairwise-orthogonal idempotents `projSym 3`, `projAnti 3`
and `projMixed 3 := 1 - projSym 3 - projAnti 3`, each of them a full-Lorentz
subrepresentation, and with the mixed summand **genuinely non-zero**.

## Deliverables

* `projMixed` — the mixed-symmetry projector `1 - projSym N - projAnti N`, and
  `projSym_add_projAnti_add_projMixed`: the three sum to `1` by construction;
* `projMixed_idem` (`N ≥ 2`) — it is idempotent, hence a genuine projector;
* `projSym_mul_projMixed`, `projMixed_mul_projSym`, `projAnti_mul_projMixed`,
  `projMixed_mul_projAnti` (`N ≥ 2`) — orthogonality to the other two summands;
* `projMixed_diagGen_comm`, `projMixed_uniform_comm`,
  `projMixed_spinGenDiag_comm`, `projMixed_parityDiag_comm` — the mixed summand
  is a **full-Lorentz** subrepresentation (diagonal `Spin⁺` generators *and*
  diagonal parity), inherited from `ChapterA3n`/`ChapterA3o`;
* `projMixed_two_eq_zero` — at `N = 2` the mixed part is empty, recovering
  `ChapterA3p`;
* `projMixed_three_ne_zero` — at `N = 3` it is **not** empty: the diagonal entry
  at the tuple `(0,0,1)` equals `2/3 ≠ 0` (only the identity and the
  transposition `(0 1)` stabilize that tuple, contributing `2/6` to the
  symmetrizer and `0` to the antisymmetrizer);
* `tensorCube_complete_reducibility` — the bundled headline.

Everything is `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open Matrix
open scoped BigOperators

namespace BookProof.ChapterA3x

open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n BookProof.ChapterA3o

/-- The **mixed-symmetry projector** on `V^{⊗N}`: whatever the symmetrizer and
the antisymmetrizer leave over. -/
noncomputable def projMixed (N : ℕ) : MN N := 1 - projSym N - projAnti N



/-! ## Orthogonality and idempotence -/











/-! ## Full-Lorentz invariance of the mixed summand -/









/-! ## `N = 2` versus `N = 3` -/



/-! ### Entrywise formulas, used for the `N = 3` non-vanishing -/









end BookProof.ChapterA3x


