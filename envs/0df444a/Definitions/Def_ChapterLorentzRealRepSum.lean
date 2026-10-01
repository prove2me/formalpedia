-- Prove2me | Definitions.Def_ChapterLorentzRealRepSum
-- name    : ChapterLorentzRealRepSum
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T10:33:19.186468+00:00
-- url     : https://prove2.me/theorems/029d5076-5c79-49f2-85ee-741361e97d22
-- title:
--   Chapter LorentzRealRepSum
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterLorentzRealRepSum.lean`): generated def bundle for ChapterLorentzRealRepSum. See BookProof/ChapterLorentzRealRepSum.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterLorentzRealRepSum.lean

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRep
import Mathlib


/-!
# Chapter "Real representations, CPT theorem and the relativistic position operator",
§"On the Lorentz, SL(2,C) and Pin(3,1) groups", **Lemma 52** — the three real
irreducible representations are mutually orthogonal and form an internal direct sum

Continuing `BookProof.ChapterLorentzRealRep` (Lemma 52, `book.tex` line ~5560),
which built the three explicit real representation spaces of `SL(2,C)` inside the
`4×4` Majorana matrix model:

* `WHalf` — the `(1/2,1/2)` vector representation, `dim 4`;
* `W10`   — the `(1,0)` representation, `dim 6`;
* `WPs`   — the pseudo-`(1/2,1/2)` representation, `dim 4`.

This file discharges the *distinctness* half of the classification: the three
representation spaces are **mutually orthogonal** in the Frobenius inner product
`⟨A, B⟩ = tr(Aᵀ B)`, and therefore their sum inside the `16`-dimensional space of
`4×4` real matrices is an **internal direct sum** of dimension `4 + 6 + 4 = 14`.

Concretely:

* `gram_half10R`/`gram_halfPsR`/`gram_10PsR` — every cross Frobenius pairing
  between two different bases vanishes (mutual orthogonality, decided over `ℤ`
  and cast to `ℝ`);
* `bAll`/`bAllR` — the concatenated `14`-element basis, whose Frobenius Gram
  matrix is `4·I` (`gram_allR`), hence `bAllR_linearIndependent`
  (the `14` matrices are linearly independent over `ℝ`);
* `span_bAllR_eq` — the span of the concatenated basis is exactly
  `WHalf ⊔ W10 ⊔ WPs`;
* `finrank_WHalf`/`finrank_W10`/`finrank_WPs` (`= 4, 6, 4`) and
  `finrank_sup` (`= 14`), with `finrank_sup_eq_add` exhibiting the
  dimension additivity `dim (WHalf ⊔ W10 ⊔ WPs) = dim WHalf + dim W10 + dim WPs`
  that certifies the internal direct sum.

As requested this stays **off the gravity line** and **off the Hankel-transform
line** (only the concrete Majorana matrices of `ChapterA3`, the discrete group
`Ω` of `ChapterPinOmega`, and the representation spaces of
`ChapterLorentzRealRep` are used).

Everything is `sorry`-free and `axiom`-free.
-/

open Matrix

namespace BookProof.ChapterLorentzRealRepSum

open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open Module

/-! ## Cross Frobenius orthogonality (over `ℤ`) -/







/-! ## Cross Frobenius orthogonality (over `ℝ`) -/







/-! ## The concatenated `14`-element basis -/

/-- The concatenation of the three bases `bHalf` (4), `b10` (6), `bPs` (4). -/
def bAll : Fin 14 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => bHalf 0
  | 1 => bHalf 1
  | 2 => bHalf 2
  | 3 => bHalf 3
  | 4 => b10 0
  | 5 => b10 1
  | 6 => b10 2
  | 7 => b10 3
  | 8 => b10 4
  | 9 => b10 5
  | 10 => bPs 0
  | 11 => bPs 1
  | 12 => bPs 2
  | 13 => bPs 3

/-- The concatenated basis over `ℝ`. -/
noncomputable def bAllR (i : Fin 14) : Matrix (Fin 4) (Fin 4) ℝ := castR (bAll i)







/-! ## The span of the concatenated basis is `WHalf ⊔ W10 ⊔ WPs` -/





/-! ## Dimensions -/











end BookProof.ChapterLorentzRealRepSum


