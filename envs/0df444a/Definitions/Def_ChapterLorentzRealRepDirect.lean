-- Prove2me | Definitions.Def_ChapterLorentzRealRepDirect
-- name    : ChapterLorentzRealRepDirect
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T08:10:42.838978+00:00
-- url     : https://prove2.me/theorems/85266551-63c3-43e6-9d7e-1780ac2d5403
-- title:
--   Chapter LorentzRealRepDirect
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterLorentzRealRepDirect.lean`): generated def bundle for ChapterLorentzRealRepDirect. See BookProof/ChapterLorentzRealRepDirect.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterLorentzRealRepDirect.lean

import Definitions.Def_ChapterLorentzRealRep
import Definitions.Def_ChapterLorentzRealRepSum
import Definitions.Def_ChapterLorentzRealRepFull
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Mathlib


/-!
# Chapter "Real representations, CPT theorem and the relativistic position operator",
§"On the Lorentz, SL(2,C) and Pin(3,1) groups", **Lemma 52** — the four
representation spaces form an *internal direct sum*

Continuing `BookProof.ChapterLorentzRealRep`, `ChapterLorentzRealRepSum` and
`ChapterLorentzRealRepFull` (`book.tex` Lemma 52, line ~5560), which built the
four mutually Frobenius-orthogonal real representation spaces

* `WHalf` — the `(1/2,1/2)` vector representation (dimension `4`),
* `W10`   — the `(1,0)` representation (dimension `6`),
* `WPs`   — the pseudo-`(1/2,1/2)` representation (dimension `4`),
* `WTwo`  — the two discrete Majorana directions `span{iγ⁰, γ⁰γ⁵}` (dimension `2`),

and proved that their fourfold sup is *all* of `Matrix (Fin 4) (Fin 4) ℝ`
(`decomposition_top`) with `16 = 4 + 6 + 4 + 2` (`finrank_full_eq_add`).

Those earlier files certified the *internal direct sum* only through a dimension
count.  This file upgrades that to the genuine structural statement:
`DirectSum.IsInternal` of the family `WFam = ![WHalf, W10, WPs, WTwo]`, i.e. the
canonical map `⨁ᵢ WFam i → Matrix (Fin 4) (Fin 4) ℝ` is an isomorphism.  From it
we read off the two defining properties of an internal direct sum:

* **spanning** `iSup_WFam_eq_top` (`⨆ i, WFam i = ⊤`);
* **independence** `WFam_iSupIndep` (`iSupIndep WFam`);

and the headline `WFam_isInternal`.

The proof is the finite-dimensional bijectivity argument: the canonical map
`DirectSum.coeLinearMap WFam` is surjective (its range is `⨆ i, WFam i = ⊤`) and
its domain `⨁ᵢ WFam i` has dimension `∑ᵢ finrank (WFam i) = 16 = finrank of the
whole matrix algebra`, so a surjection between equidimensional finite spaces is a
bijection.

As requested this stays **off the gravity line** and **off the Hankel-transform
line** (only the Majorana representation spaces of the previous waves are used).

Everything is `sorry`-free and `axiom`-free.
-/

open Matrix Module

namespace BookProof.ChapterLorentzRealRepDirect

open BookProof.ChapterLorentzRealRep BookProof.ChapterLorentzRealRepSum
open BookProof.ChapterLorentzRealRepFull

/-- The family of the four real representation subspaces of `SL(2,ℂ)` inside the
`16`-dimensional matrix algebra. -/
noncomputable def WFam : Fin 4 → Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) :=
  ![WHalf, W10, WPs, WTwo]

/-
The fourfold supremum of the family is the whole matrix algebra.
-/


/-
The dimensions of the four summands add up to the dimension of the whole
matrix algebra (`4 + 6 + 4 + 2 = 16`).
-/


/-
**Internal direct sum.**  The four mutually orthogonal representation spaces
form an internal direct sum of the whole matrix algebra: the canonical map
`⨁ᵢ WFam i → Matrix (Fin 4) (Fin 4) ℝ` is an isomorphism.
-/






end BookProof.ChapterLorentzRealRepDirect


