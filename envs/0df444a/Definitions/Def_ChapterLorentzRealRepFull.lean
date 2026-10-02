-- Prove2me | Definitions.Def_ChapterLorentzRealRepFull
-- name    : ChapterLorentzRealRepFull
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T14:20:36.459185+00:00
-- url     : https://prove2.me/theorems/aae37ebf-b7fe-4cd3-9d06-662dafeb4905
-- title:
--   Chapter LorentzRealRepFull
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterLorentzRealRepFull.lean`): generated def bundle for ChapterLorentzRealRepFull. See BookProof/ChapterLorentzRealRepFull.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterLorentzRealRepFull.lean

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRep
import Definitions.Def_ChapterLorentzRealRepSum
import Mathlib


/-!
# Chapter "Real representations, CPT theorem and the relativistic position operator",
§"On the Lorentz, SL(2,C) and Pin(3,1) groups", **Lemma 52** — the complete
orthogonal decomposition of the `16`-dimensional matrix algebra

Continuing `BookProof.ChapterLorentzRealRep` and
`BookProof.ChapterLorentzRealRepSum` (Lemma 52, `book.tex` line ~5560), which
built the three explicit real representation spaces of `SL(2,C)` inside the `4×4`
Majorana matrix model and showed they are mutually orthogonal (dimensions
`4 + 6 + 4 = 14`).

This file exhibits the **remaining two-dimensional summand** and thereby the
*complete* orthogonal decomposition of the full `16`-dimensional real matrix
algebra `Matrix (Fin 4) (Fin 4) ℝ`.  The missing directions are exactly the two
"discrete" Majorana matrices that generate the covering group `Ω`:

* `WTwo` — the real span of `{iγ⁰, γ⁰γ⁵}` (dimension `2`), the directions along
  which the discrete Pin subgroup `Ω = {±1, ±iγ⁰, ±γ⁰γ⁵, ±iγ⁵}` acts.

We prove:

* **conjugation invariance** `conj_inv_two` — conjugation by every `S ∈ Ω` maps
  each basis matrix of `WTwo` to `±` a basis matrix (a signed permutation),
  decidably over `ℤ`, and the `Submodule` form `WTwo_invariant`;
* **mutual orthogonality** — `WTwo` is Frobenius-orthogonal to `WHalf`, `W10`
  and `WPs` (`gram_two_halfR`/`gram_two_10R`/`gram_two_PsR`);
* **the concatenated `16`-element basis** `bFull`/`bFullR`, whose Frobenius Gram
  matrix is `4·I` (`gram_fullR`), hence `bFullR_linearIndependent`;
* **the complete decomposition** `span_bFullR_eq`
  (`span (range bFullR) = WHalf ⊔ W10 ⊔ WPs ⊔ WTwo`),
  `decomposition_top` (this fourfold sum is *all* of `Matrix (Fin 4) (Fin 4) ℝ`),
  and the headline `finrank_full_eq_add`
  (`16 = dim WHalf + dim W10 + dim WPs + dim WTwo = 4 + 6 + 4 + 2`), certifying
  the complete internal direct sum.

As requested this stays **off the gravity line** and **off the Hankel-transform
line** (only the concrete Majorana matrices of `ChapterA3`, the discrete group
`Ω` of `ChapterPinOmega`, and the representation spaces of
`ChapterLorentzRealRep` are used).

Everything is `sorry`-free and `axiom`-free.
-/

open Matrix

namespace BookProof.ChapterLorentzRealRepFull

open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepSum
open Module

/-! ## The remaining two-element basis (integer model) -/

/-- Basis of the remaining representation space: `iγ⁰, γ⁰γ⁵`.
(Recall `γ^μ = -i(iγ^μ)`, so `γ⁰γ⁵ = -(iγ⁰)(iγ⁵)` is integral.) -/
def w2 : Fin 2 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => mgammaZ 0
  | 1 => -(mgammaZ 0 * mgamma5Z)

/-- Signed basis (`{±w2ᵢ}`) of the remaining representation space. -/
def SW2 : Finset (Matrix (Fin 4) (Fin 4) ℤ) :=
  (Finset.univ.image w2) ∪ (Finset.univ.image fun i => -w2 i)



/-! ## Conjugation invariance (signed-permutation form), over `ℤ` -/



/-! ## Frobenius Gram matrix, over `ℤ` -/



/-! ## Cross Frobenius orthogonality with the other three spaces (over `ℤ`) -/







/-! ## Real model -/

/-- Remaining basis over `ℝ`. -/
noncomputable def w2R (i : Fin 2) : Matrix (Fin 4) (Fin 4) ℝ := castR (w2 i)









/-! ## The remaining representation space -/

/-- The remaining two-dimensional representation space. -/
noncomputable def WTwo : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) :=
  Submodule.span ℝ (Set.range w2R)





/-! ## Every element of the signed basis casts into `WTwo` -/





/-! ## The concatenated `16`-element basis -/

/-- The concatenation of all four bases `bHalf` (4), `b10` (6), `bPs` (4),
`w2` (2), an integer basis of the whole `4×4` matrix algebra. -/
def bFull : Fin 16 → Matrix (Fin 4) (Fin 4) ℤ
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
  | 14 => w2 0
  | _ => w2 1

/-- The concatenated basis over `ℝ`. -/
noncomputable def bFullR (i : Fin 16) : Matrix (Fin 4) (Fin 4) ℝ := castR (bFull i)







/-! ## The span of the concatenated basis is the whole matrix algebra -/





/-! ## The complete decomposition -/









end BookProof.ChapterLorentzRealRepFull


