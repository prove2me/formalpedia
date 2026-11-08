-- Prove2me | Definitions.Def_AffDisp4n_encSimpleInput
-- name    : AffDisp4n_encSimpleInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:15.964066+00:00
-- url     : https://prove2.me/theorems/d1b85674-76fa-4ce2-887e-a7a85bce6a0c
-- title:
--   Encoding of the input of the construction of Lemma 2.2
-- statement:
--   The input of the construction of Lemma 2.2 is written as the number $m$, the table of the pairs $P$, and the affine functions and constants of the output form.
--
--   **Formalization Note** The paper fixes no encoding. This one is injective, and its length is polynomial in $m$ and at least $m$.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), Lemma 2.2, p.17

import Mathlib
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_AffDisp4n_vecWord
import Definitions.Def_AffDisp4n_SimpleOutput

namespace AffDisp4n

/-- The words of an affine function given by its coefficients. -/
def AffForm.tokens {m : ℕ} (ℓ : AffForm m) : List (List Bool) :=
  [vecWord ℓ.coef, [bitOf ℓ.κ]]

/-- The words of an output form: a tag, then the affine functions and the constants. -/
def SimpleOutput.tokens {m : ℕ} : SimpleOutput m → List (List Bool)
  | .affine ℓ => [[false]] ++ ℓ.tokens
  | .andType ℓ₁ ℓ₂ α β γ => [[true]] ++ ℓ₁.tokens ++ ℓ₂.tokens ++ [[bitOf α], [bitOf β], [bitOf γ]]

/-- **Encoding of the input of the construction of Lemma 2.2** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), Lemma 2.2, p.17: "Given these affine functions, we can construct in polynomial time"): the number `m`, the
table of the pairs `P`, and the affine functions of the output form.

**Formalization Note** The paper fixes no encoding. This one is injective, and its length is polynomial in
`m` and at least `m`. -/
def encSimpleInput (x : Σ m, Finset (Sym2 (Fin m)) × SimpleOutput m) : List (Fin 3) :=
  LowErrExt.encWords ([natWord x.1] ++ pairsWords x.2.1 ++ x.2.2.tokens)

end AffDisp4n


