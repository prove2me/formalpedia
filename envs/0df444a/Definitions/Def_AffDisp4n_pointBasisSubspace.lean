-- Prove2me | Definitions.Def_AffDisp4n_pointBasisSubspace
-- name    : AffDisp4n_pointBasisSubspace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:15.895724+00:00
-- url     : https://prove2.me/theorems/4c31f74e-3757-4497-a221-d278870df5f3
-- title:
--   Affine subspace represented by a point and a list of vectors
-- statement:
--   The affine subspace represented by a point $x_0$ and a list $B$ of vectors is $x_0 + \operatorname{span} B$. A helper writes the point, the length of the list, the vectors and a bit as words.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), proof of Lemma 2.2, p.17

import Mathlib
import Definitions.Def_AffDisp4n_vecWord

namespace AffDisp4n

/-- The **affine subspace represented by a point and a list of vectors** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), proof of Lemma 2.2, p.17: "we write an affine subspace U as u⃗₀ + V, where V is a linear
subspace, given by the point u⃗₀ ∈ U and a basis of V"): `x₀ + span B`. -/
noncomputable def pointBasisSubspace {k : ℕ} (x₀ : Fin k → ZMod 2) (B : List (Fin k → ZMod 2)) :
    AffineSubspace (ZMod 2) (Fin k → ZMod 2) :=
  AffineSubspace.mk' x₀ (Submodule.span (ZMod 2) {v | v ∈ B})

/-- The words of a point, a list of vectors and a bit: the point, the length of the list, the vectors,
the bit. -/
def subspaceTokens {k : ℕ} (x₀ : Fin k → ZMod 2) (B : List (Fin k → ZMod 2)) (b : ZMod 2) :
    List (List Bool) :=
  [vecWord x₀, natWord B.length] ++ B.map vecWord ++ [[bitOf b]]

end AffDisp4n


