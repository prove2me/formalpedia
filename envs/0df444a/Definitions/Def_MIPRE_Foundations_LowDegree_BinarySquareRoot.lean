-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_BinarySquareRoot
-- name    : MIPRE_Foundations_LowDegree_BinarySquareRoot
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:35.191994+00:00
-- url     : https://prove2.me/theorems/a610cbf6-ddae-454c-aaad-4538919d6201
-- title:
--   Definitions of BinarySquareRoot: A polynomial-time square root in the binary cyclic group algebra For an odd-length coefficient vector, reading the…
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.BinarySquareRoot` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). A polynomial-time square root in the binary cyclic group algebra. For an odd-length coefficient vector, reading the doubled indices means reading the even positions followed by the odd positions. Splitting those two lists and appending them is polynomial-time in the ambient cost model. This implements the square-root step of self-dualization; it does not compute the inverse Gram element or the initial normal basis.
--
--   **Definitions** (6): `MIPRE.LowDegree.groupOfBits` (A binary coefficient list interpreted in the cyclic group algebra.); `MIPRE.LowDegree.rootBits` (The doubled-index permutation for an odd-length coefficient vector.); `MIPRE.LowDegree.rootBitsProg` (The coefficient square-root permutation, in polynomial time.); `MIPRE.LowDegree.splitParity` (Split a list into its even-position and odd-position subsequences.); `MIPRE.LowDegree.splitParityProg` (The parity split, with an ambient program and polynomial cost proof.); `_private.MIPRE.Foundations.LowDegree.BinarySquareRoot.0.MIPRE.LowDegree.splitParityStep`.
--
--   **Embedded lemmas** (7): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `coeff_groupOfBits`, `length_rootBits`, `length_splitParity`, `rootBitsProg_apply`, `splitParityProg_apply`, `splitParity_eq_foldr`, `splitParityStep_size`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.BinarySquareRoot` (`MIPRE/Foundations/LowDegree/BinarySquareRoot.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 8 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinarySquareRoot.lean; blueprint lem:binary-square-root-program

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinarySquareRoot.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize

/-!
# A polynomial-time square root in the binary cyclic group algebra

For an odd-length coefficient vector, reading the doubled indices means reading
the even positions followed by the odd positions. Splitting those two lists and
appending them is polynomial-time in the ambient cost model. This implements the
square-root step of self-dualization; it does not compute the inverse Gram element
or the initial normal basis.
-/

namespace MIPRE.LowDegree

open Cost

variable {α : Type*}

/-- Split a list into its even-position and odd-position subsequences. -/
def splitParity : List α → List α × List α
  | [] => ([], [])
  | a :: l => (a :: (splitParity l).2, (splitParity l).1)

theorem splitParity_eq_foldr (l : List α) :
    splitParity l = l.foldr (fun a s => (a :: s.2, s.1)) ([], []) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [splitParity, ih]

theorem length_splitParity (l : List α) :
    (splitParity l).1.length = (l.length + 1) / 2 ∧
    (splitParity l).2.length = l.length / 2 := by
  induction l with
  | nil => simp [splitParity]
  | cons a l ih =>
    change (splitParity l).2.length + 1 = (l.length + 1 + 1) / 2 ∧
      (splitParity l).1.length = (l.length + 1) / 2
    rw [ih.1, ih.2]
    constructor <;> omega

/-- The doubled-index permutation for an odd-length coefficient vector. -/
def rootBits (l : List α) : List α := (splitParity l).1 ++ (splitParity l).2

@[simp] theorem length_rootBits (l : List α) : (rootBits l).length = l.length := by
  have h := length_splitParity l
  simp only [rootBits, List.length_append, h.1, h.2]
  omega

section Programs

variable [SizedEncoding α]

noncomputable def splitParityStep :
    PolyTimeFun ((List α × List α) × α) (List α × List α) :=
  (PolyTimeFun.cons PolyTimeFun.snd (PolyTimeFun.snd.comp PolyTimeFun.fst)).pair
    (PolyTimeFun.fst.comp PolyTimeFun.fst)

theorem splitParityStep_size (s : List α × List α) (a : α) :
    esize (splitParityStep (s, a)) ≤ esize s +
      (Polynomial.X + 1 : Polynomial ℕ).eval (esize a) := by
  rcases s with ⟨e, o⟩
  simp [splitParityStep, esize_prod, esize_list_cons]
  omega

/-- The parity split, with an ambient program and polynomial cost proof. -/
noncomputable def splitParityProg : PolyTimeFun (List α) (List α × List α) :=
  PolyTimeFun.congr
    ((PolyTimeFun.foldlAdd splitParityStep (Polynomial.X + 1) splitParityStep_size).comp
      (PolyTimeFun.reverse.pair (PolyTimeFun.const ([], []))))
    splitParity (by
      intro l
      simp only [PolyTimeFun.comp_apply, PolyTimeFun.pair_apply, PolyTimeFun.reverse_apply,
        PolyTimeFun.const_apply, PolyTimeFun.foldlAdd_apply, List.foldl_reverse]
      exact (splitParity_eq_foldr l).symm)

@[simp] theorem splitParityProg_apply (l : List α) : splitParityProg l = splitParity l := rfl

/-- The coefficient square-root permutation, in polynomial time. -/
noncomputable def rootBitsProg : PolyTimeFun (List α) (List α) :=
  PolyTimeFun.append.comp splitParityProg

@[simp] theorem rootBitsProg_apply (l : List α) : rootBitsProg l = rootBits l := rfl

end Programs

section GroupAlgebra

variable {k : ℕ} [NeZero k]

/-- A binary coefficient list interpreted in the cyclic group algebra. -/
noncomputable def groupOfBits (l : BitStr) : AddMonoidAlgebra (ZMod 2) (ZMod k) :=
  .ofCoeff (Finsupp.onFinset Finset.univ (fun i => ofBool (l.getD i.val false))
    (fun i _ => Finset.mem_univ i))

@[simp] theorem coeff_groupOfBits (l : BitStr) (i : ZMod k) :
    (groupOfBits l).coeff i = ofBool (l.getD i.val false) := by
  simp [groupOfBits]

end GroupAlgebra

end MIPRE.LowDegree


