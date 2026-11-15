-- Prove2me | Definitions.Def_LARLLL_BareissProgram
-- name    : LARLLL_BareissProgram
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T02:15:55.156917+00:00
-- url     : https://prove2.me/theorems/cf60346f-3d52-4121-8c86-10488662c79f
-- title:
--   Checked fraction-free Bareiss elimination program foundations
-- statement:
--   The original fraction-free Bareiss elimination data, total pivot loops, and matrix updates, retaining their checked implementation replacement equalities. These data are the actual programs used by the integer Gram-Schmidt and LLL construction. This source-faithful bundle introduces no assumption about full LLL bit complexity.
-- source:
--   Apache-2.0 original leanprover/hex libraries, ported and kernel checked in the existing native LLL development. Whole declaration commands were selected using the official Lean declaration/sketch and structural syntax oracles. Exact original module locations, source SHA-256 values, and unchanged checked data values are recorded in the validation receipt. Compiler csimp equality proofs and notices are preserved. Current source SHA-256: a01952b0b107d2ca21cb181eae4499091630000f5e12673df4ca73c148c61572.

import Definitions.Def_LARLLL_DeterminantEnumeration

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/






set_option autoImplicit true



section

/-!
Determinant of elementary row and column operations.

Building on the permutation-vector structure in `HexDeterminant.Permutation`,
this module reindexes the Leibniz sum to read off the determinant's reaction to
the elementary operations: `det_identity`, `det_rowSwap`, `det_rowScale`,
`det_rowAdd`, `det_transpose`, `cofactor_transpose`, and the column analogues
`det_colPermute_vector`, `det_colSwap`, `det_colAdd`.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}




















/-- `M` with column `dst` overwritten by a copy of column `src`. -/
 def _root_.Hex.Matrix.colAddDuplicate {R : Type u} {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) : Matrix R n n :=
  Matrix.ofFn fun r c => if c = dst then M[(r, src)] else M[(r, c)]



















/-- `M` with row `dst` overwritten by a copy of row `src` (row analogue of
`colAddDuplicate`). -/
 def _root_.Hex.Matrix.rowAddDuplicate {R : Type u} {n : Nat}
    (M : Matrix R n n) (src dst : Fin n) : Matrix R n n :=
  setRow M dst (getRow M src)

































































end Matrix
end Hex

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/






set_option autoImplicit true



section

/-!
Determinant column linearity for `hex-matrix`.

This module proves that `det` is multilinear in a single replaced column.
Working from the per-permutation product `detProduct` and signed term
`detTerm`, it establishes the additive `det_setCol_add`, the scalar
`det_setCol_smul`, and the finite-list/`Fin m` aggregated forms
`det_setCol_sum_list` and `det_setCol_sum_finRange`. It also collects the
duplicate-column/row vanishing lemmas (`det_eq_zero_of_col_eq`,
`det_eq_zero_of_row_eq`) and `det_setCol_add_otherCols` (column operations
preserve the determinant), plus the `columnSumMatrix` builder and the Fubini
sum-swap `List.foldl_add_comm` used by the Cauchy-Binet expansion.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}























/-- Square matrix whose `j`-th column is the finite linear combination of the
columns of `source` with coefficients from row `j` of `coeff`. -/
@[expose]
def columnSumMatrix {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) : Matrix R n n :=
  ofFn fun r j =>
    Fin.foldl m (fun acc k => acc + coeff[(j, k)] * source[(r, k)]) 0



















/-! # All-column ordered tuple expansion

Iterates `det_columnSumMatrix_expand_column` over every column to express
`det (columnSumMatrix source coeff)` as a sum over ordered column tuples.
Uses a list-based "left prefix" partial assignment, with a Fubini-style
sum-swap to align the iteration order with `columnTupleVectors`.
-/






end Matrix
end Hex

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/





set_option autoImplicit true



section

/-!
Gram matrices and standard-basis dot products.
-/

universe u v

namespace Vector











end Vector

namespace Hex

namespace Matrix

/-- Gram matrix of the rows of a dense matrix. -/
@[expose]
def gramMatrix [Mul R] [Add R] [OfNat R 0] (M : Matrix R n m) : Matrix R n n :=
  ofFn fun i j => (row M i).dotProduct (row M j)

/-- Entry characterization for the Gram matrix of the rows of a dense matrix. -/
@[grind =] theorem getElem_gramMatrix [Mul R] [Add R] [OfNat R 0]
    (M : Matrix R n m) (i j : Fin n) :
    (gramMatrix M)[i][j] = (row M i).dotProduct (row M j) := by
  rw [gramMatrix, getElem_ofFn]







end Matrix

end Hex

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/







set_option autoImplicit true



section

/-!
Ordered column-tuple expansion underlying Cauchy-Binet for `hex-matrix`.

This module expands the determinant of a column-sum matrix as a finite sum
over all ordered column tuples drawn from `Fin m`. It defines the
column-selected minor `columnTupleMatrix`, its product coefficient
`columnTupleCoeff`, the tuple enumerator `columnTupleVectors`, and proves the
summands of repeated columns vanish. The headline results are
`det_columnSumMatrix_eq_sum_columnTuples` (the Mathlib-free multilinearity
form) and `det_gramMatrix_eq_sum_columnTuples`, which specializes it to a row
Gram matrix. The bulk of the file is a suffix-based partial-assignment
recursion (`columnSumMatrixWithSuffix`) aligning the iteration with
`columnTupleVectors`.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-- Square submatrix obtained by selecting an ordered tuple of columns. -/
@[expose]
def columnTupleMatrix {R : Type u} {n m : Nat}
    (A : Matrix R n m) (cols : Fin n → Fin m) : Matrix R n n :=
  ofFn fun r c => A[(r, cols c)]



/-- Interpret an ordered column tuple vector as its column-selection function. -/
@[expose]
def columnTupleVectorFn {n m : Nat} (cols : Vector (Fin m) n) : Fin n → Fin m :=
  fun i => cols[i]









/-- Enumerate all ordered `n`-tuples of columns from `Fin m`. -/
@[expose]
def columnTupleVectors : (n m : Nat) → List (Vector (Fin m) n)
  | 0, _ => [#v[]]
  | n + 1, m =>
      (columnTupleVectors n m).flatMap fun pref =>
        (List.finRange m).map fun c =>
          insertAt c pref (Fin.last n)





 theorem _root_.Hex.Matrix.insertAt_last_injective_pair {α : Type u} {n : Nat}
    {c c' : α} {pref pref' : Vector α n}
    (h : insertAt c pref (Fin.last n) = insertAt c' pref' (Fin.last n)) :
    c = c' ∧ pref = pref' := by
  constructor
  · have hlast :
        (insertAt c pref (Fin.last n))[Fin.last n] =
          (insertAt c' pref' (Fin.last n))[Fin.last n] := by
      rw [h]
    rw [insertAt_get_self, insertAt_get_self] at hlast
    exact hlast
  · ext i hi
    let idx : Fin n := ⟨i, hi⟩
    have hidx :
        (insertAt c pref (Fin.last n))[idx.castSucc] =
          (insertAt c' pref' (Fin.last n))[idx.castSucc] := by
      rw [h]
    rw [insertAt_last_get_castSucc, insertAt_last_get_castSucc] at hidx
    exact hidx





/-- Product coefficient attached to an ordered column tuple in the Gram expansion. -/
@[expose]
def columnTupleCoeff {R : Type u} [Mul R] [OfNat R 1] {n m : Nat}
    (A : Matrix R n m) (cols : Vector (Fin m) n) : R :=
  Fin.foldl n (fun acc i => acc * A[(i, cols[i])]) 1

/-- The determinant summand associated to an ordered column tuple. -/
@[expose]
def columnTupleExpansionTerm {R : Type u} [Lean.Grind.Ring R] {n m : Nat}
    (A : Matrix R n m) (cols : Vector (Fin m) n) : R :=
  columnTupleCoeff A cols * det (columnTupleMatrix A (columnTupleVectorFn cols))









/-! # Suffix-based partial assignment

We use a SUFFIX-based parametrization (chosen represents right-fixed columns)
to align with the natural recursion of `columnTupleVectors`, which factors out
the LAST element of the suffix. After Fubini sum-swap, the inductive step
reduces to identity matching of the per-term values. -/

/-- Square matrix where the last `chosen.length` columns are fixed to selected
`source` columns indexed by `chosen` (in order), and the remaining left columns
stay in finite-sum form. -/
 def _root_.Hex.Matrix.columnSumMatrixWithSuffix
    {R : Type u} [Lean.Grind.CommRing R] {n m : Nat}
    (source coeff : Matrix R n m) (chosen : List (Fin m)) : Matrix R n n :=
  ofFn fun r j =>
    if h : n - chosen.length ≤ j.val then
      source[(r, chosen[j.val - (n - chosen.length)]'(by
        have : j.val < n := j.isLt; omega))]
    else
      Fin.foldl m (fun acc k => acc + coeff[(j, k)] * source[(r, k)]) 0











 def _root_.Hex.Matrix.assembleColumnsSuffix {n m : Nat} (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length)) (hk : chosen.length ≤ n) :
    Vector (Fin m) n :=
  ⟨(pref.toList ++ chosen).toArray, by
    simp [hk]⟩





 def _root_.Hex.Matrix.vectorLengthCast {α : Type u} {n k : Nat} (h : n = k)
    (v : Vector α n) : Vector α k :=
  match v with
  | ⟨xs, hx⟩ => ⟨xs, by simpa [h] using hx⟩







 def _root_.Hex.Matrix.partialColumnTupleCoeff {R : Type u} [Mul R] [OfNat R 1] {n m : Nat}
    (coeff : Matrix R n m) (chosen : List (Fin m))
    (pref : Vector (Fin m) (n - chosen.length)) : R :=
  Fin.foldl (n - chosen.length)
    (fun acc i => acc * coeff[((⟨i.val, by
      have hi : i.val < n - chosen.length := i.isLt
      omega⟩ : Fin n), pref[i])]) 1
























end Matrix
end Hex

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/










set_option autoImplicit true



section

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-! # Strictly-increasing column-tuple enumeration

The Cauchy-Binet sum-of-squares formula needs a Mathlib-free enumeration of the
"essentially distinct" column choices: each strictly increasing length-`n`
selection from `Fin m` represents one orbit of injective ordered tuples under
the action of permutations of `Fin n`. The enumeration below builds these
tuples by appending the new largest element, recursing on a `bound` parameter
that constrains the next entry to be strictly less than `bound`.
-/

/-- All strictly increasing length-`n` column tuples in `Fin m` whose entries
are all `< bound`. The recursion appends a new largest element `c < bound` and
recurses on the remaining prefix with the smaller bound `c.val`. -/
@[expose]
def selectedColumnTuplesUpTo (m : Nat) :
    (n : Nat) → (bound : Nat) → List (Vector (Fin m) n)
  | 0, _ => [#v[]]
  | n + 1, bound =>
      ((List.finRange m).filter (fun c : Fin m => decide (c.val < bound))).flatMap
        fun c =>
          (selectedColumnTuplesUpTo m n c.val).map fun pref => pref.push c

/-- Enumerate all strictly increasing length-`n` column selections from `Fin m`.
This list of orbit representatives drives the Cauchy-Binet grouping argument
that re-folds the ordered-tuple Gram expansion as a sum of squared minors. -/
@[expose]
def selectedColumnTuples (n m : Nat) : List (Vector (Fin m) n) :=
  selectedColumnTuplesUpTo m n m

/-- A column tuple is strictly increasing as a function `Fin n → Fin m`. -/
@[expose]
def IsStrictlyIncreasingColumnTuple {m n : Nat} (cols : Vector (Fin m) n) : Prop :=
  ∀ i j : Fin n, i.val < j.val → cols[i].val < cols[j].val





 theorem _root_.Hex.Matrix.getElem_push_castSucc {α : Type u} {n : Nat}
    (v : Vector α n) (x : α) (i : Fin n) :
    (v.push x)[i.castSucc] = v[i] := by
  rcases i with ⟨i, hi⟩
  simp [Fin.castSucc, Fin.castAdd, Fin.castLE, Vector.getElem_push_lt, hi]

 theorem _root_.Hex.Matrix.getElem_push_last_index {α : Type u} {n : Nat}
    (v : Vector α n) (x : α) :
    (v.push x)[Fin.last n] = x := by
  simp [Fin.last, Vector.getElem_push_eq]

/-- Pushing a new largest element preserves strict increase as long as the
old largest entry was still smaller than the new element. -/
 theorem _root_.Hex.Matrix.isStrictlyIncreasingColumnTuple_push {m n : Nat}
    (pref : Vector (Fin m) n) (c : Fin m)
    (hpref : IsStrictlyIncreasingColumnTuple pref)
    (hbound : ∀ i : Fin n, pref[i].val < c.val) :
    IsStrictlyIncreasingColumnTuple (pref.push c) := by
  intro i j hij
  rcases Nat.lt_succ_iff_lt_or_eq.mp j.isLt with hjlt | hjeq
  · -- j < n, so both i, j are inside `pref`.
    have hilt : i.val < n := by omega
    have hi_eq : i = (⟨i.val, hilt⟩ : Fin n).castSucc := by
      apply Fin.ext; rfl
    have hj_eq : j = (⟨j.val, hjlt⟩ : Fin n).castSucc := by
      apply Fin.ext; rfl
    rw [hi_eq, hj_eq, _root_.Hex.Matrix.getElem_push_castSucc, _root_.Hex.Matrix.getElem_push_castSucc]
    exact hpref ⟨i.val, hilt⟩ ⟨j.val, hjlt⟩ hij
  · -- j.val = n, so j is the last index.
    have hilt : i.val < n := by omega
    have hi_eq : i = (⟨i.val, hilt⟩ : Fin n).castSucc := by
      apply Fin.ext; rfl
    have hj_eq : j = Fin.last n := by
      apply Fin.ext; simpa using hjeq
    rw [hi_eq, hj_eq, _root_.Hex.Matrix.getElem_push_castSucc, _root_.Hex.Matrix.getElem_push_last_index]
    exact hbound ⟨i.val, hilt⟩











/-- The push map `pref ↦ pref.push c` is injective on prefixes for any fixed
last element `c`, since the popped vector recovers the prefix. -/
 theorem _root_.Hex.Matrix.push_left_injective {α : Type u} {n : Nat} (c : α) :
    Function.Injective fun pref : Vector α n => pref.push c := by
  intro pref pref' h
  have := congrArg Vector.pop h
  simpa using this

/-- Outer-list version of `Nodup` for the `flatMap` body that builds
`selectedColumnTuplesUpTo` from a list of "last column" candidates. -/
 theorem _root_.Hex.Matrix.selectedColumnTuplesUpTo_flatMap_nodup (m n : Nat) :
    ∀ (cs : List (Fin m)), cs.Nodup →
      (∀ c ∈ cs, (selectedColumnTuplesUpTo m n c.val).Nodup) →
      (cs.flatMap fun c =>
        (selectedColumnTuplesUpTo m n c.val).map fun pref => pref.push c).Nodup
  | [], _, _ => by simp
  | c :: cs, hnodup, hinner => by
      simp only [List.flatMap_cons]
      simp only [List.nodup_cons] at hnodup
      rw [List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · -- inner `(map ...)` for the head `c` is Nodup
        apply _root_.Hex.Matrix.list_nodup_map_of_injective (_root_.Hex.Matrix.push_left_injective c)
        exact hinner c (by simp)
      · -- suffix Nodup by IH
        exact selectedColumnTuplesUpTo_flatMap_nodup m n cs hnodup.2
          (fun c' hc' => hinner c' (List.mem_cons_of_mem c hc'))
      · -- disjointness: head produces last-element c, suffix produces last-element c' ∈ cs ⇒ c' ≠ c
        intro a hahead b hbsuffix hab
        rcases List.mem_map.mp hahead with ⟨pref, _, rfl⟩
        rcases List.mem_flatMap.mp hbsuffix with ⟨c', hc', hb⟩
        rcases List.mem_map.mp hb with ⟨pref', _, rfl⟩
        -- last entries match c and c' respectively, but c ≠ c'
        have hlast : (pref.push c)[Fin.last n] = (pref'.push c')[Fin.last n] := by
          rw [hab]
        rw [_root_.Hex.Matrix.getElem_push_last_index, _root_.Hex.Matrix.getElem_push_last_index] at hlast
        exact hnodup.1 (hlast ▸ hc')







/-! # Canonical sort and orbit factorization for injective column tuples

For the Cauchy-Binet orbit-grouping argument we need, for every injective
ordered column tuple `cols : Vector (Fin m) n`, a canonical factorization

```
cols[i] = (sortInjTuple cols)[(sortInjPerm cols)[i]]
```

where `sortInjTuple cols` is strictly increasing (i.e. lives in
`selectedColumnTuples n m`) and `sortInjPerm cols` is a permutation of
`Fin n` (i.e. lives in `permutationVectors n`). This gives a bijection
between injective `columnTupleVectors n m` entries and the product
`selectedColumnTuples n m × permutationVectors n`, which lets the orbit
sum group ordered minors by their canonical sorted column choice.

The implementation is rank-based: `sortInjPerm cols i` is the number of
columns in `cols` strictly smaller in value than `cols[i]`. For any
`cols`, this is `< n` because `cols[i]` is never strictly less than
itself; for *injective* `cols`, the rank is moreover a bijection on
`Fin n`. -/

/-- Count of indices whose `cols`-image has strictly smaller `Fin.val`
than that at `i`. This is the natural-number form of the rank. -/
@[expose]
def columnRankNat {m n : Nat} (cols : Vector (Fin m) n) (i : Fin n) : Nat :=
  ((List.finRange n).filter fun j => decide (cols[j].val < cols[i].val)).length

/-- The rank is always strictly less than `n`: index `i` itself is never
in the filter, so the filter is a strict sublist of `finRange n`. -/
theorem columnRankNat_lt {m n : Nat} (cols : Vector (Fin m) n) (i : Fin n) :
    columnRankNat cols i < n := by
  have hwit :
      ∃ x ∈ List.finRange n, ¬ (decide (cols[x].val < cols[i].val) = true) := by
    refine ⟨i, List.mem_finRange i, ?_⟩
    simp
  have hlt :=
    (List.length_filter_lt_length_iff_exists
      (p := fun j => decide (cols[j].val < cols[i].val))
      (l := List.finRange n)).mpr hwit
  simpa [columnRankNat, List.length_finRange] using hlt

/-- Canonical sorting permutation: for each index `i`, output the rank of
`cols[i]` (number of strictly smaller positions). For an injective `cols`
this is genuinely a permutation of `Fin n`; for a non-injective `cols` it
is still well-defined but may have repeated values. -/
@[expose]
def sortInjPerm {m n : Nat} (cols : Vector (Fin m) n) : Vector (Fin n) n :=
  Vector.ofFn fun i => ⟨columnRankNat cols i, columnRankNat_lt cols i⟩



/-- The canonical sorted version of `cols`: read `cols` through the inverse
of `sortInjPerm`. For an injective `cols` this is strictly increasing; for
a non-injective `cols` the value is well-defined but not meaningful. -/
@[expose]
def sortInjTuple {m n : Nat} (cols : Vector (Fin m) n) : Vector (Fin m) n :=
  Vector.ofFn fun r => cols[(inversePermutationVector (sortInjPerm cols))[r]]



























/-! # Forward injectivity of the sort/permutation pair -/



/-! # Reconstruction from `selectedColumnTuples × permutationVectors`

For a strictly-increasing `sel` and a permutation `perm`, the
"reconstruction" `Vector.ofFn (fun i => sel[perm[i]])` is itself
injective, and its canonical sort/permutation pair recovers
`(sel, perm)`. This is the inverse map of `sortInjTuple`/`sortInjPerm`. -/

/-- Reconstruction map: given a sorted choice and a permutation, build
an ordered column tuple. -/
@[expose]
def reconstructInjTuple {m n : Nat}
    (sel : Vector (Fin m) n) (perm : Vector (Fin n) n) : Vector (Fin m) n :=
  Vector.ofFn fun i => sel[perm[i]]



























/-! # Bijection wrappers -/



















/-! # General rectangular Cauchy--Binet -/


















































end Matrix
end Hex

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/






set_option autoImplicit true
section

/-!
Proof-free exact division for integer algorithms.

Algorithms using this operation establish divisibility in their proof layer and
avoid carrying that proof on the executable value path.  The native attachment
uses Lean's GMP-backed exact quotient; the Lean definition remains Euclidean
division so it is transparent to proofs.
-/

namespace HexArith.Int

/-- Integer exact division without a proof argument on the value path. -/
@[expose]
def exactDiv (num denom : @& Int) : Int := num / denom

@[simp] theorem exactDiv_zero (denom : Int) : exactDiv 0 denom = 0 := by
  simp [exactDiv]

/-- Under the divisibility invariant, `exactDiv` agrees with `Int.divExact`. -/
theorem exactDiv_eq_divExact {num denom : Int} (h : denom ∣ num) :
    exactDiv num denom = Int.divExact num denom h := by
  simp [exactDiv, Int.divExact_eq_ediv]

end HexArith.Int

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/





set_option autoImplicit true



section

/-!
Bordered leading minors used by Bareiss-style determinant arguments.
-/

namespace Hex

universe u

namespace Matrix

/-- Bordered Bareiss minor with the first `k` rows/columns and one extra
border row `i` and column `j`. For Bareiss applications `i` and `j` are in the
trailing part, but the constructor is total and leaves that side condition to
the invariant using it. -/
@[expose]
def borderedMinor (M : Matrix R n n) (k : Nat) (hk : k < n) (i j : Fin n) :
    Matrix R (k + 1) (k + 1) :=
  ofFn fun r c =>
    let rr : Fin n :=
      if hr : r.val < k then
        ⟨r.val, Nat.lt_trans hr hk⟩
      else
        i
    let cc : Fin n :=
      if hc : c.val < k then
        ⟨c.val, Nat.lt_trans hc hk⟩
      else
        j
    M[(rr, cc)]

/-- Interior-block case of the bordered-minor entry formula. -/
@[grind =] theorem borderedMinor_entry_lt_lt (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) (r c : Fin (k + 1)) (hr : r.val < k) (hc : c.val < k) :
    (borderedMinor M k hk i j)[r][c] =
      (let rr : Fin n := ⟨r.val, Nat.lt_trans hr hk⟩
       let cc : Fin n := ⟨c.val, Nat.lt_trans hc hk⟩
       M[(rr, cc)]) := by
  unfold borderedMinor
  rw [getElem_ofFn]
  simp [hr, hc]

/-- Border-column case of the bordered-minor entry formula. -/
@[grind =] theorem borderedMinor_entry_lt_last (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) (r : Fin (k + 1)) (hr : r.val < k) :
    (borderedMinor M k hk i j)[r][Fin.last k] =
      (let rr : Fin n := ⟨r.val, Nat.lt_trans hr hk⟩
       M[rr][j]) := by
  unfold borderedMinor
  rw [getElem_ofFn]
  simp [hr, Nat.lt_irrefl]

/-- Border-row case of the bordered-minor entry formula. -/
@[grind =] theorem borderedMinor_entry_last_lt (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) (c : Fin (k + 1)) (hc : c.val < k) :
    (borderedMinor M k hk i j)[Fin.last k][c] =
      (let cc : Fin n := ⟨c.val, Nat.lt_trans hc hk⟩
       M[i][cc]) := by
  unfold borderedMinor
  rw [getElem_ofFn]
  simp [hc, Nat.lt_irrefl]

/-- Corner case of the bordered-minor entry formula. -/
@[grind =] theorem borderedMinor_entry_last_last (M : Matrix R n n) (k : Nat) (hk : k < n)
    (i j : Fin n) :
    (borderedMinor M k hk i j)[Fin.last k][Fin.last k] = M[i][j] := by
  unfold borderedMinor
  rw [getElem_ofFn]
  simp [Nat.lt_irrefl]





end Matrix

end Hex

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/








set_option autoImplicit true



section

/-!
Executable Bareiss determinant algorithm for `hex-matrix`.

This module implements fraction-free Bareiss elimination over `Int` in two
layers: a no-pivot recurrence that follows the standard exact-division update,
and a public row-pivoting wrapper that swaps in a nonzero pivot when needed and
tracks the resulting determinant sign. The Mathlib-free layer exposes the
executable data and state needed by later bridge proofs; it does not expose a
theorem identifying the executable Bareiss determinant with the generic
Leibniz determinant.
-/

namespace Hex

universe u

namespace Matrix

variable {R : Type u} {n : Nat}

/-- Output of an executable Bareiss elimination pass. -/
structure BareissData (R : Type u) (n : Nat) where
  /-- Terminal matrix produced by the Bareiss pass. When `singularStep = none`,
  `BareissData.det` reads the last diagonal entry of this matrix, with the
  row-swap sign applied; for `n = 0`, the empty diagonal contributes `1`. -/
  matrix : Matrix R n n
  /-- Number of row swaps performed by pivoting. Even parity contributes sign
  `1`; odd parity contributes sign `-1`. -/
  rowSwaps : Nat
  /-- The first elimination step that found a zero pivot and no replacement
  row. A value `some k` records that singular step and makes
  `BareissData.det` return `0`; `none` means the run reached the terminal
  diagonal encoding. -/
  singularStep : Option Nat

namespace BareissData

/-- The determinant sign contributed by the recorded row swaps. -/
@[expose]
def sign [One R] [Neg R] (data : BareissData R n) : R :=
  if data.rowSwaps % 2 = 0 then 1 else -1

@[expose]
def lastDiag? (M : Matrix R n n) : Option R :=
  match n with
  | 0 => none
  | k + 1 =>
      let i : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
      some M[(i, i)]

/-- The determinant encoded by a Bareiss elimination result. -/
@[expose]
def det [Zero R] [One R] [Neg R] [Mul R] (data : BareissData R n) : R :=
  match data.singularStep with
  | some _ => 0
  | none =>
      match lastDiag? data.matrix with
      | some d => data.sign * d
      | none => data.sign







end BareissData

/-- Internal state of the no-pivot Bareiss recurrence, exposed read-only for
the Mathlib-side determinant proof. -/
structure BareissState (R : Type u) (n : Nat) where
  /-- Current elimination step. The next update, if any, uses this row and
  column as the pivot position. -/
  step : Nat
  /-- Current matrix carried by the Bareiss recurrence. Its terminal value is
  copied into `BareissData.matrix` by `finish`. -/
  matrix : Matrix R n n
  /-- Previous nonzero pivot used as the exact-division denominator; initially
  `1`. -/
  prevPivot : R
  /-- Number of row swaps already performed by the pivoting wrapper. Even
  parity contributes determinant sign `1`; odd parity contributes sign `-1`. -/
  rowSwaps : Nat
  /-- First step at which the recurrence found a zero pivot and could not
  continue. A value `some k` is terminal evidence for the determinant-zero
  encoding; `none` means no singular step has been recorded. -/
  singularStep : Option Nat

/-- Compatibility alias for the exact-division primitive now owned by
`hex-arith`. New code should use `HexArith.Int.exactDiv`. -/
abbrev exactDiv (num denom : @& Int) : Int := HexArith.Int.exactDiv num denom

/-- When divisibility is known, `exactDiv` is the GMP-backed exact quotient. -/
-- @[grind]-excluded: RHS `Int.divExact num denom h` mentions the divisibility
-- proof term `h`, which `grind =` cannot instantiate from the LHS pattern.
theorem exactDiv_eq_divExact {num denom : Int} (h : denom ∣ num) :
    exactDiv num denom = Int.divExact num denom h := by
  exact HexArith.Int.exactDiv_eq_divExact h

/-- Search column `col` for a nonzero pivot at or below `start`. -/
@[expose]
def findPivotAux [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n) (start fuel : Nat) :
    Option (Fin n) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if h : start < n then
        let i : Fin n := ⟨start, h⟩
        if M[(i, col)] = 0 then
          findPivotAux M col (start + 1) fuel
        else
          some i
      else
        none

/-- Search column `col` for a nonzero pivot at or below `start`. -/
@[expose]
def findPivot? [Zero R] [DecidableEq R]
    (M : Matrix R n n) (col : Fin n) (start : Nat) :
    Option (Fin n) :=
  findPivotAux M col start (n - start)

















/-- Apply one Bareiss update step to the trailing submatrix strictly below and
to the right of the current pivot.

Rows at or above the pivot (`i ≤ k`) are left untouched, and only the rows below
the pivot are rebuilt. The pivot row is read once into `pivotRow` before the
scatter (it is never mutated, since only rows `i > k` change). This
`mapRowsIdx` form is the reference the entry lemmas reduce through; compiled
code runs the per-entry in-place `stepMatrixWithImpl` via the `@[csimp]` below. -/
@[expose, specialize quot]
def stepMatrixWith [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (M : Matrix R n n) (k : Nat) (pivot prevPivot : R) :
    Matrix R n n :=
  if hk : k < n then
    let pivotRow := Matrix.getRow M ⟨k, hk⟩
    M.mapRowsIdx fun i row =>
      if k < i.val then
        let mik := row[k]'hk
        Fin.foldl n (fun r j =>
          r.modify j.val fun x =>
            if k < j.val then
              quot (pivot * x - mik * pivotRow[j]) prevPivot
            else if j.val = k then
              0
            else
              x) row
      else
        row
  else
    M

/-- Fast in-place implementation of `stepMatrixWith`: each updated row is written
through per-entry `Matrix.modifyEntries` updates of the flat backing buffer,
with no per-row materialization or write-back. Swapped in for compiled code by
the `@[csimp]` lemma below; `stepMatrixWith` stays the reference form for proofs. -/
@[expose, specialize quot]
def stepMatrixWithImpl [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (M : Matrix R n n) (k : Nat) (pivot prevPivot : R) :
    Matrix R n n :=
  if hk : k < n then
    let pivotRow := Matrix.getRow M ⟨k, hk⟩
    Fin.foldl n (fun A i =>
      if k < i.val then
        let mik := A[(i, (⟨k, hk⟩ : Fin n))]
        A.modifyEntries i.val fun j x =>
          if k < j.val then
            quot (pivot * x - mik * pivotRow[j]) prevPivot
          else if j.val = k then
            0
          else
            x
      else
        A) M
  else
    M

/-- The `stepMatrixWithImpl` fold leaves row `r` untouched when `r` is not among the
folded indices. -/
 theorem _root_.Hex.Matrix.stepImplFold_ne [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (k : Nat) (hk : k < n) (pivot prevPivot : R)
    (pivotRow : Vector R n) (r c : Fin n) :
    ∀ (xs : List (Fin n)) (A : Matrix R n n), (∀ t ∈ xs, t ≠ r) →
      (xs.foldl (fun A (i : Fin n) =>
        if k < i.val then
          A.modifyEntries i.val fun j x =>
            if k < j.val then
              quot (pivot * x - A[(i, (⟨k, hk⟩ : Fin n))] * pivotRow[j]) prevPivot
            else if j.val = k then 0
            else x
        else A) A)[r][c] = A[r][c] := by
  intro xs
  induction xs with
  | nil => intro A _; rfl
  | cons x xs ih =>
    intro A hne
    rw [List.foldl_cons, ih _ (fun t ht => hne t (List.mem_cons_of_mem _ ht))]
    by_cases hx : k < x.val
    · rw [if_pos hx, Matrix.getElem_modifyEntries,
        if_neg (fun hv => hne x List.mem_cons_self ((Fin.ext hv).symm))]
    · rw [if_neg hx]

/-- The `stepMatrixWithImpl` fold updates every member row from its original
entries. -/
 theorem _root_.Hex.Matrix.stepImplFold_mem [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (k : Nat) (hk : k < n) (pivot prevPivot : R)
    (pivotRow : Vector R n) (c : Fin n) :
    ∀ (xs : List (Fin n)), xs.Nodup → ∀ (A : Matrix R n n) (r : Fin n), r ∈ xs →
      (xs.foldl (fun A (i : Fin n) =>
        if k < i.val then
          A.modifyEntries i.val fun j x =>
            if k < j.val then
              quot (pivot * x - A[(i, (⟨k, hk⟩ : Fin n))] * pivotRow[j]) prevPivot
            else if j.val = k then 0
            else x
        else A) A)[r][c] =
      if k < r.val then
        (if k < c.val then
          quot (pivot * A[r][c] - A[(r, (⟨k, hk⟩ : Fin n))] * pivotRow[c]) prevPivot
        else if c.val = k then 0
        else A[r][c])
      else A[r][c] := by
  intro xs
  induction xs with
  | nil => intro _ A r hr; simp at hr
  | cons x xs ih =>
    intro hnd A r hr
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hr'
    · rw [_root_.Hex.Matrix.stepImplFold_ne quot k hk pivot prevPivot pivotRow r c xs _
        (fun t ht heq => (List.nodup_cons.mp hnd).1 (heq ▸ ht))]
      by_cases hx : k < r.val
      · rw [if_pos hx, if_pos hx, Matrix.getElem_modifyEntries, if_pos rfl]
      · rw [if_neg hx, if_neg hx]
    · have hxr : x ≠ r := fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ hr')
      have hrowr : ∀ cc : Fin n,
          (if k < x.val then
            A.modifyEntries x.val fun j y =>
              if k < j.val then
                quot (pivot * y - A[(x, (⟨k, hk⟩ : Fin n))] * pivotRow[j]) prevPivot
              else if j.val = k then 0
              else y
          else A)[r][cc] = A[r][cc] := by
        intro cc
        by_cases hx : k < x.val
        · rw [if_pos hx, Matrix.getElem_modifyEntries,
            if_neg (fun hv => hxr (Fin.ext hv.symm))]
        · rw [if_neg hx]
      rw [ih (List.nodup_cons.mp hnd).2 _ r hr']
      rw [show (if k < x.val then
            A.modifyEntries x.val fun j y =>
              if k < j.val then
                quot (pivot * y - A[(x, (⟨k, hk⟩ : Fin n))] * pivotRow[j]) prevPivot
              else if j.val = k then 0
              else y
          else A)[(r, (⟨k, hk⟩ : Fin n))] = A[(r, (⟨k, hk⟩ : Fin n))] from by
        rw [Matrix.getElem_pair_eq_nested (i := r) (j := (⟨k, hk⟩ : Fin n)),
          Matrix.getElem_pair_eq_nested (i := r) (j := (⟨k, hk⟩ : Fin n))]
        exact hrowr ⟨k, hk⟩]
      rw [hrowr c]

/-- `stepMatrixWithImpl` agrees entrywise with the same `ofFn` form as
`stepMatrixWith` (`stepMatrixWith_eq_ofFn`); the `@[csimp]` equality chains the two. -/
 theorem _root_.Hex.Matrix.stepMatrixImpl_eq_ofFn [Zero R] [Sub R] [Mul R]
    (quot : R → R → R) (M : Matrix R n n) (k : Nat) (pivot prevPivot : R) :
    stepMatrixWithImpl quot M k pivot prevPivot =
      Matrix.ofFn fun i j =>
        if hkij : k < i.val ∧ k < j.val then
          let colK : Fin n := ⟨k, Nat.lt_trans hkij.1 i.isLt⟩
          let rowK : Fin n := ⟨k, Nat.lt_trans hkij.2 j.isLt⟩
          quot (pivot * M[(i, j)] - M[(i, colK)] * M[(rowK, j)]) prevPivot
        else if k < i.val ∧ j.val = k then
          0
        else
          M[(i, j)] := by
  apply Matrix.ext_getElem
  intro i j
  rw [Matrix.getElem_ofFn]
  unfold stepMatrixWithImpl
  by_cases hk : k < n
  · rw [dif_pos hk]
    show (Fin.foldl n _ M)[i][j] = _
    rw [Fin.foldl_eq_finRange_foldl,
      _root_.Hex.Matrix.stepImplFold_mem quot k hk pivot prevPivot (Matrix.getRow M ⟨k, hk⟩) j
        (List.finRange n) (List.nodup_finRange n) M i (List.mem_finRange _)]
    simp only [Matrix.getElem_pair_eq_nested, Matrix.getElem_eq_getRow]
    rw [show (Matrix.getRow M ⟨k, hk⟩)[j] = (Matrix.getRow M ⟨k, hk⟩)[j.val] from rfl]
    grind
  · rw [dif_neg hk]
    have hik : ¬ k < i.val := fun h => hk (Nat.lt_trans h i.isLt)
    simp only [Matrix.getElem_pair_eq_nested]
    grind

/-- The in-place `stepMatrixWith` agrees entrywise with the `ofFn` form it replaces;
lets the existing entry lemmas reduce through the same body. -/
theorem stepMatrixWith_eq_ofFn [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (M : Matrix R n n) (k : Nat) (pivot prevPivot : R) :
    stepMatrixWith quot M k pivot prevPivot =
      Matrix.ofFn fun i j =>
        if hkij : k < i.val ∧ k < j.val then
          let colK : Fin n := ⟨k, Nat.lt_trans hkij.1 i.isLt⟩
          let rowK : Fin n := ⟨k, Nat.lt_trans hkij.2 j.isLt⟩
          quot (pivot * M[(i, j)] - M[(i, colK)] * M[(rowK, j)]) prevPivot
        else if k < i.val ∧ j.val = k then
          0
        else
          M[(i, j)] := by
  apply Matrix.ext_getElem
  intro i j
  rw [Matrix.getElem_ofFn]
  unfold stepMatrixWith
  by_cases hk : k < n
  · rw [dif_pos hk, Matrix.getElem_mapRowsIdx]
    by_cases hi : k < i.val
    · simp only [hi, if_pos, Vector.getElem_finFoldl_modify, Matrix.getElem_pair_eq_nested,
        Matrix.getElem_eq_getRow, Matrix.getRow, Fin.getElem_fin]
      grind
    · simp only [hi, Matrix.getElem_pair_eq_nested, Matrix.getElem_eq_getRow,
        Matrix.getRow, Fin.getElem_fin]
      grind
  · rw [dif_neg hk]
    have hik : ¬ k < i.val := fun h => hk (Nat.lt_trans h i.isLt)
    simp only [Matrix.getElem_pair_eq_nested, Matrix.getElem_eq_getRow, Matrix.getRow,
      Fin.getElem_fin]
    grind

@[csimp] theorem stepMatrixWith_eq_stepMatrixWithImpl : @stepMatrixWith = @stepMatrixWithImpl := by
  funext R _ _ _ quot n M k pivot prevPivot
  rw [stepMatrixWith_eq_ofFn, _root_.Hex.Matrix.stepMatrixImpl_eq_ofFn]

/-- Outside the trailing update region and pivot column below the pivot,
`stepMatrixWith` leaves entries unchanged. -/
@[grind =]
theorem stepMatrixWith_eq_of_not_update
    [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (M : Matrix R n n) (k : Nat) (pivot prevPivot : R) (i j : Fin n)
    (htrail : ¬ (k < i.val ∧ k < j.val))
    (hcol : ¬ (k < i.val ∧ j.val = k)) :
    (stepMatrixWith quot M k pivot prevPivot)[i][j] = M[i][j] := by
  rw [stepMatrixWith_eq_ofFn, Matrix.getElem_ofFn]; simp [htrail, hcol]



/-- `stepMatrixWith` clears the pivot column below the current pivot. -/
@[grind =]
theorem stepMatrixWith_pivot_col_below
    [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (M : Matrix R n n) (k : Nat) (pivot prevPivot : R) (i colK : Fin n)
    (hi : k < i.val) (hcolK : colK.val = k) :
    (stepMatrixWith quot M k pivot prevPivot)[i][colK] = 0 := by
  rw [stepMatrixWith_eq_ofFn, Matrix.getElem_ofFn]; simp [hi, hcolK]

/-- Entry formula for the trailing block updated by one Bareiss step. -/
-- @[grind]-excluded: `let`-wrapped RHS (`let colK := …; let rowK := …`) is
-- rejected by `grind =`; left untagged like the analogous Hensel step lemmas.
theorem stepMatrixWith_update_eq
    [Zero R] [Sub R] [Mul R] (quot : R → R → R)
    (M : Matrix R n n) (k : Nat) (pivot prevPivot : R) (i j : Fin n)
    (hi : k < i.val) (hj : k < j.val) :
    (stepMatrixWith quot M k pivot prevPivot)[i][j] =
      (let colK : Fin n := ⟨k, Nat.lt_trans hi i.isLt⟩
       let rowK : Fin n := ⟨k, Nat.lt_trans hj j.isLt⟩
       quot (pivot * M[i][j] - M[i][colK] * M[rowK][j]) prevPivot) := by
  rw [stepMatrixWith_eq_ofFn, Matrix.getElem_ofFn]; simp [hi, hj]

/-- If the current matrix entries already match bordered minors and exact
division evaluates to the next bordered minor, then one `stepMatrixWith` update
preserves the bordered-minor invariant at the updated entry. -/
-- @[grind]-excluded: one-shot bordered-minor invariant-preservation lemma whose
-- bespoke premises (`hpivot`/`hentry`/`hexact`) are not a characterising rewrite.
theorem stepMatrixWith_borderedMinor_update
    [Lean.Grind.CommRing R] (quot : R → R → R)
    (source current : Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) (hi : k < i.val) (hj : k < j.val) (pivot prevPivot : R)
    (hpivot :
      pivot =
        det (borderedMinor source k hk
          (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
          (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)))
    (hentry :
      current[i][j] = det (borderedMinor source k hk i j))
    (hleft :
      current[i][(⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)] =
        det (borderedMinor source k hk i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)))
    (htop :
      current[(⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)][j] =
        det (borderedMinor source k hk (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j))
    (hexact :
      quot
        (det (borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
            (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk i j) -
          det (borderedMinor source k hk i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j))
        prevPivot =
          det (borderedMinor source (k + 1) hnext i j)) :
    (stepMatrixWith quot current k pivot prevPivot)[i][j] =
      det (borderedMinor source (k + 1) hnext i j) := by
  rw [stepMatrixWith_update_eq quot current k pivot prevPivot i j hi hj]
  change
    quot
      (pivot * current[i][j] -
        current[i][(⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)] *
        current[(⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)][j])
      prevPivot =
        det (borderedMinor source (k + 1) hnext i j)
  rw [hpivot, hentry, hleft, htop]
  exact hexact

/-- Exact-division equation for one Bareiss bordered-minor update.

Once a determinant identity supplies the numerator as `nextMinor * prevPivot`,
this lemma packages it as the `quot` premise expected by
`stepMatrixWith_borderedMinor_update`. -/
-- @[grind]-excluded: proof-composition lemma gated on a determinant identity
-- premise (`hdesnanot`); not a local rewrite.
theorem exactQuot_borderedMinor_of_mul_eq [Lean.Grind.CommRing R]
    (quot : R → R → R) (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (source : Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) (hi : k < i.val) (hj : k < j.val) (prevPivot : R)
    (hprev_ne : prevPivot ≠ 0)
    (hdesnanot :
      det (borderedMinor source (k + 1) hnext i j) * prevPivot =
        det (borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
            (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk i j) -
          det (borderedMinor source k hk
            i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j)) :
    quot
        (det (borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
            (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk i j) -
          det (borderedMinor source k hk
            i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j))
        prevPivot =
      det (borderedMinor source (k + 1) hnext i j) := by
  let nextMinor := det (borderedMinor source (k + 1) hnext i j)
  let numerator :=
    det (borderedMinor source k hk
        (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
        (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
      det (borderedMinor source k hk i j) -
      det (borderedMinor source k hk
        i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
      det (borderedMinor source k hk
        (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j)
  have hnum : numerator = prevPivot * nextMinor := by
    dsimp [numerator, nextMinor]
    rw [← hdesnanot, Lean.Grind.CommRing.mul_comm]
  change quot numerator prevPivot = nextMinor
  rw [hnum, Lean.Grind.CommRing.mul_comm]
  exact hquot nextMinor prevPivot hprev_ne



/-- Array-backed state used by the executable row-pivoted Bareiss loop. -/
structure BareissArrayState (R : Type u) where
  step : Nat
  matrix : Array (Array R)
  prevPivot : R
  rowSwaps : Nat
  singularStep : Option Nat

/-- Read an entry from an `Array (Array R)` row-storage representation.

Exposed so downstream Mathlib-free clients (notably the shared scaled
Gram-Schmidt loop in `HexGramSchmidt.Int`) can speak about array storage
without re-deriving the conversion lemmas. -/
@[expose, inline] def getEntry [Zero R]
    (rows : Array (Array R)) (row col : Nat) : R :=
  (rows.getD row #[]).getD col 0

/-- Pack a `Matrix R n n` as an `Array (Array R)` of size `n × n`. The
representation used by the executable Bareiss array pass. -/
@[expose]
def matrixToRows [Zero R] (M : Matrix R n n) : Array (Array R) :=
  (Array.range n).map fun row =>
    (Array.range n).map fun col =>
      if hrow : row < n then
        if hcol : col < n then
          let i : Fin n := ⟨row, hrow⟩
          let j : Fin n := ⟨col, hcol⟩
          M[(i, j)]
        else
          0
      else
        0

/-- Unpack an `Array (Array R)` row-storage representation back into a
`Matrix R n n`. Inverse-on-the-left of `matrixToRows`. -/
@[expose]
def rowsToMatrix [Zero R] (rows : Array (Array R)) (n : Nat) : Matrix R n n :=
  Matrix.ofFn fun i j => getEntry rows i.val j.val

























section GenericBareiss

variable [Zero R] [One R] [Neg R] [Sub R] [Mul R] [DecidableEq R]
variable {quot : R → R → R}

/-- Bareiss elimination with row pivoting. If a column has no nonzero pivot,
the elimination aborts and the determinant is zero. -/
@[expose, specialize quot]
def pivotLoopWith (quot : R → R → R) (fuel : Nat)
    (state : BareissState R n) : BareissState R n :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if hDone : state.step + 1 < n then
        let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        let (M, swaps) :=
          if state.matrix[(k, k)] = 0 then
            match findPivot? state.matrix k (state.step + 1) with
            | some pivot => (rowSwap state.matrix k pivot, state.rowSwaps + 1)
            | none => (state.matrix, state.rowSwaps)
          else
            (state.matrix, state.rowSwaps)
        let pivot := M[(k, k)]
        if hp : pivot = 0 then
          { state with matrix := M, rowSwaps := swaps, singularStep := some state.step }
        else
          let next : BareissState R n :=
            { step := state.step + 1
              matrix := stepMatrixWith quot M state.step pivot state.prevPivot
              prevPivot := pivot
              rowSwaps := swaps
              singularStep := none }
          pivotLoopWith quot fuel next
      else
        state











/-- `bareissArrayStateWith` runs the matrix-level Bareiss elimination via `pivotLoopWith quot`
and repackages the reduced result as a `BareissArrayState R`, storing the matrix
row-by-row via `matrixToRows`. -/
@[expose, specialize quot]
def bareissArrayStateWith (quot : R → R → R) (M : Matrix R n n) : BareissArrayState R :=
  let state := pivotLoopWith quot n
    { step := 0
      matrix := M
      prevPivot := 1
      rowSwaps := 0
      singularStep := none }
  { step := state.step
    matrix := matrixToRows state.matrix
    prevPivot := state.prevPivot
    rowSwaps := state.rowSwaps
    singularStep := state.singularStep }

/-- `arraySign` is the determinant sign contributed by `rowSwaps` recorded row
swaps, `1` for an even count and `-1` for an odd count. -/
@[expose]
def arraySign (rowSwaps : Nat) : R :=
  if rowSwaps % 2 = 0 then 1 else -1

/-- `arrayLastDiag?` reads the last diagonal entry `(n-1, n-1)` of the reduced
rows, returning `none` when `n = 0`. -/
@[expose]
def arrayLastDiag? (rows : Array (Array R)) (n : Nat) : Option R :=
  match n with
  | 0 => none
  | k + 1 => some (getEntry rows k k)

/-- `bareissArrayDet` assembles the determinant value from the final array
state, returning `0` when elimination recorded a singular column and the signed
last diagonal entry otherwise. -/
@[expose]
def bareissArrayDet (state : BareissArrayState R) (n : Nat) : R :=
  match state.singularStep with
  | some _ => 0
  | none =>
      match arrayLastDiag? state.matrix n with
      | some d => arraySign state.rowSwaps * d
      | none => arraySign state.rowSwaps

/-- Package a Bareiss state as public elimination data. -/
@[expose]
def finish (state : BareissState R n) : BareissData R n :=
  { matrix := state.matrix
    rowSwaps := state.rowSwaps
    singularStep := state.singularStep }

/-- Bareiss elimination without pivoting. A zero pivot aborts and records the
singular step. -/
@[expose, specialize quot]
def noPivotLoopWith (quot : R → R → R) (fuel : Nat)
    (state : BareissState R n) : BareissState R n :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if hDone : state.step + 1 < n then
        let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        let pivot := state.matrix[(k, k)]
        if hp : pivot = 0 then
          { state with singularStep := some state.step }
        else
          let next : BareissState R n :=
            { step := state.step + 1
              matrix := stepMatrixWith quot state.matrix state.step pivot state.prevPivot
              prevPivot := pivot
              rowSwaps := state.rowSwaps
              singularStep := none }
          noPivotLoopWith quot fuel next
      else
        state

omit [One R] [Neg R] in
/-- With zero fuel, the no-pivot Bareiss loop returns its input state. -/
@[grind]
theorem noPivotLoopWith_zero_fuel (state : BareissState R n) :
    noPivotLoopWith quot 0 state = state := by
  rfl

omit [One R] [Neg R] in
/-- If the current step is already past the last update step, the no-pivot loop
returns its input state. -/
@[grind]
theorem noPivotLoopWith_done (fuel : Nat) (state : BareissState R n)
    (hDone : ¬ state.step + 1 < n) :
    noPivotLoopWith quot (fuel + 1) state = state := by
  simp [noPivotLoopWith, hDone]

omit [One R] [Neg R] in
/-- If the no-pivot loop sees a zero pivot before completion, it records the
current step as singular. -/
@[grind]
theorem noPivotLoopWith_of_singular (fuel : Nat) (state : BareissState R n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] = 0) :
    noPivotLoopWith quot (fuel + 1) state = { state with singularStep := some state.step } := by
  simp_all [noPivotLoopWith]

omit [One R] [Neg R] in
/-- If the current no-pivot Bareiss pivot is nonzero, one loop iteration applies
`stepMatrixWith quot`, advances the step, and recurses on the remaining fuel. -/
@[grind]
theorem noPivotLoopWith_of_regular (fuel : Nat) (state : BareissState R n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] ≠ 0) :
    noPivotLoopWith quot (fuel + 1) state =
      noPivotLoopWith quot fuel
        { step := state.step + 1
          matrix := stepMatrixWith quot state.matrix state.step state.matrix[state.step][state.step]
            state.prevPivot
          prevPivot := state.matrix[state.step][state.step]
          rowSwaps := state.rowSwaps
          singularStep := none } := by
  simp_all [noPivotLoopWith]

omit [One R] [Neg R] in
/-- Entries in rows already processed, or in columns strictly before the current
step, are unchanged by subsequent no-pivot loop iterations. -/
@[grind]
theorem noPivotLoopWith_matrix_entry_of_row_le_or_col_lt (fuel : Nat)
    (state : BareissState R n) (i j : Fin n)
    (hfixed : i.val ≤ state.step ∨ j.val < state.step) :
    (noPivotLoopWith quot fuel state).matrix[i][j] = state.matrix[i][j] := by
  induction fuel generalizing state with
  | zero =>
      simp [noPivotLoopWith]
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · let k : Fin n :=
          ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        by_cases hp : state.matrix[k][k] = 0
        · simp [noPivotLoopWith_of_singular (quot := quot) fuel state hDone hp]
        · rw [noPivotLoopWith_of_regular (quot := quot) fuel state hDone]
          · let next : BareissState R n :=
              { step := state.step + 1
                matrix := stepMatrixWith quot state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none }
            change (noPivotLoopWith quot fuel next).matrix[i][j] = state.matrix[i][j]
            have hnext : i.val ≤ next.step ∨ j.val < next.step := by
              cases hfixed with
              | inl hi =>
                  exact Or.inl (Nat.le_trans hi (Nat.le_succ state.step))
              | inr hj =>
                  exact Or.inr (Nat.lt_trans hj (Nat.lt_succ_self state.step))
            rw [ih next hnext]
            dsimp [next]
            apply stepMatrixWith_eq_of_not_update
            · intro htrail
              cases hfixed with
              | inl hi =>
                  exact Nat.not_lt_of_ge hi htrail.1
              | inr hj =>
                  exact Nat.not_lt_of_ge (Nat.le_of_lt hj) htrail.2
            · intro hcol
              cases hfixed with
              | inl hi =>
                  exact Nat.not_lt_of_ge hi hcol.1
              | inr hj =>
                  exact Nat.ne_of_lt hj hcol.2
          · simpa [k] using hp
      · simp [noPivotLoopWith_done (quot := quot) fuel state hDone]





omit [One R] [Neg R] in
/-- Once a no-pivot Bareiss state is already at the terminal step boundary,
additional fuel leaves it unchanged. -/
-- @[grind]-excluded: structural fixed-point lemma overlapping `noPivotLoopWith_done (quot := quot)`;
-- kept for manual fuel reasoning.
theorem noPivotLoopWith_id_at_done
    {n : Nat} (fuel : Nat) (state : BareissState R n)
    (hDone : ¬ state.step + 1 < n) :
    noPivotLoopWith quot fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ f _ih => exact noPivotLoopWith_done (quot := quot) f state hDone

omit [One R] [Neg R] in
/-- Once a no-pivot Bareiss state has recorded a zero pivot at the current
step, additional fuel leaves that singular fixed point unchanged. -/
-- @[grind]-excluded: structural fixed-point lemma with bespoke singular-state
-- premises; used once inside `noPivotLoopWith_add (quot := quot)`.
theorem noPivotLoopWith_id_at_singular_fixedpoint
    {n : Nat} (fuel : Nat) (state : BareissState R n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0)
    (hsing : state.singularStep = some state.step) :
    noPivotLoopWith quot fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ f _ih =>
      rw [noPivotLoopWith_of_singular (quot := quot) f state hDone hp]
      cases state
      simp at hsing ⊢
      exact hsing.symm

omit [One R] [Neg R] in
/-- Fuel composition for the no-pivot Bareiss loop: running `a + b` units of
fuel from `state` equals running `b` more units after `a` initial units. -/
-- @[grind]-excluded: fuel-composition (associativity) lemma; as a rewrite it
-- splits one loop into two and risks non-termination of grind's saturation.
theorem noPivotLoopWith_add
    {n : Nat} (a b : Nat) (state : BareissState R n) :
    noPivotLoopWith quot (a + b) state = noPivotLoopWith quot b (noPivotLoopWith quot a state) := by
  induction a generalizing state with
  | zero =>
      show noPivotLoopWith quot (0 + b) state = noPivotLoopWith quot b state
      simp
  | succ a' ih =>
      by_cases hDone : state.step + 1 < n
      · let k : Fin n :=
          ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        by_cases hp : state.matrix[k][k] = 0
        · have h_lhs :
              noPivotLoopWith quot (a' + 1 + b) state =
                {state with singularStep := some state.step} := by
            have : a' + 1 + b = (a' + b) + 1 := by omega
            rw [this]
            exact noPivotLoopWith_of_singular (quot := quot) (a' + b) state hDone hp
          have h_rhs_inner :
              noPivotLoopWith quot (a' + 1) state =
                {state with singularStep := some state.step} :=
            noPivotLoopWith_of_singular (quot := quot) a' state hDone hp
          rw [h_lhs, h_rhs_inner]
          symm
          let s' : BareissState R n := {state with singularStep := some state.step}
          have hDone_s' : s'.step + 1 < n := hDone
          have hp_s' : s'.matrix[(⟨s'.step, Nat.lt_of_succ_lt hDone_s'⟩ : Fin n)][
              (⟨s'.step, Nat.lt_of_succ_lt hDone_s'⟩ : Fin n)] = 0 := hp
          have hsing_s' : s'.singularStep = some s'.step := rfl
          exact noPivotLoopWith_id_at_singular_fixedpoint (quot := quot) b s' hDone_s' hp_s' hsing_s'
        · have h_lhs :
              noPivotLoopWith quot (a' + 1 + b) state =
                noPivotLoopWith quot (a' + b)
                  { step := state.step + 1
                    matrix := stepMatrixWith quot state.matrix state.step
                      state.matrix[k][k] state.prevPivot
                    prevPivot := state.matrix[k][k]
                    rowSwaps := state.rowSwaps
                    singularStep := none } := by
            have : a' + 1 + b = (a' + b) + 1 := by omega
            rw [this]
            exact noPivotLoopWith_of_regular (quot := quot) (a' + b) state hDone hp
          have h_rhs_inner :
              noPivotLoopWith quot (a' + 1) state =
                noPivotLoopWith quot a'
                  { step := state.step + 1
                    matrix := stepMatrixWith quot state.matrix state.step
                      state.matrix[k][k] state.prevPivot
                    prevPivot := state.matrix[k][k]
                    rowSwaps := state.rowSwaps
                    singularStep := none } :=
            noPivotLoopWith_of_regular (quot := quot) a' state hDone hp
          rw [h_lhs, h_rhs_inner]
          exact ih _
      · rw [noPivotLoopWith_id_at_done (quot := quot) (a' + 1 + b) state hDone]
        rw [noPivotLoopWith_id_at_done (quot := quot) (a' + 1) state hDone]
        exact (noPivotLoopWith_id_at_done (quot := quot) b state hDone).symm

omit [One R] [Neg R] in
/-- When a no-pivot Bareiss run records no singular step and has enough room,
the `step` field advances by exactly the amount of consumed fuel. -/
-- @[grind]-excluded: step-count accounting lemma with arithmetic-room and
-- no-singular premises; proof-internal, not a characterising rewrite.
theorem noPivotLoopWith_step_eq_add_of_singularStep_none
    {n : Nat} (fuel : Nat) (state : BareissState R n)
    (h_init : state.singularStep = none)
    (h_room : state.step + fuel + 1 ≤ n)
    (h_no_sing : (noPivotLoopWith quot fuel state).singularStep = none) :
    (noPivotLoopWith quot fuel state).step = state.step + fuel := by
  induction fuel generalizing state with
  | zero =>
      show state.step = state.step + 0
      omega
  | succ f ih =>
      have hDone : state.step + 1 < n := by omega
      by_cases hp : state.matrix[state.step][state.step] = 0
      · rw [noPivotLoopWith_of_singular (quot := quot) f state hDone hp] at h_no_sing
        simp at h_no_sing
      · rw [noPivotLoopWith_of_regular (quot := quot) f state hDone hp] at h_no_sing
        rw [noPivotLoopWith_of_regular (quot := quot) f state hDone hp]
        have h_next_room : state.step + 1 + f + 1 ≤ n := by omega
        have h_next_step := ih
          { step := state.step + 1
            matrix := stepMatrixWith quot state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot
            prevPivot := state.matrix[state.step][state.step]
            rowSwaps := state.rowSwaps
            singularStep := none }
          rfl h_next_room h_no_sing
        rw [h_next_step]
        show state.step + 1 + f = state.step + (f + 1)
        omega



/-- Initial state used by the no-pivot Bareiss recurrence. -/
@[expose]
def noPivotInitialState (M : Matrix R n n) : BareissState R n :=
  { step := 0
    matrix := M
    prevPivot := 1
    rowSwaps := 0
    singularStep := none }







/-- Run the row-pivoted Bareiss elimination and return the final elimination
data together with the swap/sign bookkeeping. -/
@[expose]
def bareissDataWith (quot : R → R → R) (M : Matrix R n n) : BareissData R n :=
  let state := bareissArrayStateWith quot M
  { matrix := rowsToMatrix state.matrix n
    rowSwaps := state.rowSwaps
    singularStep := state.singularStep }



/-- Determinant computed by the row-pivoted Bareiss algorithm. -/
@[expose, specialize quot]
def bareissWith (quot : R → R → R) (M : Matrix R n n) : R :=
  let state := bareissArrayStateWith quot M
  bareissArrayDet state n





end GenericBareiss

/-- Integer specialization of the generic Bareiss matrix update. -/
abbrev stepMatrix (M : Matrix Int n n) (k : Nat) (pivot prevPivot : Int) :
    Matrix Int n n :=
  stepMatrixWith exactDiv M k pivot prevPivot

/-- Integer specialization of the generic row-pivoted Bareiss loop. -/
abbrev pivotLoop (fuel : Nat) (state : BareissState Int n) : BareissState Int n :=
  pivotLoopWith exactDiv fuel state

/-- Integer specialization of the generic no-pivot Bareiss loop. -/
abbrev noPivotLoop (fuel : Nat) (state : BareissState Int n) : BareissState Int n :=
  noPivotLoopWith exactDiv fuel state



/-- Integer specialization returning no-pivot elimination data. -/
@[expose]
def bareissNoPivotData (M : Matrix Int n n) : BareissData Int n :=
  finish <| noPivotLoop n (noPivotInitialState M)



/-- Integer specialization returning row-pivoted elimination data. -/
abbrev bareissData (M : Matrix Int n n) : BareissData Int n :=
  bareissDataWith exactDiv M

/-- Integer specialization of the row-pivoted Bareiss determinant. -/
abbrev bareiss (M : Matrix Int n n) : Int :=
  bareissWith exactDiv M

/-! Integer proof-interface compatibility.  These theorems state their
conclusions through the traditional entry points while delegating every proof
to the generic `With` theorem. -/



@[grind =]
theorem stepMatrix_eq_of_not_update (M : Matrix Int n n) (k : Nat)
    (pivot prevPivot : Int) (i j : Fin n)
    (htrail : ¬ (k < i.val ∧ k < j.val))
    (hcol : ¬ (k < i.val ∧ j.val = k)) :
    (stepMatrix M k pivot prevPivot)[i][j] = M[i][j] :=
  stepMatrixWith_eq_of_not_update exactDiv M k pivot prevPivot i j htrail hcol



@[grind =]
theorem stepMatrix_pivot_col_below (M : Matrix Int n n) (k : Nat)
    (pivot prevPivot : Int) (i colK : Fin n)
    (hi : k < i.val) (hcolK : colK.val = k) :
    (stepMatrix M k pivot prevPivot)[i][colK] = 0 :=
  stepMatrixWith_pivot_col_below exactDiv M k pivot prevPivot i colK hi hcolK

theorem stepMatrix_update_eq (M : Matrix Int n n) (k : Nat)
    (pivot prevPivot : Int) (i j : Fin n) (hi : k < i.val) (hj : k < j.val) :
    (stepMatrix M k pivot prevPivot)[i][j] =
      (let colK : Fin n := ⟨k, Nat.lt_trans hi i.isLt⟩
       let rowK : Fin n := ⟨k, Nat.lt_trans hj j.isLt⟩
       exactDiv (pivot * M[i][j] - M[i][colK] * M[rowK][j]) prevPivot) :=
  stepMatrixWith_update_eq exactDiv M k pivot prevPivot i j hi hj













@[grind]
theorem noPivotLoop_zero_fuel (state : BareissState Int n) :
    noPivotLoop 0 state = state :=
  noPivotLoopWith_zero_fuel (quot := exactDiv) state

@[grind]
theorem noPivotLoop_done (fuel : Nat) (state : BareissState Int n)
    (hDone : ¬ state.step + 1 < n) :
    noPivotLoop (fuel + 1) state = state :=
  noPivotLoopWith_done (quot := exactDiv) fuel state hDone

@[grind]
theorem noPivotLoop_of_singular (fuel : Nat) (state : BareissState Int n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] = 0) :
    noPivotLoop (fuel + 1) state = { state with singularStep := some state.step } :=
  noPivotLoopWith_of_singular (quot := exactDiv) fuel state hDone hp

@[grind]
theorem noPivotLoop_of_regular (fuel : Nat) (state : BareissState Int n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] ≠ 0) :
    noPivotLoop (fuel + 1) state =
      noPivotLoop fuel
        { step := state.step + 1
          matrix := stepMatrix state.matrix state.step state.matrix[state.step][state.step]
            state.prevPivot
          prevPivot := state.matrix[state.step][state.step]
          rowSwaps := state.rowSwaps
          singularStep := none } :=
  noPivotLoopWith_of_regular (quot := exactDiv) fuel state hDone hp

@[grind]
theorem noPivotLoop_matrix_entry_of_row_le_or_col_lt (fuel : Nat)
    (state : BareissState Int n) (i j : Fin n)
    (hfixed : i.val ≤ state.step ∨ j.val < state.step) :
    (noPivotLoop fuel state).matrix[i][j] = state.matrix[i][j] :=
  noPivotLoopWith_matrix_entry_of_row_le_or_col_lt
    (quot := exactDiv) fuel state i j hfixed







theorem noPivotLoop_id_at_singular_fixedpoint (fuel : Nat)
    (state : BareissState Int n) (hDone : state.step + 1 < n)
    (hp : state.matrix[(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0)
    (hsing : state.singularStep = some state.step) :
    noPivotLoop fuel state = state :=
  noPivotLoopWith_id_at_singular_fixedpoint
    (quot := exactDiv) fuel state hDone hp hsing

theorem noPivotLoop_add (a b : Nat) (state : BareissState Int n) :
    noPivotLoop (a + b) state = noPivotLoop b (noPivotLoop a state) :=
  noPivotLoopWith_add (quot := exactDiv) a b state

theorem noPivotLoop_step_eq_add_of_singularStep_none (fuel : Nat)
    (state : BareissState Int n) (h_init : state.singularStep = none)
    (h_room : state.step + fuel + 1 ≤ n)
    (h_no_sing : (noPivotLoop fuel state).singularStep = none) :
    (noPivotLoop fuel state).step = state.step + fuel :=
  noPivotLoopWith_step_eq_add_of_singularStep_none
    (quot := exactDiv) fuel state h_init h_room h_no_sing











end Matrix
end Hex

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end


