-- Prove2me | Definitions.Def_LARLLL_DeterminantEnumeration
-- name    : LARLLL_DeterminantEnumeration
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T02:15:00.300342+00:00
-- url     : https://prove2.me/theorems/2ac2bd64-f0e6-4249-a8dd-90fe04427ecf
-- title:
--   Checked finite determinant enumeration foundations
-- statement:
--   Exact finite column and permutation enumeration together with the original determinant operations and supporting combinatorial identities used by the native LLL proof. This source-faithful bundle introduces no assumption about full LLL bit complexity.
-- source:
--   Apache-2.0 original leanprover/hex libraries, ported and kernel checked in the existing native LLL development. Whole declaration commands were selected using the official Lean declaration/sketch and structural syntax oracles. Exact original module locations, source SHA-256 values, and unchanged checked data values are recorded in the validation receipt. Compiler csimp equality proofs and notices are preserved. Current source SHA-256: 52525e269356e406c354688d077fb5f9ab759e83441a39123e77adaa96b88adf.

import Definitions.Def_LARLLL_GramSchmidtRational

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/






set_option autoImplicit true



section

/-!
Rational Gram-Schmidt API for `hex-gram-schmidt`.

This module wraps the executable kernel into the rational-valued `basis` and
`coeffs` of a `Matrix Rat n m` and proves their defining properties: the
leading row is untouched (`basis_zero`), distinct basis rows are orthogonal
(`basis_orthogonal`), the triangular factorization `b = coeffs · basis`
(`basis_decomposition`), and the unit-diagonal / lower-triangular shape of
`coeffs` (`coeffs_diag`, `coeffs_upper`, `coeffs_lower_projection`). It also
tracks how `basis` and `coeffs` transform under `Matrix.rowAdd` and adjacent
`Matrix.rowSwap` (the explicit re-orthogonalization formulas
`basis_rowSwap_adjacent_prev`/`_curr` and the coefficient updates), and proves
that orthogonalization preserves every row-prefix span (`basis_span`). These
are the rational facts the integer-cast layer lifts.
-/
namespace Hex
namespace GramSchmidt.Rat

/-- The Gram-Schmidt orthogonal basis for a rational matrix. -/
@[expose]
noncomputable def basis (b : Matrix Rat n m) : Matrix Rat n m :=
  GramSchmidt.basisMatrix b

/-- The Gram-Schmidt coefficient matrix for a rational input matrix. -/
@[expose]
noncomputable def coeffs (b : Matrix Rat n m) : Matrix Rat n n :=
  GramSchmidt.coeffMatrix b (basis b)

/-- Gram-Schmidt leaves the first row untouched: the leading basis row of a
rational matrix is its leading input row. -/
@[simp, grind =]
theorem basis_zero (b : Matrix Rat n m) (hn : 0 < n) :
    (basis b).row ⟨0, hn⟩ = b.row ⟨0, hn⟩ := by
  simpa [basis, GramSchmidt.basisMatrix, Matrix.row] using
    _root_.Hex.GramSchmidt.basisRows_head (b := b) hn



/-- The triangular factorization `b = coeffs · basis`, stated row by row: each
rational input row equals its orthogonalized basis row plus the
coefficient-weighted combination of the earlier basis rows. -/
theorem basis_decomposition (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    b.row ⟨i, hi⟩ =
      (basis b).row ⟨i, hi⟩ +
        GramSchmidt.prefixCombination (coeffs b) (basis b) i hi := by
  simpa [basis, coeffs] using
    _root_.Hex.GramSchmidt.basisMatrix_reconstruction_invariant (b := b) i hi











































/-- Orthogonalization preserves the row space of each prefix: the first `i + 1`
rational basis rows span exactly the vectors spanned by the first `i + 1` input
rows. -/
theorem basis_span (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    ∀ v : Vector Rat m,
      GramSchmidt.prefixSpan (basis b) i hi v ↔
        GramSchmidt.prefixSpan b i hi v := by
  have hmembersAll :
      ∀ (i : Nat) (hi : i < n),
        (∀ j : Fin (i + 1),
          GramSchmidt.prefixSpan b i hi ((GramSchmidt.prefixRows (basis b) i hi).row j)) ∧
        (∀ j : Fin (i + 1),
          GramSchmidt.prefixSpan (basis b) i hi ((GramSchmidt.prefixRows b i hi).row j)) := by
    intro i
    induction i with
    | zero =>
        intro hi
        constructor
        · intro j
          have hrow :
              (GramSchmidt.prefixRows (basis b) 0 hi).row j =
                (GramSchmidt.prefixRows b 0 hi).row j := by
            apply Vector.ext
            intro col hcol
            have hj : j.val = 0 := by omega
            have hb0 := congrArg (fun v : Vector Rat m => v[col]) (basis_zero b hi)
            simpa [GramSchmidt.prefixRows, Matrix.row, hj] using hb0
          rw [hrow]
          exact _root_.Hex.GramSchmidt.prefixSpan_row b 0 hi j
        · intro j
          have hrow :
              (GramSchmidt.prefixRows b 0 hi).row j =
                (GramSchmidt.prefixRows (basis b) 0 hi).row j := by
            apply Vector.ext
            intro col hcol
            have hj : j.val = 0 := by omega
            have hb0 := congrArg (fun v : Vector Rat m => v[col]) (basis_zero b hi)
            simpa [GramSchmidt.prefixRows, Matrix.row, hj] using hb0.symm
          rw [hrow]
          exact _root_.Hex.GramSchmidt.prefixSpan_row (basis b) 0 hi j
    | succ k ih =>
        intro hi
        have hk : k < n := Nat.lt_of_succ_lt hi
        have ihk := ih hk
        constructor
        · intro j
          by_cases hlt : j.val < k + 1
          · let jp : Fin (k + 1) := ⟨j.val, hlt⟩
            have hprev := ihk.1 jp
            have hmono := _root_.Hex.GramSchmidt.prefixSpan_mono_succ b k hi hprev
            have hrow :
                (GramSchmidt.prefixRows (basis b) (k + 1) hi).row j =
                  (GramSchmidt.prefixRows (basis b) k hk).row jp := by
              apply Vector.ext
              intro col hcol
              simp [GramSchmidt.prefixRows, Matrix.row, jp]
            rwa [hrow]
          · have hjlast : j.val = k + 1 := by omega
            let last : Fin n := ⟨k + 1, hi⟩
            let pc :=
              GramSchmidt.prefixCombination (coeffs b) (basis b) (k + 1) hi
            have hpc : GramSchmidt.prefixSpan b (k + 1) hi pc := by
              have hraw :=
                _root_.Hex.GramSchmidt.prefixSpan_strictRowCombination
                  (A := basis b) (B := b) (i := k + 1) (hi := hi)
                  (c := _root_.Hex.GramSchmidt.projectionCoeffVector (b.row last) (basis b)
                    (k + 1) (Nat.le_of_lt hi))
                  (by
                    intro row
                    let jp : Fin (k + 1) := row
                    have hprev := ihk.1 jp
                    have hmono := _root_.Hex.GramSchmidt.prefixSpan_mono_succ b k hi hprev
                    have hrow :
                        (_root_.Hex.GramSchmidt.strictPrefixRows (basis b) (k + 1)
                            (Nat.le_of_lt hi)).row row =
                          (GramSchmidt.prefixRows (basis b) k hk).row jp := by
                      apply Vector.ext
                      intro col hcol
                      simp [_root_.Hex.GramSchmidt.strictPrefixRows, GramSchmidt.prefixRows,
                        Matrix.row, jp]
                    rwa [hrow])
              simpa [pc, basis, coeffs,
                _root_.Hex.GramSchmidt.prefixCombination_eq_strictPrefixRowCombination] using hraw
            have hbrow : GramSchmidt.prefixSpan b (k + 1) hi (b.row last) := by
              simpa [GramSchmidt.prefixRows, Matrix.row, last, hjlast] using
                _root_.Hex.GramSchmidt.prefixSpan_row b (k + 1) hi j
            have hbasis_eq :
                ((GramSchmidt.prefixRows (basis b) (k + 1) hi).row j) =
                  b.row last + (-1 : Rat) • pc := by
              have hdec := basis_decomposition b (k + 1) hi
              apply Vector.ext
              intro col hcol
              have hdec_col := congrArg (fun v : Vector Rat m => v[col]) hdec
              simp [Vector.getElem_add, Vector.getElem_smul, pc, last, hjlast,
                GramSchmidt.prefixRows, Matrix.row] at hdec_col ⊢
              change ((basis b).getRow ⟨k + 1, hi⟩)[col] =
                (b.getRow ⟨k + 1, hi⟩)[col] +
                  (-1 : Rat) * (prefixCombination (coeffs b) (basis b) (k + 1) hi)[col]
              rw [hdec_col]
              grind
            rw [hbasis_eq]
            exact _root_.Hex.GramSchmidt.prefixSpan_add b (k + 1) hi hbrow
              (_root_.Hex.GramSchmidt.prefixSpan_smul b (k + 1) hi (-1) hpc)
        · intro j
          by_cases hlt : j.val < k + 1
          · let jp : Fin (k + 1) := ⟨j.val, hlt⟩
            have hprev := ihk.2 jp
            have hmono := _root_.Hex.GramSchmidt.prefixSpan_mono_succ (basis b) k hi hprev
            have hrow :
                (GramSchmidt.prefixRows b (k + 1) hi).row j =
                  (GramSchmidt.prefixRows b k hk).row jp := by
              apply Vector.ext
              intro col hcol
              simp [GramSchmidt.prefixRows, Matrix.row, jp]
            rwa [hrow]
          · have hjlast : j.val = k + 1 := by omega
            let last : Fin n := ⟨k + 1, hi⟩
            let pc :=
              GramSchmidt.prefixCombination (coeffs b) (basis b) (k + 1) hi
            have hpc : GramSchmidt.prefixSpan (basis b) (k + 1) hi pc := by
              have hraw :=
                _root_.Hex.GramSchmidt.prefixSpan_strictPrefix_vecMul
                  (M := basis b) (i := k + 1) (hi := hi)
                  (c := _root_.Hex.GramSchmidt.projectionCoeffVector (b.row last) (basis b)
                    (k + 1) (Nat.le_of_lt hi))
              simpa [pc, basis, coeffs,
                _root_.Hex.GramSchmidt.prefixCombination_eq_strictPrefixRowCombination] using hraw
            have hbasisrow :
                GramSchmidt.prefixSpan (basis b) (k + 1) hi ((basis b).row last) := by
              have hself := _root_.Hex.GramSchmidt.prefixSpan_row (basis b) (k + 1) hi j
              simpa [GramSchmidt.prefixRows, Matrix.row, last, hjlast] using hself
            have hb_eq :
                ((GramSchmidt.prefixRows b (k + 1) hi).row j) =
                  (basis b).row last + pc := by
              have hdec := basis_decomposition b (k + 1) hi
              apply Vector.ext
              intro col hcol
              have hdec_col := congrArg (fun v : Vector Rat m => v[col]) hdec
              simpa [pc, last, hjlast, GramSchmidt.prefixRows, Matrix.row] using hdec_col
            rw [hb_eq]
            exact _root_.Hex.GramSchmidt.prefixSpan_add (basis b) (k + 1) hi hbasisrow hpc
  intro v
  constructor
  · intro hv
    rcases hv with ⟨c, hc⟩
    have hspan :=
      _root_.Hex.GramSchmidt.prefixSpan_vecMul (A := basis b) (B := b)
        (i := i) (hi := hi) c (hmembersAll i hi).1
    rwa [hc] at hspan
  · intro hv
    rcases hv with ⟨c, hc⟩
    have hspan :=
      _root_.Hex.GramSchmidt.prefixSpan_vecMul (A := b) (B := basis b)
        (i := i) (hi := hi) c (hmembersAll i hi).2
    rwa [hc] at hspan















end GramSchmidt.Rat
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
Integer-cast layer of the Gram-Schmidt surface for `hex-gram-schmidt`.

This module defines the rational-valued `basis` and `coeffs` of an integer
input matrix (via `GramSchmidt.castIntMatrix`) and lifts the rational results
of `HexGramSchmidt/Basic/Rat.lean` to the integer setting: the leading-row,
orthogonality, triangular-decomposition, and prefix-span facts (`basis_zero`,
`basis_orthogonal`, `basis_decomposition`, `coeffs_diag`, `coeffs_upper`,
`basis_span`), together with the behaviour of `basis`/`coeffs` under the
integer row operations `Matrix.rowAdd` and adjacent `Matrix.rowSwap` used by
the LLL size-reduction and swap steps.
-/
namespace Hex
namespace GramSchmidt.Int

/-- The Gram-Schmidt orthogonal basis for an integer matrix, viewed in
`Rat` after coefficient divisions. -/
@[expose]
noncomputable def basis (b : Matrix Int n m) : Matrix Rat n m :=
  GramSchmidt.basisMatrix (GramSchmidt.castIntMatrix b)

/-- The Gram-Schmidt coefficient matrix for an integer input matrix. -/
@[expose]
noncomputable def coeffs (b : Matrix Int n m) : Matrix Rat n n :=
  GramSchmidt.coeffMatrix (GramSchmidt.castIntMatrix b) (basis b)















































/-- Orthogonalization preserves the row space of each prefix for an integer
matrix: the first `i + 1` basis rows span exactly the vectors spanned by the
first `i + 1` input rows cast into `Rat`. -/
theorem basis_span (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    ∀ v : Vector Rat m,
      GramSchmidt.prefixSpan (basis b) i hi v ↔
        GramSchmidt.prefixSpan (GramSchmidt.castIntMatrix b) i hi v := by
  simpa [basis, GramSchmidt.Rat.basis] using
    GramSchmidt.Rat.basis_span (b := GramSchmidt.castIntMatrix b) i hi

end GramSchmidt.Int
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
Vector insertion helpers.

These are generic vector/list bridge operations used by determinant permutation
enumerations and column-tuple constructions.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-- Insert an element into a vector at a given position. -/
@[expose]
def insertAt (x : α) (v : Vector α n) (i : Fin (n + 1)) : Vector α (n + 1) :=
  ⟨(v.toList.insertIdx i.val x).toArray, by
    have hi : i.val ≤ v.toList.length := by
      simpa using Nat.lt_succ_iff.mp i.isLt
    simpa using List.length_insertIdx_of_le_length (a := x) (as := v.toList) hi⟩

/-- Reading `insertAt x v i` at the insertion position `i` returns the inserted
element `x`. -/
theorem insertAt_get_self {α : Type u} {n : Nat}
    (x : α) (v : Vector α n) (i : Fin (n + 1)) :
    (insertAt x v i)[i] = x := by
  unfold insertAt
  simp [List.getElem_insertIdx_self]

/-- After inserting `x` at `Fin.last n`, reading the result at `i.castSucc` returns
the original entry `v[i]`. -/
theorem insertAt_last_get_castSucc {α : Type u} {n : Nat}
    (x : α) (v : Vector α n) (i : Fin n) :
    (insertAt x v (Fin.last n))[i.castSucc] = v[i] := by
  unfold insertAt
  simp [List.getElem_insertIdx_of_lt]

/-- Inserting an element at index `xs.length` is the same as appending it. -/
theorem list_insertIdx_length {α : Type u} (xs : List α) (x : α) :
    xs.insertIdx xs.length x = xs ++ [x] := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      simp [ih]

/-- `Vector.map` commutes with `Vector.toList`. -/
theorem vector_toList_map {α β : Type u} {n : Nat} (v : Vector α n)
    (f : α → β) :
    (v.map f).toList = v.toList.map f := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp

/-- `insertAt x v (Fin.last n)` appends `x` to the end of `v.toList`. -/
theorem insertAt_last_toList {α : Type u} {n : Nat} (x : α) (v : Vector α n) :
    (insertAt x v (Fin.last n)).toList = v.toList ++ [x] := by
  unfold insertAt
  simp only [Vector.toList]
  have hidx : (Fin.last n).val = v.toArray.toList.length := by
    simp
  simpa [hidx] using list_insertIdx_length v.toArray.toList x

/-- `insertAt x v i` corresponds to `List.insertIdx` at position `i` on the
underlying list. -/
theorem insertAt_toList {α : Type u} {n : Nat}
    (x : α) (v : Vector α n) (i : Fin (n + 1)) :
    (insertAt x v i).toList = v.toList.insertIdx i.val x := by
  unfold insertAt
  simp [Vector.toList]

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
Permutation enumeration and inversion-parity arithmetic for the local
Leibniz determinant.

This module defines `permutationVectors`, the recursive enumeration of the
permutations of `Fin n` as length-`n` vectors, together with `inversionCount`,
which counts the inversions of a permutation written as a list. The bulk of the
file establishes how inversion count behaves under list concatenation and under
swaps: `inversionCount_append` splits a concatenation into the inversions of
each part plus the cross-inversions (`crossInversionCount`), and
`inversionCount_adjacent_swap_parity` / `inversionCount_swap_separated_parity`
show that swapping two distinct entries flips inversion parity. These parity
facts underpin the sign computations used by the determinant.

It also proves that the enumeration is a faithful listing of the symmetric
group: `permutationVectors_complete` (every duplicate-free length-`n` vector is
enumerated) and `permutationVectors_nodup` / `permutationVectors_nodup_list` (no
repeats), via the `raiseFinAbove` / `peelLastVector` last-position recursion and
a handful of determinant-agnostic list and `Fin` helpers reused downstream.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-- Enumerate the permutations of `Fin n` as length-`n` vectors.

The recursion uses {name}`Hex.Vector.map'` rather than {name}`Vector.map` so
that the enumeration, and hence the Leibniz determinant built on it, reduces
in the kernel downstream of this module; core's {name}`Vector.map` delegates
to the unexposed {name}`Array.map` loop and stalls there. -/
@[expose]
def permutationVectors : (n : Nat) → List (Vector (Fin n) n)
  | 0 => [#v[]]
  | n + 1 =>
      List.flatMap
        (fun v =>
          (List.finRange (n + 1)).map fun i =>
            insertAt (Fin.last n) (Hex.Vector.map' Fin.castSucc v) i)
        (permutationVectors n)

/-- The size-`n+1` enumeration, restated with core's {name}`Vector.map`.

Symbolic proofs about the enumeration want this form. It is not the defining
equation: {name}`Hex.Vector.map'` and {name}`Vector.map` are propositionally
equal by {name}`Hex.Vector.map'_eq_map`, not definitionally, which is why
unfolding {name}`Hex.Matrix.permutationVectors` no longer closes these goals by
`rfl`.

Rewriting with this leaves a term core's {name}`Vector.map` blocks in the
kernel, so a proof that finishes with `decide +kernel` must leave
{name}`Hex.Matrix.permutationVectors` folded rather than reach for it. -/
theorem permutationVectors_succ {n : Nat} :
    permutationVectors (n + 1) =
      List.flatMap
        (fun v =>
          (List.finRange (n + 1)).map fun i =>
            insertAt (Fin.last n) (v.map Fin.castSucc) i)
        (permutationVectors n) := by
  simp only [permutationVectors, Hex.Vector.map'_eq_map]

/-- Count inversions in a permutation written as a list. -/
@[expose]
def inversionCount : List (Fin n) → Nat
  | [] => 0
  | x :: xs =>
      xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 + inversionCount xs

/-- Count the cross-inversions between two lists: pairs `(x, y)` with `x` drawn
from the first list, `y` from the second, and `y < x`. -/
 def _root_.Hex.Matrix.crossInversionCount {n : Nat} : List (Fin n) → List (Fin n) → Nat
  | [], _ => 0
  | x :: xs, ys =>
      ys.foldl (fun acc y => acc + if y < x then 1 else 0) 0 +
        crossInversionCount xs ys



/-- The inversion-counting left fold splits its starting accumulator off
additively. -/
 theorem _root_.Hex.Matrix.inversionFold_start {n : Nat} (xs : List (Fin n)) (x : Fin n)
    (acc : Nat) :
    xs.foldl (fun acc y => acc + if y < x then 1 else 0) acc =
      acc + xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 := by
  induction xs generalizing acc with
  | nil => simp
  | cons y ys ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + if y < x then 1 else 0), ih (0 + if y < x then 1 else 0)]
      omega

/-- The inversion-counting fold over an appended list is the sum of the folds
over each part. -/
 theorem _root_.Hex.Matrix.inversionFold_append {n : Nat} (xs ys : List (Fin n)) (x : Fin n) :
    (xs ++ ys).foldl (fun acc y => acc + if y < x then 1 else 0) 0 =
      xs.foldl (fun acc y => acc + if y < x then 1 else 0) 0 +
        ys.foldl (fun acc y => acc + if y < x then 1 else 0) 0 := by
  rw [List.foldl_append, _root_.Hex.Matrix.inversionFold_start]

/-- Inversions of a concatenation split into the inversions within each part
plus the cross-inversions between them. -/
 theorem _root_.Hex.Matrix.inversionCount_append {n : Nat} (xs ys : List (Fin n)) :
    inversionCount (xs ++ ys) =
      inversionCount xs + inversionCount ys + _root_.Hex.Matrix.crossInversionCount xs ys := by
  induction xs with
  | nil =>
      change inversionCount ys =
        inversionCount ([] : List (Fin n)) + inversionCount ys +
          _root_.Hex.Matrix.crossInversionCount ([] : List (Fin n)) ys
      simp [inversionCount, _root_.Hex.Matrix.crossInversionCount]
  | cons x xs ih =>
      simp only [List.cons_append, inversionCount, _root_.Hex.Matrix.crossInversionCount]
      rw [_root_.Hex.Matrix.inversionFold_append, ih]
      omega

/-- Cross-inversion count is additive in its right argument under
concatenation. -/
 theorem _root_.Hex.Matrix.crossInversionCount_append_right {n : Nat}
    (xs ys zs : List (Fin n)) :
    _root_.Hex.Matrix.crossInversionCount xs (ys ++ zs) =
      _root_.Hex.Matrix.crossInversionCount xs ys + _root_.Hex.Matrix.crossInversionCount xs zs := by
  induction xs with
  | nil =>
      simp [_root_.Hex.Matrix.crossInversionCount]
  | cons x xs ih =>
      simp only [_root_.Hex.Matrix.crossInversionCount]
      rw [_root_.Hex.Matrix.inversionFold_append, ih]
      omega



/-- Swapping the two elements of a right-hand pair leaves the cross-inversion
count unchanged. -/
 theorem _root_.Hex.Matrix.crossInversionCount_pair_swap_right {n : Nat}
    (xs : List (Fin n)) (a b : Fin n) :
    _root_.Hex.Matrix.crossInversionCount xs [a, b] =
      _root_.Hex.Matrix.crossInversionCount xs [b, a] := by
  induction xs with
  | nil =>
      simp [_root_.Hex.Matrix.crossInversionCount]
  | cons x xs ih =>
      simp [_root_.Hex.Matrix.crossInversionCount]
      rw [ih]
      omega

/-- Swapping the two elements of a left-hand pair leaves the cross-inversion
count unchanged. -/
 theorem _root_.Hex.Matrix.crossInversionCount_pair_swap_left {n : Nat}
    (xs : List (Fin n)) (a b : Fin n) :
    _root_.Hex.Matrix.crossInversionCount [a, b] xs =
      _root_.Hex.Matrix.crossInversionCount [b, a] xs := by
  simp [_root_.Hex.Matrix.crossInversionCount]
  omega

/-- A two-element list has exactly one inversion precisely when its entries are
out of order. -/
 theorem _root_.Hex.Matrix.inversionCount_pair {n : Nat} (a b : Fin n) :
    inversionCount [a, b] = if b < a then 1 else 0 := by
  simp [inversionCount]

/-- Swapping two distinct adjacent entries flips the parity of the inversion
count. -/
 theorem _root_.Hex.Matrix.inversionCount_adjacent_swap_parity {n : Nat}
    (pre post : List (Fin n)) (a b : Fin n) (h : a ≠ b) :
    inversionCount (pre ++ a :: b :: post) % 2 =
      (inversionCount (pre ++ b :: a :: post) + 1) % 2 := by
  have horder : a < b ∨ b < a := by
    have hval : a.val ≠ b.val := by
      intro hv
      exact h (Fin.ext hv)
    cases Nat.lt_or_gt_of_ne hval with
    | inl hab => exact Or.inl hab
    | inr hba => exact Or.inr hba
  rw [show pre ++ a :: b :: post = pre ++ ([a, b] ++ post) by simp,
    show pre ++ b :: a :: post = pre ++ ([b, a] ++ post) by simp]
  have hcross :
      _root_.Hex.Matrix.crossInversionCount pre ([a, b] ++ post) =
        _root_.Hex.Matrix.crossInversionCount pre ([b, a] ++ post) := by
    repeat rw [_root_.Hex.Matrix.crossInversionCount_append_right]
    rw [_root_.Hex.Matrix.crossInversionCount_pair_swap_right]
  have htail :
      _root_.Hex.Matrix.crossInversionCount [a, b] post =
        _root_.Hex.Matrix.crossInversionCount [b, a] post := by
    exact _root_.Hex.Matrix.crossInversionCount_pair_swap_left post a b
  rw [_root_.Hex.Matrix.inversionCount_append pre ([a, b] ++ post), _root_.Hex.Matrix.inversionCount_append pre ([b, a] ++ post),
    hcross, _root_.Hex.Matrix.inversionCount_append [a, b] post, _root_.Hex.Matrix.inversionCount_append [b, a] post, htail,
    _root_.Hex.Matrix.inversionCount_pair a b, _root_.Hex.Matrix.inversionCount_pair b a]
  cases horder with
  | inl hab =>
      have hba : ¬ b < a := by omega
      simp [hab, hba]
      omega
  | inr hba =>
      have hab : ¬ a < b := by omega
      simp [hab, hba]
      omega

/-- Swapping two entries separated by an arbitrary duplicate-free middle segment
flips the parity of the inversion count. -/
 theorem _root_.Hex.Matrix.inversionCount_swap_separated_parity {n : Nat}
    (pre mid post : List (Fin n)) (a b : Fin n)
    (hnodup : (pre ++ a :: mid ++ b :: post).Nodup) :
    inversionCount (pre ++ b :: mid ++ a :: post) % 2 =
      (inversionCount (pre ++ a :: mid ++ b :: post) + 1) % 2 := by
  induction mid generalizing pre with
  | nil =>
      have hne : b ≠ a := by
        intro hba
        subst b
        have hsplit : ((pre ++ [a]) ++ a :: post).Nodup := by
          simpa [List.append_assoc] using hnodup
        exact ((List.nodup_append (l₁ := pre ++ [a]) (l₂ := a :: post)).mp hsplit).2.2
          a (by simp) a (by simp) rfl
      simpa [Nat.add_comm] using
        (_root_.Hex.Matrix.inversionCount_adjacent_swap_parity pre post b a hne)
  | cons x xs ih =>
      have hswap₁ :
          inversionCount (pre ++ b :: x :: xs ++ a :: post) % 2 =
            (inversionCount (pre ++ x :: b :: xs ++ a :: post) + 1) % 2 := by
        simpa [List.append_assoc] using
          _root_.Hex.Matrix.inversionCount_adjacent_swap_parity pre (xs ++ a :: post) b x (by
            intro hbx
            subst b
            have hsplit : ((pre ++ a :: x :: xs) ++ x :: post).Nodup := by
              simpa [List.append_assoc] using hnodup
            exact ((List.nodup_append (l₁ := pre ++ a :: x :: xs) (l₂ := x :: post)).mp hsplit).2.2
              x (by simp) x (by simp) rfl)
      have hnodup_tail : ((pre ++ [x]) ++ a :: xs ++ b :: post).Nodup := by
        have hp :
            ((pre ++ [x]) ++ a :: xs ++ b :: post).Perm
              (pre ++ a :: x :: xs ++ b :: post) := by
          simpa [List.append_assoc] using
            List.Perm.append_left pre (List.Perm.swap a x (xs ++ b :: post))
        exact hp.nodup_iff.mpr hnodup
      have hmid :
          inversionCount (pre ++ x :: b :: xs ++ a :: post) % 2 =
            (inversionCount (pre ++ x :: a :: xs ++ b :: post) + 1) % 2 := by
        simpa only [List.cons_append, List.append_assoc, List.nil_append] using
          (ih (pre ++ [x]) hnodup_tail)
      have hswap₂ :
          inversionCount (pre ++ x :: a :: xs ++ b :: post) % 2 =
            (inversionCount (pre ++ a :: x :: xs ++ b :: post) + 1) % 2 := by
        simpa [List.append_assoc] using
          _root_.Hex.Matrix.inversionCount_adjacent_swap_parity pre (xs ++ b :: post) x a (by
            intro hxa
            subst x
            have hsplit : (pre ++ [a] ++ (a :: xs ++ b :: post)).Nodup := by
              simpa [List.append_assoc] using hnodup
            exact ((List.nodup_append (l₁ := pre ++ [a]) (l₂ := a :: xs ++ b :: post)).mp hsplit).2.2
              a (by simp) a (by simp) rfl)
      omega



/-! # Generic list and `Fin` combinatorics

These determinant-agnostic helpers about folds, `Nodup`, and `insertAt`
support the enumeration completeness and duplicate-freeness proofs below,
and are reused by the Leibniz determinant layer downstream. -/

/-- Mapping a duplicate-free list by an injective function preserves
duplicate-freeness. -/
 theorem _root_.Hex.Matrix.list_nodup_map_of_injective {α : Type u} {β : Type v}
    [DecidableEq β] {f : α → β} (hinj : Function.Injective f) :
    ∀ {xs : List α}, xs.Nodup → (xs.map f).Nodup
  | [], _ => by simp
  | x :: xs, hnodup => by
      simp only [List.map_cons, List.nodup_cons] at hnodup ⊢
      constructor
      · intro hmem
        simp only [List.mem_map] at hmem
        rcases hmem with ⟨y, hy, hfy⟩
        exact hnodup.1 (hinj hfy.symm ▸ hy)
      · exact list_nodup_map_of_injective hinj hnodup.2



/-- Mapping a `Nodup` list through the injective `Fin.castSucc` keeps it `Nodup`. -/
 theorem _root_.Hex.Matrix.list_nodup_map_castSucc {n : Nat} (xs : List (Fin n)) :
    xs.Nodup → (xs.map Fin.castSucc).Nodup := by
  induction xs with
  | nil =>
      intro _h
      simp
  | cons x xs ih =>
      intro hnodup
      rw [List.nodup_cons] at hnodup
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_map] at hmem
        rcases hmem with ⟨y, hy, hxy⟩
        have hval : x.val = y.val := by
          simpa using (congrArg Fin.val hxy).symm
        exact hnodup.1 (Fin.ext hval ▸ hy)
      · exact ih hnodup.2

/-- `Fin.last n` never lies in the image of a list under `Fin.castSucc`. -/
 theorem _root_.Hex.Matrix.finLast_not_mem_map_castSucc {n : Nat} (xs : List (Fin n)) :
    Fin.last n ∉ xs.map Fin.castSucc := by
  intro hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨x, _hxmem, hxlast⟩
  have hval : x.val = n := by
    simpa using congrArg Fin.val hxlast
  exact Nat.ne_of_lt x.isLt hval

/-- Inserting `Fin.last n` at any position into the `castSucc`-embedded nodup vector
keeps the resulting list `Nodup`, since `Fin.last n` is new and the embedding
stays injective. -/
 theorem _root_.Hex.Matrix.insertAt_last_castSucc_nodup {n : Nat}
    (v : Vector (Fin n) n) (i : Fin (n + 1))
    (hnodup : v.toList.Nodup) :
    (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.Nodup := by
  rw [insertAt_toList]
  have hmap : (v.map Fin.castSucc).toList.Nodup := by
    rw [vector_toList_map]
    exact _root_.Hex.Matrix.list_nodup_map_castSucc v.toList hnodup
  have hlast : Fin.last n ∉ (v.map Fin.castSucc).toList := by
    rw [vector_toList_map]
    exact _root_.Hex.Matrix.finLast_not_mem_map_castSucc v.toList
  have hcons : (Fin.last n :: (v.map Fin.castSucc).toList).Nodup := by
    rw [List.nodup_cons]
    exact ⟨hlast, hmap⟩
  have hidx : i.val ≤ (v.map Fin.castSucc).toList.length := by
    simpa using Nat.lt_succ_iff.mp i.isLt
  exact (List.perm_insertIdx (Fin.last n) (v.map Fin.castSucc).toList hidx).symm.nodup hcons

/-- A `Nodup` list of `Fin (n + 1)` with full length `n + 1` must contain
`Fin.last n`. -/
 theorem _root_.Hex.Matrix.finLast_mem {n : Nat} {xs : List (Fin (n + 1))}
    (hlen : xs.length = n + 1) (hnodup : xs.Nodup) :
    Fin.last n ∈ xs := by
  by_cases hmem : Fin.last n ∈ xs
  · exact hmem
  · exfalso
    have hsubset : xs ⊆ (List.finRange (n + 1)).erase (Fin.last n) := by
      intro x hx
      refine (List.mem_erase_of_ne ?_).2 (List.mem_finRange x)
      rintro rfl
      exact hmem hx
    have hle : xs.length ≤ ((List.finRange (n + 1)).erase (Fin.last n)).length :=
      List.nodup_subset_length_le hnodup hsubset
    have herase :
        ((List.finRange (n + 1)).erase (Fin.last n)).length = n := by
      rw [List.length_erase]
      simp [List.mem_finRange, List.length_finRange]
    omega


/-! # Completeness and duplicate-freeness of the enumeration -/

/-- `lowerFinLast x h` reinterprets an `x : Fin (n + 1)` that is not `Fin.last n`
as an element of `Fin n` carrying the same underlying value. -/
 def _root_.Hex.Matrix.lowerFinLast {n : Nat} (x : Fin (n + 1)) (h : x ≠ Fin.last n) :
    Fin n :=
  ⟨x.val, by
    have hxlt : x.val < n + 1 := x.isLt
    have hxne : x.val ≠ n := by
      intro hx
      exact h (Fin.ext hx)
    omega⟩

/-- `raiseFinAbove i r` embeds `r : Fin n` into `Fin (n + 1)` while skipping the
position `i`: values below `i` are kept, values at or above `i` are shifted up by
one. -/
 def _root_.Hex.Matrix.raiseFinAbove {n : Nat} (i : Fin (n + 1)) (r : Fin n) :
    Fin (n + 1) :=
  if h : r.val < i.val then
    ⟨r.val, by omega⟩
  else
    ⟨r.val + 1, by omega⟩



























/-- `Fin.castSucc` undoes `lowerFinLast`: `(lowerFinLast x h).castSucc = x`. -/
 theorem _root_.Hex.Matrix.lowerFinLast_castSucc {n : Nat} (x : Fin (n + 1))
    (h : x ≠ Fin.last n) :
    (_root_.Hex.Matrix.lowerFinLast x h).castSucc = x := by
  exact Fin.ext rfl

/-- In a length-`(n + 1)` nodup list the index of `Fin.last n` is within bounds. -/
 theorem _root_.Hex.Matrix.finLast_idxOf_lt {n : Nat} {xs : List (Fin (n + 1))}
    (hlen : xs.length = n + 1) (hnodup : xs.Nodup) :
    xs.idxOf (Fin.last n) < xs.length := by
  exact List.idxOf_lt_length_of_mem (_root_.Hex.Matrix.finLast_mem hlen hnodup)

/-- `peelLastVector perm k …` removes the entry `Fin.last n` (located at position
`k`) from a nodup permutation vector, lowering each remaining entry back to
`Fin n`. -/
 def _root_.Hex.Matrix.peelLastVector {n : Nat} (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (_hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) : Vector (Fin n) n :=
  Vector.ofFn fun r =>
    let j := if r.val < k then r.val else r.val + 1
    have hj : j < n + 1 := by
      dsimp [j]
      split
      · omega
      · have hr : r.val < n := r.isLt
        omega
    let y := perm[(⟨j, hj⟩ : Fin (n + 1))]
    _root_.Hex.Matrix.lowerFinLast y (by
      intro hy
      have hjlen : j < perm.toList.length := by
        simpa [Vector.length_toList] using hj
      have hjidx :
          perm.toList.idxOf (perm.toList[j]'hjlen) = j := by
        exact hnodup.idxOf_getElem j hjlen
      have hylist : perm.toList[j]'hjlen = Fin.last n := by
        rw [Vector.getElem_toList]; exact hy
      have hkj : k = j := by
        rw [← hidx, ← hylist, hjidx]
      dsimp [j] at hkj
      split at hkj
      · omega
      · omega)

/-- Re-embedding `peelLastVector` through `Fin.castSucc` yields the original
permutation list with position `k` erased. -/
 theorem _root_.Hex.Matrix.peelLastVector_castSucc_toList {n : Nat}
    (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) :
    ((_root_.Hex.Matrix.peelLastVector perm k hk hidx hnodup).map Fin.castSucc).toList =
      perm.toList.eraseIdx k := by
  apply List.ext_getElem
  · have hklist : k < perm.toList.length := by
      simpa [Vector.length_toList] using hk
    rw [List.length_eraseIdx_of_lt hklist]
    simp [Vector.length_toList]
  · intro i hi₁ hi₂
    by_cases hik : i < k
    · simp [_root_.Hex.Matrix.peelLastVector, hik, _root_.Hex.Matrix.lowerFinLast_castSucc, List.getElem_eraseIdx]
    · have hikle : k ≤ i := Nat.le_of_not_gt hik
      have hklist : k < perm.toList.length := by
        simpa [Vector.length_toList] using hk
      have heraseLen : (perm.toList.eraseIdx k).length = n := by
        rw [List.length_eraseIdx_of_lt hklist]
        simp [Vector.length_toList]
      have hi : i < n := by
        simpa [heraseLen] using hi₂
      simp [_root_.Hex.Matrix.peelLastVector, hik, _root_.Hex.Matrix.lowerFinLast_castSucc, List.getElem_eraseIdx]

/-- If `xs.map f` is nodup and `f` is injective, then `xs` is nodup. -/
 theorem _root_.Hex.Matrix.list_nodup_of_map_injective {α β : Type u} {f : α → β}
    (hinj : Function.Injective f) :
    ∀ {xs : List α}, (xs.map f).Nodup → xs.Nodup
  | [], _ => by simp
  | x :: xs, hnodup => by
      simp only [List.map_cons, List.nodup_cons] at hnodup ⊢
      constructor
      · intro hxmem
        exact hnodup.1 (List.mem_map.mpr ⟨x, hxmem, rfl⟩)
      · exact list_nodup_of_map_injective hinj hnodup.2

/-- `peelLastVector` produces a nodup vector. -/
 theorem _root_.Hex.Matrix.peelLastVector_nodup {n : Nat}
    (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) :
    (_root_.Hex.Matrix.peelLastVector perm k hk hidx hnodup).toList.Nodup := by
  apply _root_.Hex.Matrix.list_nodup_of_map_injective (f := Fin.castSucc)
  · intro x y hxy
    exact Fin.ext (by simpa using congrArg Fin.val hxy)
  · rw [← vector_toList_map]
    rw [_root_.Hex.Matrix.peelLastVector_castSucc_toList perm k hk hidx hnodup]
    exact hnodup.eraseIdx k

/-- Inserting the erased element `xs[i]` back at position `i` of `xs.eraseIdx i`
reconstructs the original list `xs`. -/
 theorem _root_.Hex.Matrix.list_insertIdx_eraseIdx_getElem {α : Type u} {xs : List α} {i : Nat}
    (hi : i < xs.length) :
    (xs.eraseIdx i).insertIdx i (xs[i]'hi) = xs := by
  induction xs generalizing i with
  | nil =>
      cases hi
  | cons x xs ih =>
      cases i with
      | zero =>
          simp
      | succ i =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
          simp [ih hi]

/-- Inserting `Fin.last n` at position `k` into the `castSucc`-embedded
`peelLastVector` reconstructs the original permutation vector `perm`. -/
 theorem _root_.Hex.Matrix.insertAt_peelLastVector {n : Nat}
    (perm : Vector (Fin (n + 1)) (n + 1))
    (k : Nat) (hk : k < n + 1)
    (hidx : perm.toList.idxOf (Fin.last n) = k)
    (hnodup : perm.toList.Nodup) :
    insertAt (Fin.last n)
        ((_root_.Hex.Matrix.peelLastVector perm k hk hidx hnodup).map Fin.castSucc) ⟨k, hk⟩ =
      perm := by
  apply Vector.toArray_inj.mp
  apply Array.toList_inj.mp
  change (insertAt (Fin.last n)
        ((_root_.Hex.Matrix.peelLastVector perm k hk hidx hnodup).map Fin.castSucc) ⟨k, hk⟩).toList =
      perm.toList
  rw [insertAt_toList, _root_.Hex.Matrix.peelLastVector_castSucc_toList perm k hk hidx hnodup]
  have hklist : k < perm.toList.length := by
    simpa [Vector.length_toList] using hk
  have hget : perm.toList[k]'hklist = Fin.last n := by
    have hidxLt : perm.toList.idxOf (Fin.last n) < perm.toList.length := by
      simpa [hidx] using hklist
    simpa [hidx] using
      (List.getElem_idxOf (x := Fin.last n) (xs := perm.toList) hidxLt)
  simpa [hget] using
    (_root_.Hex.Matrix.list_insertIdx_eraseIdx_getElem (xs := perm.toList) (i := k) hklist)

/-- Every duplicate-free length-`n` vector of `Fin n` appears in
`permutationVectors n`. This gives the completeness half of the local
permutation enumeration used by the Leibniz determinant. -/
theorem permutationVectors_complete {n : Nat} {perm : Vector (Fin n) n}
    (hnodup : perm.toList.Nodup) :
    perm ∈ permutationVectors n := by
  induction n with
  | zero =>
      have hnil : perm.toList = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp [Vector.length_toList]
      have hperm : perm = #v[] := by
        ext i hi
        omega
      simp [permutationVectors, hperm]
  | succ n ih =>
      let k := perm.toList.idxOf (Fin.last n)
      have hk : k < n + 1 := by
        simpa [k, Vector.length_toList] using
          _root_.Hex.Matrix.finLast_idxOf_lt (by simp [Vector.length_toList]) hnodup
      have hidx : perm.toList.idxOf (Fin.last n) = k := rfl
      let peeled := _root_.Hex.Matrix.peelLastVector perm k hk hidx hnodup
      have hpeeled : peeled ∈ permutationVectors n := by
        exact ih (_root_.Hex.Matrix.peelLastVector_nodup perm k hk hidx hnodup)
      rw [permutationVectors_succ, List.mem_flatMap]
      refine ⟨peeled, hpeeled, ?_⟩
      rw [List.mem_map]
      refine ⟨(⟨k, hk⟩ : Fin (n + 1)), List.mem_finRange (⟨k, hk⟩ : Fin (n + 1)), ?_⟩
      exact _root_.Hex.Matrix.insertAt_peelLastVector perm k hk hidx hnodup

/-- Every vector enumerated by `permutationVectors n` is duplicate-free, so
each listed vector really represents a permutation of `Fin n`. -/
theorem permutationVectors_nodup {n : Nat} {perm : Vector (Fin n) n}
    (hmem : perm ∈ permutationVectors n) :
    perm.toList.Nodup := by
  induction n with
  | zero =>
      have hnil : perm.toList = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        simp [Vector.length_toList]
      rw [hnil]
      simp
  | succ n ih =>
      simp [permutationVectors, List.mem_flatMap, List.mem_map] at hmem
      rcases hmem with ⟨v, hv, i, _hi, rfl⟩
      exact _root_.Hex.Matrix.insertAt_last_castSucc_nodup v i (ih hv)

 theorem _root_.Hex.Matrix.insertAt_last_castSucc_idxOf {n : Nat}
    (v : Vector (Fin n) n) (i : Fin (n + 1)) (hnodup : v.toList.Nodup) :
    (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.idxOf (Fin.last n) =
      i.val := by
  have hins :
      (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.Nodup :=
    _root_.Hex.Matrix.insertAt_last_castSucc_nodup v i hnodup
  have hlen :
      i.val < (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.length := by
    simp [Vector.length_toList]
  have hget :
      (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList[i.val] =
        Fin.last n := by
    change (insertAt (Fin.last n) (v.map Fin.castSucc) i)[i] = Fin.last n
    exact insertAt_get_self (Fin.last n) (v.map Fin.castSucc) i
  simpa [hget] using hins.idxOf_getElem i.val hlen

/-- `insertAt_last_castSucc_injective` states that inserting `Fin.last n` into the
`castSucc`-lifted nodup vectors `v` and `w` at positions `i` and `j` yields equal
results only when `i = j` and `v = w`, the injectivity that keeps the inserted
permutation vectors distinct in the recursive enumeration. -/
 theorem _root_.Hex.Matrix.insertAt_last_castSucc_injective {n : Nat}
    {v w : Vector (Fin n) n} {i j : Fin (n + 1)}
    (hv : v.toList.Nodup) (hw : w.toList.Nodup)
    (h :
      insertAt (Fin.last n) (v.map Fin.castSucc) i =
        insertAt (Fin.last n) (w.map Fin.castSucc) j) :
    i = j ∧ v = w := by
  have hidx :
      i.val = j.val := by
    rw [← _root_.Hex.Matrix.insertAt_last_castSucc_idxOf v i hv, h]
    exact _root_.Hex.Matrix.insertAt_last_castSucc_idxOf w j hw
  have hij : i = j := Fin.ext hidx
  subst j
  have hlist := congrArg
    (fun x : Vector (Fin (n + 1)) (n + 1) => x.toList.eraseIdx i.val) h
  change
    (insertAt (Fin.last n) (v.map Fin.castSucc) i).toList.eraseIdx i.val =
      (insertAt (Fin.last n) (w.map Fin.castSucc) i).toList.eraseIdx i.val at hlist
  rw [insertAt_toList, insertAt_toList] at hlist
  repeat rw [List.eraseIdx_insertIdx_self] at hlist
  have hmap : v.toList.map Fin.castSucc = w.toList.map Fin.castSucc := by
    simpa [vector_toList_map] using hlist
  have hvwList : v.toList = w.toList := by
    exact (List.map_inj_right
      (fun x y hxy => Fin.ext (by simpa using congrArg Fin.val hxy))).mp hmap
  refine ⟨rfl, ?_⟩
  apply Vector.toArray_inj.mp
  apply Array.toList_inj.mp
  simpa [Vector.toList] using hvwList

/-- `permutationVectorInsertions_nodup` states that, for a fixed nodup vector `v`,
the list of insertions of `Fin.last n` at each position has no duplicates, so the
size-`n+1` vectors built from a single size-`n` permutation stay distinct. -/
 theorem _root_.Hex.Matrix.permutationVectorInsertions_nodup {n : Nat}
    (v : Vector (Fin n) n) (hnodup : v.toList.Nodup) :
    ((List.finRange (n + 1)).map fun i =>
        insertAt (Fin.last n) (v.map Fin.castSucc) i).Nodup := by
  exact _root_.Hex.Matrix.list_nodup_map_of_injective
    (fun i j h => (_root_.Hex.Matrix.insertAt_last_castSucc_injective hnodup hnodup h).1)
    (List.nodup_finRange (n + 1))

/-- `permutationVectorInsertions_disjoint` states that distinct nodup vectors `v`
and `w` produce insertion lists sharing no element, the cross-vector disjointness
that prevents collisions when the per-vector insertions are concatenated. -/
 theorem _root_.Hex.Matrix.permutationVectorInsertions_disjoint {n : Nat}
    {v w : Vector (Fin n) n}
    (hv : v.toList.Nodup) (hw : w.toList.Nodup) (hvw : v ≠ w) :
    ∀ a, a ∈ ((List.finRange (n + 1)).map fun i =>
        insertAt (Fin.last n) (v.map Fin.castSucc) i) →
      ∀ b, b ∈ ((List.finRange (n + 1)).map fun i =>
        insertAt (Fin.last n) (w.map Fin.castSucc) i) →
        a ≠ b := by
  intro a ha b hb hab
  simp only [List.mem_map] at ha hb
  rcases ha with ⟨i, _hi, rfl⟩
  rcases hb with ⟨j, _hj, hb⟩
  exact hvw (_root_.Hex.Matrix.insertAt_last_castSucc_injective hv hw (hab.trans hb.symm)).2

/-- `permutationVectors_flatMap_nodup` states that flat-mapping the per-vector
insertion lists over a nodup list `vs` of nodup vectors yields a nodup list,
combining the per-vector and cross-vector facts into the no-duplicates property of
the size-`n+1` permutation enumeration. -/
 theorem _root_.Hex.Matrix.permutationVectors_flatMap_nodup {n : Nat}
    (vs : List (Vector (Fin n) n))
    (hvs : vs.Nodup) (hperm : ∀ v, v ∈ vs → v.toList.Nodup) :
    (vs.flatMap fun v =>
        (List.finRange (n + 1)).map fun i =>
          insertAt (Fin.last n) (v.map Fin.castSucc) i).Nodup := by
  induction vs with
  | nil =>
      simp
  | cons v vs ih =>
      simp only [List.flatMap_cons]
      rw [List.nodup_append]
      simp only [List.nodup_cons] at hvs
      refine ⟨?_, ?_, ?_⟩
      · exact _root_.Hex.Matrix.permutationVectorInsertions_nodup v (hperm v (by simp))
      · exact ih hvs.2 (fun w hw => hperm w (List.mem_cons_of_mem v hw))
      · intro a ha b hb hab
        simp only [List.mem_flatMap, List.mem_map] at hb
        rcases hb with ⟨w, hw, j, _hj, rfl⟩
        exact _root_.Hex.Matrix.permutationVectorInsertions_disjoint
          (hperm v (by simp)) (hperm w (List.mem_cons_of_mem v hw))
          (by
            intro hvw
            exact hvs.1 (hvw ▸ hw))
          a ha _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩) hab

/-- The permutation enumeration itself has no duplicate vectors. This lets
determinant proofs compare sums over `permutationVectors` by list
permutation rather than by quotienting repeated terms. -/
theorem permutationVectors_nodup_list {n : Nat} :
    (permutationVectors n).Nodup := by
  induction n with
  | zero =>
      simp [permutationVectors]
  | succ n ih =>
      rw [permutationVectors_succ]
      exact _root_.Hex.Matrix.permutationVectors_flatMap_nodup
        (permutationVectors n) ih
        (fun v hv => permutationVectors_nodup hv)

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
Core Leibniz-formula definitions for the dense determinant.

This module defines the determinant `det` of a dense square matrix as the
`permutationVectors`-indexed sum of signed Leibniz terms, built from `detSign`
(the inversion-parity sign of a permutation vector), `detProduct` (the unsigned
diagonal product), and `detTerm` (their product). It records the small base
cases `det_one_by_one`, `det_two_by_two`, and `det_principalSubmatrix_zero`, and
provides the reusable `foldl`-arithmetic toolkit (scalar factoring, additive
splitting, permutation invariance, single-index scaling) plus the
`Fin.castSucc`/`Fin.last` inversion-count lemmas used by the recursive
determinant proofs in the sibling modules.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-- The sign of a permutation vector, computed from inversion parity. -/
@[expose]
def detSign {R : Type u} [Lean.Grind.Ring R] {n : Nat} (perm : Vector (Fin n) n) : R :=
  if inversionCount perm.toList % 2 = 0 then 1 else -1

/-- The unsigned product associated to a permutation vector. -/
@[expose]
def detProduct {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R n n) (perm : Vector (Fin n) n) : R :=
  Fin.foldl n (fun acc i => acc * M[(i, perm[i])]) 1

/-- The Leibniz summand associated to a permutation vector. -/
@[expose]
def detTerm {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (M : Matrix R n n) (perm : Vector (Fin n) n) : R :=
  detSign perm * detProduct M perm

/-- The determinant of a dense square matrix, defined by the Leibniz formula. -/
@[expose]
def det {R : Type u} [Lean.Grind.Ring R] {n : Nat} (M : Matrix R n n) : R :=
  (permutationVectors n).foldl (fun acc perm => acc + detTerm M perm) 0



/-- The determinant of the empty leading prefix is the Bareiss previous-pivot
convention `1`. -/
@[simp, grind =] theorem det_principalSubmatrix_zero {R : Type u} [Lean.Grind.Ring R]
    (M : Matrix R n n) :
    det (principalSubmatrix M 0 (Nat.zero_le n)) = (1 : R) := by
  simp [det, detTerm, detSign, detProduct, permutationVectors, inversionCount]
  grind

/-- The determinant of a `1 × 1` matrix is its only entry.
This is the smallest non-empty determinant base case. -/
@[simp, grind =] theorem det_one_by_one {R : Type u} [Lean.Grind.Ring R]
    (M : Matrix R 1 1) :
    det M = M[0][0] := by
  simp [det, detTerm, detSign, detProduct, Fin.foldl_eq_finRange_foldl,
    permutationVectors, insertAt, inversionCount, List.finRange]
  grind




/-- Mapping a duplicate-free list preserves duplicate-freeness when the function
is injective on that list's elements. -/
 theorem _root_.Hex.Matrix.list_nodup_map_on {α : Type u} {β : Type v}
    [DecidableEq β] {f : α → β} :
    ∀ {xs : List α}, xs.Nodup →
      (∀ a, a ∈ xs → ∀ b, b ∈ xs → f a = f b → a = b) →
      (xs.map f).Nodup
  | [], _hnodup, _hinj => by simp
  | x :: xs, hnodup, hinj => by
      simp only [List.nodup_cons] at hnodup
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨y, hy, hfy⟩
        have hxy := hinj x (by simp) y (List.mem_cons_of_mem x hy) hfy.symm
        subst y
        exact hnodup.1 hy
      · exact list_nodup_map_on hnodup.2 (by
          intro a ha b hb hab
          exact hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb) hab)


























/-- Folding the inversion count against a pivot is unchanged when both the list
`xs` and the pivot `x` are mapped through `Fin.castSucc`. -/
 theorem _root_.Hex.Matrix.inversionFold_map_castSucc {n : Nat} (xs : List (Fin n)) (x : Fin n)
    (acc : Nat) :
    (xs.map Fin.castSucc).foldl
        (fun acc y => acc + if y < x.castSucc then 1 else 0) acc =
    xs.foldl (fun acc y => acc + if y < x then 1 else 0) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons y ys ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hhead :
          (if y.castSucc < x.castSucc then 1 else 0) =
            (if y < x then 1 else 0) := by
        simp [Fin.lt_def]
      rw [hhead]
      exact ih _



/-- Appending `Fin.last n` after the `castSucc`-embedded list adds no inversions,
so the count equals `inversionCount xs`. -/
 theorem _root_.Hex.Matrix.inversionCount_insert_last_castSucc {n : Nat} (xs : List (Fin n)) :
    inversionCount ((xs.map Fin.castSucc) ++ [Fin.last n]) = inversionCount xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.cons_append, inversionCount]
      rw [ih, List.foldl_append, List.foldl_cons, List.foldl_nil, _root_.Hex.Matrix.inversionFold_map_castSucc]
      simp [Fin.lt_def]








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
The last-row determinant recursion.

This module derives how the Leibniz determinant recurses on the final row and
column. Inserting `Fin.last n` at the end of a permutation vector splits the
sign and the product (`detSign_insertAt_last`, `detProduct_insertAt_last`,
`detTerm_insertAt_last`), and the general insertion position is handled by
`detSign_insertAt_general` / `detTerm_insertAt_general`. The payoff is the
last-row factorisation `det_eq_principalSubmatrix_mul_last`: when the final row
vanishes off the diagonal, the determinant is the determinant of the leading
principal submatrix times the corner entry. Laplace expansion and the triangular
diagonal-product formulas (`HexDeterminant.Triangular`) build on it. The
enumeration combinatorics this recursion rides on (`permutationVectors`
completeness and duplicate-freeness, `raiseFinAbove` / `peelLastVector`) live in
`HexDeterminant.Enumeration`.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-- Appending the new largest value in the last position does not change
the determinant sign, because it adds no inversions. -/
theorem detSign_insertAt_last {R : Type u} [Lean.Grind.Ring R] {n : Nat}
    (v : Vector (Fin n) n) :
    detSign (R := R)
      (insertAt (Fin.last n) (v.map Fin.castSucc) (Fin.last n)) =
    detSign (R := R) v := by
  unfold detSign
  rw [insertAt_last_toList, vector_toList_map, _root_.Hex.Matrix.inversionCount_insert_last_castSucc]







/-- The identity permutation has positive determinant sign. -/
theorem detSign_identity {R : Type u} [Lean.Grind.Ring R] (n : Nat) :
    detSign (R := R) (Vector.ofFn fun i : Fin n => i) = 1 := by
  induction n with
  | zero =>
      have hvec : (Vector.ofFn fun i : Fin 0 => i) = #v[] := by
        ext i hi
        omega
      simp [hvec, detSign, inversionCount]
  | succ n ih =>
      have hvec :
          (Vector.ofFn fun i : Fin (n + 1) => i) =
            insertAt (Fin.last n)
              ((Vector.ofFn fun i : Fin n => i).map Fin.castSucc) (Fin.last n) := by
        ext k hk
        by_cases hlast : k = n
        · subst k
          simp [insertAt, List.getElem_insertIdx_self]
        · have hklt : k < n := by omega
          simp [insertAt, List.getElem_insertIdx_of_lt, hklt]
      rw [hvec, detSign_insertAt_last]
      exact ih





























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
Permutation-group structure on permutation vectors.

This module develops the operations on permutation vectors that the elementary
row and column operation laws are built from: `finTranspose` and
`transposePermutationValues`/`swapPermutationValues` (position and value swaps),
`inversePermutationVector`, and `composePermutationValues`. It shows these
preserve membership in `permutationVectors` and tracks their effect on inversion
parity, culminating in `detSign_swapPermutationValues` and the multiplicativity
law `detSign_composePermutationValues`. The elementary-operation determinant
laws themselves live in `HexDeterminant.RowOps`.
-/

namespace Hex
universe u
namespace Matrix
variable {α : Type u}

/-- The transposition of `Fin n` swapping `i` and `j`, sending `r` to `j` if
`r = i`, to `i` if `r = j`, and to itself otherwise. -/
@[expose]
def finTranspose {n : Nat} (i j : Fin n) (r : Fin n) : Fin n :=
  if r = i then j else if r = j then i else r

/-- `finTranspose i j` sends `i` to `j`. -/
 theorem _root_.Hex.Matrix.finTranspose_left {n : Nat} (i j : Fin n) :
    finTranspose i j i = j := by
  simp [finTranspose]

/-- `finTranspose i j` sends `j` to `i`. -/
 theorem _root_.Hex.Matrix.finTranspose_right {n : Nat} (i j : Fin n) :
    finTranspose i j j = i := by
  by_cases h : j = i
  · subst j
    simp [finTranspose]
  · simp [finTranspose, h]

/-- `finTranspose i j` fixes every `r` distinct from both `i` and `j`. -/
 theorem _root_.Hex.Matrix.finTranspose_of_ne {n : Nat} (i j r : Fin n)
    (hi : r ≠ i) (hj : r ≠ j) :
    finTranspose i j r = r := by
  simp [finTranspose, hi, hj]







/-- Precompose a permutation vector `perm` with the transposition swapping rows
`i` and `j`, yielding the vector whose `r`-th entry is `perm[finTranspose i j r]`. -/
 def _root_.Hex.Matrix.transposePermutationValues {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) : Vector (Fin n) n :=
  Vector.ofFn fun r => perm[finTranspose i j r]





/-- The `r`-th entry of `transposePermutationValues perm i j` is
`perm[finTranspose i j r]`, unfolding the definition. -/
 theorem _root_.Hex.Matrix.transposePermutationValues_get {n : Nat}
    (perm : Vector (Fin n) n) (i j r : Fin n) :
    (_root_.Hex.Matrix.transposePermutationValues perm i j)[r] = perm[finTranspose i j r] := by
  simp [_root_.Hex.Matrix.transposePermutationValues]







/-- `vector_get_fin_congr` transports a vector lookup across an equality of finite indices. -/
 theorem _root_.Hex.Matrix.vector_get_fin_congr {α : Type u} {n : Nat} (v : Vector α n)
    {a b : Fin n} (h : a = b) : v[a] = v[b] := by
  subst b
  rfl

/-- `vector_toList_split_two` splits a vector's list view around two strictly ordered finite indices. -/
 theorem _root_.Hex.Matrix.vector_toList_split_two {α : Type u} {n : Nat}
    (v : Vector α n) {i j : Fin n} (hij : i.val < j.val) :
    v.toList =
      v.toList.take i.val ++ v[i] ::
        (v.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          v[j] :: v.toList.drop (j.val + 1) := by
  have hi : i.val < v.toList.length := by
    simp [Vector.length_toList]
  have hjdrop : j.val - i.val - 1 < (v.toList.drop (i.val + 1)).length := by
    simp only [List.length_drop, Vector.length_toList]
    omega
  calc
    v.toList = v.toList.take i.val ++ v.toList.drop i.val := by
      exact (List.take_append_drop i.val v.toList).symm
    _ = v.toList.take i.val ++ v[i] :: v.toList.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hi]
      simp [Vector.getElem_toList]
    _ =
      v.toList.take i.val ++ v[i] ::
        (v.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          (v.toList.drop (i.val + 1)).drop (j.val - i.val - 1) := by
      rw [List.append_assoc]
      congr 1
      congr 1
      exact (List.take_append_drop (j.val - i.val - 1)
        (v.toList.drop (i.val + 1))).symm
    _ =
      v.toList.take i.val ++ v[i] ::
        (v.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          v[j] :: v.toList.drop (j.val + 1) := by
      have hmid : i.val + 1 + (j.val - i.val - 1) = j.val := by
        omega
      have hdrop : i.val + 1 + ((j.val - i.val - 1) + 1) = j.val + 1 := by
        omega
      rw [List.drop_eq_getElem_cons hjdrop]
      simp [List.drop_drop, Vector.getElem_toList, List.getElem_drop, hmid, hdrop]

/-- `transposePermutationValues_take_of_lt` identifies the unchanged prefix before the first transposed index. -/
 theorem _root_.Hex.Matrix.transposePermutationValues_take_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    (_root_.Hex.Matrix.transposePermutationValues perm i j).toList.take i.val =
      perm.toList.take i.val := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k hk₁ hk₂
    simp [Vector.length_toList] at hk₁ hk₂
    have hk : k < n := by omega
    have hki : (⟨k, hk⟩ : Fin n) ≠ i := by
      intro h
      have : k = i.val := by simpa using congrArg Fin.val h
      omega
    have hkj : (⟨k, hk⟩ : Fin n) ≠ j := by
      intro h
      have : k = j.val := by simpa using congrArg Fin.val h
      omega
    calc
      (List.take i.val (_root_.Hex.Matrix.transposePermutationValues perm i j).toList)[k] =
          (_root_.Hex.Matrix.transposePermutationValues perm i j)[k]'hk := by
        simp [Vector.getElem_toList]
      _ = perm[k]'hk := by
        change (_root_.Hex.Matrix.transposePermutationValues perm i j)[(⟨k, hk⟩ : Fin n)] =
          perm[(⟨k, hk⟩ : Fin n)]
        rw [_root_.Hex.Matrix.transposePermutationValues_get]
        exact _root_.Hex.Matrix.vector_get_fin_congr perm (_root_.Hex.Matrix.finTranspose_of_ne i j ⟨k, hk⟩ hki hkj)
      _ = (List.take i.val perm.toList)[k] := by
        simp [Vector.getElem_toList]

/-- `transposePermutationValues_middle_of_lt` identifies the unchanged middle segment between two transposed indices. -/
 theorem _root_.Hex.Matrix.transposePermutationValues_middle_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    ((_root_.Hex.Matrix.transposePermutationValues perm i j).toList.drop (i.val + 1)).take
        (j.val - i.val - 1) =
      (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k hk₁ hk₂
    simp [Vector.length_toList] at hk₁ hk₂
    have hrlt : i.val + 1 + k < n := by
      omega
    have hri : (⟨i.val + 1 + k, hrlt⟩ : Fin n) ≠ i := by
      intro h
      have : i.val + 1 + k = i.val := by simpa using congrArg Fin.val h
      omega
    have hrj : (⟨i.val + 1 + k, hrlt⟩ : Fin n) ≠ j := by
      intro h
      have : i.val + 1 + k = j.val := by simpa using congrArg Fin.val h
      omega
    calc
      (List.take (j.val - i.val - 1)
          (List.drop (i.val + 1) (_root_.Hex.Matrix.transposePermutationValues perm i j).toList))[k] =
          (_root_.Hex.Matrix.transposePermutationValues perm i j)[i.val + 1 + k]'hrlt := by
        simp [Vector.getElem_toList]
      _ = perm[i.val + 1 + k]'hrlt := by
        change (_root_.Hex.Matrix.transposePermutationValues perm i j)[(⟨i.val + 1 + k, hrlt⟩ : Fin n)] =
          perm[(⟨i.val + 1 + k, hrlt⟩ : Fin n)]
        rw [_root_.Hex.Matrix.transposePermutationValues_get]
        exact _root_.Hex.Matrix.vector_get_fin_congr perm
          (_root_.Hex.Matrix.finTranspose_of_ne i j ⟨i.val + 1 + k, hrlt⟩ hri hrj)
      _ =
          (List.take (j.val - i.val - 1) (List.drop (i.val + 1) perm.toList))[k] := by
        simp [Vector.getElem_toList]

/-- `transposePermutationValues_drop_of_lt` identifies the unchanged suffix after the second transposed index. -/
 theorem _root_.Hex.Matrix.transposePermutationValues_drop_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    (_root_.Hex.Matrix.transposePermutationValues perm i j).toList.drop (j.val + 1) =
      perm.toList.drop (j.val + 1) := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro k hk₁ hk₂
    simp [Vector.length_toList] at hk₁ hk₂
    have hrlt : j.val + 1 + k < n := by
      omega
    have hri : (⟨j.val + 1 + k, hrlt⟩ : Fin n) ≠ i := by
      intro h
      have : j.val + 1 + k = i.val := by simpa using congrArg Fin.val h
      omega
    have hrj : (⟨j.val + 1 + k, hrlt⟩ : Fin n) ≠ j := by
      intro h
      have : j.val + 1 + k = j.val := by simpa using congrArg Fin.val h
      omega
    calc
      (List.drop (j.val + 1) (_root_.Hex.Matrix.transposePermutationValues perm i j).toList)[k] =
          (_root_.Hex.Matrix.transposePermutationValues perm i j)[j.val + 1 + k]'hrlt := by
        simp [Vector.getElem_toList]
      _ = perm[j.val + 1 + k]'hrlt := by
        change (_root_.Hex.Matrix.transposePermutationValues perm i j)[(⟨j.val + 1 + k, hrlt⟩ : Fin n)] =
          perm[(⟨j.val + 1 + k, hrlt⟩ : Fin n)]
        rw [_root_.Hex.Matrix.transposePermutationValues_get]
        exact _root_.Hex.Matrix.vector_get_fin_congr perm
          (_root_.Hex.Matrix.finTranspose_of_ne i j ⟨j.val + 1 + k, hrlt⟩ hri hrj)
      _ = (List.drop (j.val + 1) perm.toList)[k] := by
        simp [Vector.getElem_toList]

/-- `transposePermutationValues_toList_of_lt` expands the list view when the left transposed index is strictly before the right one. -/
 theorem _root_.Hex.Matrix.transposePermutationValues_toList_of_lt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hij : i.val < j.val) :
    (_root_.Hex.Matrix.transposePermutationValues perm i j).toList =
      perm.toList.take i.val ++ perm[j] ::
        (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
          perm[i] :: perm.toList.drop (j.val + 1) := by
  rw [_root_.Hex.Matrix.vector_toList_split_two (_root_.Hex.Matrix.transposePermutationValues perm i j) hij,
    _root_.Hex.Matrix.transposePermutationValues_take_of_lt perm hij,
    _root_.Hex.Matrix.transposePermutationValues_middle_of_lt perm hij,
    _root_.Hex.Matrix.transposePermutationValues_drop_of_lt perm hij]
  have hi : (_root_.Hex.Matrix.transposePermutationValues perm i j)[i] = perm[j] := by
    rw [_root_.Hex.Matrix.transposePermutationValues_get]
    exact _root_.Hex.Matrix.vector_get_fin_congr perm (_root_.Hex.Matrix.finTranspose_left i j)
  have hj : (_root_.Hex.Matrix.transposePermutationValues perm i j)[j] = perm[i] := by
    rw [_root_.Hex.Matrix.transposePermutationValues_get]
    exact _root_.Hex.Matrix.vector_get_fin_congr perm (_root_.Hex.Matrix.finTranspose_right i j)
  rw [hi, hj]

/-- `transposePermutationValues_toList_of_gt` expands the list view when the right transposed index is strictly before the left one. -/
 theorem _root_.Hex.Matrix.transposePermutationValues_toList_of_gt {n : Nat}
    (perm : Vector (Fin n) n) {i j : Fin n} (hji : j.val < i.val) :
    (_root_.Hex.Matrix.transposePermutationValues perm i j).toList =
      perm.toList.take j.val ++ perm[i] ::
        (perm.toList.drop (j.val + 1)).take (i.val - j.val - 1) ++
          perm[j] :: perm.toList.drop (i.val + 1) := by
  have hcomm : _root_.Hex.Matrix.transposePermutationValues perm i j = _root_.Hex.Matrix.transposePermutationValues perm j i := by
    ext r hr
    apply Fin.val_eq_of_eq
    change (_root_.Hex.Matrix.transposePermutationValues perm i j)[(⟨r, hr⟩ : Fin n)] =
      (_root_.Hex.Matrix.transposePermutationValues perm j i)[(⟨r, hr⟩ : Fin n)]
    repeat rw [_root_.Hex.Matrix.transposePermutationValues_get]
    by_cases hri : (⟨r, hr⟩ : Fin n) = i
    · subst i
      exact _root_.Hex.Matrix.vector_get_fin_congr perm
        ((_root_.Hex.Matrix.finTranspose_left ⟨r, hr⟩ j).trans
          (_root_.Hex.Matrix.finTranspose_right j ⟨r, hr⟩).symm)
    · by_cases hrj : (⟨r, hr⟩ : Fin n) = j
      · subst j
        exact _root_.Hex.Matrix.vector_get_fin_congr perm
          ((_root_.Hex.Matrix.finTranspose_right i ⟨r, hr⟩).trans
            (_root_.Hex.Matrix.finTranspose_left ⟨r, hr⟩ i).symm)
      · exact _root_.Hex.Matrix.vector_get_fin_congr perm
          ((_root_.Hex.Matrix.finTranspose_of_ne i j ⟨r, hr⟩ hri hrj).trans
            (_root_.Hex.Matrix.finTranspose_of_ne j i ⟨r, hr⟩ hrj hri).symm)
  rw [hcomm]
  exact
    (_root_.Hex.Matrix.transposePermutationValues_toList_of_lt perm (i := j) (j := i) hji)





/-- Swap the values `i` and `j` inside a permutation vector, leaving positions
fixed. This models the column permutation induced by exchanging two columns. -/
@[expose]
def swapPermutationValues {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n) : Vector (Fin n) n :=
  perm.map (finTranspose i j)

 theorem _root_.Hex.Matrix.swapPermutationValues_get {n : Nat}
    (perm : Vector (Fin n) n) (i j r : Fin n) :
    (swapPermutationValues perm i j)[r] = finTranspose i j perm[r] := by
  simp [swapPermutationValues]

/-- Entrywise characterization of `swapPermutationValues`: occurrences of
`i` become `j`, occurrences of `j` become `i`, and all other values stay put. -/
theorem swapPermutationValues_get_if {n : Nat}
    (perm : Vector (Fin n) n) (i j r : Fin n) :
    (swapPermutationValues perm i j)[r] =
      if perm[r] = i then j else if perm[r] = j then i else perm[r] := by
  rw [_root_.Hex.Matrix.swapPermutationValues_get]
  rfl







/-- `fin_mem_of_full_nodup` shows that a length-`n` nodup list of `Fin n`
values contains every `x : Fin n`, the pigeonhole fact that makes the
`inversePermutationValues` index lookup total. -/
 theorem _root_.Hex.Matrix.fin_mem_of_full_nodup {n : Nat} {xs : List (Fin n)}
    (x : Fin n) (hlen : xs.length = n) (hnodup : xs.Nodup) :
    x ∈ xs := by
  by_cases hmem : x ∈ xs
  · exact hmem
  · exfalso
    have hsubset : xs ⊆ (List.finRange n).erase x := by
      intro y hy
      refine (List.mem_erase_of_ne ?_).2 (List.mem_finRange y)
      rintro rfl
      exact hmem hy
    have hle : xs.length ≤ ((List.finRange n).erase x).length :=
      List.nodup_subset_length_le hnodup hsubset
    have herase : ((List.finRange n).erase x).length = n - 1 := by
      rw [List.length_erase]
      simp [List.mem_finRange, List.length_finRange]
    rw [hlen, herase] at hle
    cases n with
    | zero => exact Fin.elim0 x
    | succ n => omega

/-- `fin_idxOf_lt` bounds `xs.idxOf x` below `xs.length` for a
full nodup list, supplying the `Fin n` index proof obligation for the
`inversePermutationValues` entries. -/
 theorem _root_.Hex.Matrix.fin_idxOf_lt {n : Nat} {xs : List (Fin n)}
    (x : Fin n) (hlen : xs.length = n) (hnodup : xs.Nodup) :
    xs.idxOf x < xs.length := by
  exact List.idxOf_lt_length_of_mem (_root_.Hex.Matrix.fin_mem_of_full_nodup x hlen hnodup)

/-- The inverse permutation vector: at value `c`, return the position where
`c` occurs in `perm`. -/
def inversePermutationValues {n : Nat}
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    Vector (Fin n) n :=
  Vector.ofFn fun c =>
    ⟨perm.toList.idxOf c,
      by
        simpa [Vector.length_toList] using
          _root_.Hex.Matrix.fin_idxOf_lt c (by simp [Vector.length_toList]) hnodup⟩



















@[expose]
def inversePermutationVector {n : Nat}
    (perm : Vector (Fin n) n) : Vector (Fin n) n :=
  if hnodup : perm.toList.Nodup then
    inversePermutationValues perm hnodup
  else
    perm







@[expose]
def composePermutationValues {n : Nat}
    (sigma tau : Vector (Fin n) n) : Vector (Fin n) n :=
  Vector.ofFn fun i => sigma[tau[i]]

























 theorem _root_.Hex.Matrix.swapPermutationValues_eq {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) :
    let pi : Fin n := ⟨perm.toList.idxOf i,
      by simpa [Vector.length_toList] using
        _root_.Hex.Matrix.fin_idxOf_lt i (by simp [Vector.length_toList]) hnodup⟩
    let pj : Fin n := ⟨perm.toList.idxOf j,
      by simpa [Vector.length_toList] using
        _root_.Hex.Matrix.fin_idxOf_lt j (by simp [Vector.length_toList]) hnodup⟩
    swapPermutationValues perm i j = _root_.Hex.Matrix.transposePermutationValues perm pi pj := by
  dsimp
  ext r hr
  let pi : Fin n := ⟨perm.toList.idxOf i,
    by simpa [Vector.length_toList] using
      _root_.Hex.Matrix.fin_idxOf_lt i (by simp [Vector.length_toList]) hnodup⟩
  let pj : Fin n := ⟨perm.toList.idxOf j,
    by simpa [Vector.length_toList] using
      _root_.Hex.Matrix.fin_idxOf_lt j (by simp [Vector.length_toList]) hnodup⟩
  have hpi_get : perm[pi] = i := by
    have hlt : perm.toList.idxOf i < perm.toList.length := by
      simpa [pi, Vector.length_toList] using pi.isLt
    have hget : perm.toList[perm.toList.idxOf i]'hlt = i :=
      List.getElem_idxOf (x := i) (xs := perm.toList) hlt
    exact hget
  have hpj_get : perm[pj] = j := by
    have hlt : perm.toList.idxOf j < perm.toList.length := by
      simpa [pj, Vector.length_toList] using pj.isLt
    have hget : perm.toList[perm.toList.idxOf j]'hlt = j :=
      List.getElem_idxOf (x := j) (xs := perm.toList) hlt
    exact hget
  apply Fin.val_eq_of_eq
  change (swapPermutationValues perm i j)[(⟨r, hr⟩ : Fin n)] =
    (_root_.Hex.Matrix.transposePermutationValues perm pi pj)[(⟨r, hr⟩ : Fin n)]
  rw [_root_.Hex.Matrix.swapPermutationValues_get, _root_.Hex.Matrix.transposePermutationValues_get]
  by_cases hri : (⟨r, hr⟩ : Fin n) = pi
  · rw [hri]
    calc
      finTranspose i j perm[pi] = finTranspose i j i := by rw [hpi_get]
      _ = j := _root_.Hex.Matrix.finTranspose_left i j
      _ = perm[pj] := hpj_get.symm
      _ = perm[finTranspose pi pj pi] := by
          exact congrArg (fun x => perm[x]) (_root_.Hex.Matrix.finTranspose_left pi pj).symm
  · by_cases hrj : (⟨r, hr⟩ : Fin n) = pj
    · rw [hrj]
      calc
        finTranspose i j perm[pj] = finTranspose i j j := by rw [hpj_get]
        _ = i := _root_.Hex.Matrix.finTranspose_right i j
        _ = perm[pi] := hpi_get.symm
        _ = perm[finTranspose pi pj pj] := by
            exact congrArg (fun x => perm[x]) (_root_.Hex.Matrix.finTranspose_right pi pj).symm
    · have hnot_i : perm[(⟨r, hr⟩ : Fin n)] ≠ i := by
        intro hv
        have hridx : perm.toList.idxOf perm[(⟨r, hr⟩ : Fin n)] = r := by
          have hrlen : r < perm.toList.length := by
            simpa [Vector.length_toList] using hr
          exact hnodup.idxOf_getElem r hrlen
        have hval : r = pi.val := by
          calc
            r = perm.toList.idxOf perm[(⟨r, hr⟩ : Fin n)] := hridx.symm
            _ = perm.toList.idxOf i := by rw [hv]
            _ = pi.val := rfl
        exact hri (Fin.ext hval)
      have hnot_j : perm[(⟨r, hr⟩ : Fin n)] ≠ j := by
        intro hv
        have hridx : perm.toList.idxOf perm[(⟨r, hr⟩ : Fin n)] = r := by
          have hrlen : r < perm.toList.length := by
            simpa [Vector.length_toList] using hr
          exact hnodup.idxOf_getElem r hrlen
        have hval : r = pj.val := by
          calc
            r = perm.toList.idxOf perm[(⟨r, hr⟩ : Fin n)] := hridx.symm
            _ = perm.toList.idxOf j := by rw [hv]
            _ = pj.val := rfl
        exact hrj (Fin.ext hval)
      rw [_root_.Hex.Matrix.finTranspose_of_ne i j perm[(⟨r, hr⟩ : Fin n)] hnot_i hnot_j]
      exact _root_.Hex.Matrix.vector_get_fin_congr perm (_root_.Hex.Matrix.finTranspose_of_ne pi pj ⟨r, hr⟩ hri hrj).symm

 theorem _root_.Hex.Matrix.inversionCount_transposePermutationValues_parity {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) (h : i ≠ j) :
    inversionCount (_root_.Hex.Matrix.transposePermutationValues perm i j).toList % 2 =
      (inversionCount perm.toList + 1) % 2 := by
  have hval : i.val ≠ j.val := by
    intro hv
    exact h (Fin.ext hv)
  cases Nat.lt_or_gt_of_ne hval with
  | inl hij =>
      have hnodup_split :
          (perm.toList.take i.val ++ perm[i] ::
              (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
                perm[j] :: perm.toList.drop (j.val + 1)).Nodup := by
        rw [← _root_.Hex.Matrix.vector_toList_split_two perm hij]
        exact hnodup
      have hpar :
          inversionCount
              (perm.toList.take i.val ++ perm[j] ::
                (perm.toList.drop (i.val + 1)).take (j.val - i.val - 1) ++
                  perm[i] :: perm.toList.drop (j.val + 1)) %
              2 =
            (inversionCount perm.toList + 1) % 2 := by
        have hswap :=
          _root_.Hex.Matrix.inversionCount_swap_separated_parity
            (perm.toList.take i.val)
            ((perm.toList.drop (i.val + 1)).take (j.val - i.val - 1))
            (perm.toList.drop (j.val + 1)) perm[i] perm[j] hnodup_split
        rw [← _root_.Hex.Matrix.vector_toList_split_two perm hij] at hswap
        exact hswap
      rw [_root_.Hex.Matrix.transposePermutationValues_toList_of_lt perm hij]
      exact hpar
  | inr hji =>
      have hnodup_split :
          (perm.toList.take j.val ++ perm[j] ::
              (perm.toList.drop (j.val + 1)).take (i.val - j.val - 1) ++
                perm[i] :: perm.toList.drop (i.val + 1)).Nodup := by
        rw [← _root_.Hex.Matrix.vector_toList_split_two perm hji]
        exact hnodup
      have hpar :
          inversionCount
              (perm.toList.take j.val ++ perm[i] ::
                (perm.toList.drop (j.val + 1)).take (i.val - j.val - 1) ++
                  perm[j] :: perm.toList.drop (i.val + 1)) %
              2 =
            (inversionCount perm.toList + 1) % 2 := by
        have hswap :=
          _root_.Hex.Matrix.inversionCount_swap_separated_parity
            (perm.toList.take j.val)
            ((perm.toList.drop (j.val + 1)).take (i.val - j.val - 1))
            (perm.toList.drop (i.val + 1)) perm[j] perm[i] hnodup_split
        rw [← _root_.Hex.Matrix.vector_toList_split_two perm hji] at hswap
        exact hswap
      rw [_root_.Hex.Matrix.transposePermutationValues_toList_of_gt perm hji]
      exact hpar



 theorem _root_.Hex.Matrix.detSign_transposeValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) (h : i ≠ j) :
    detSign (R := R) perm = -detSign (R := R) (_root_.Hex.Matrix.transposePermutationValues perm i j) := by
  unfold detSign
  have hpar :=
    _root_.Hex.Matrix.inversionCount_transposePermutationValues_parity perm i j hnodup h
  by_cases hp : inversionCount perm.toList % 2 = 0
  · have ht : inversionCount (_root_.Hex.Matrix.transposePermutationValues perm i j).toList % 2 ≠ 0 := by
      omega
    simp [hp, ht]
    grind
  · have hpone : inversionCount perm.toList % 2 = 1 := by
      have hlt : inversionCount perm.toList % 2 < 2 := Nat.mod_lt _ (by decide)
      omega
    have ht : inversionCount (_root_.Hex.Matrix.transposePermutationValues perm i j).toList % 2 = 0 := by
      omega
    simp [hp, ht]

/-- Swapping two distinct values in a duplicate-free permutation vector flips
the determinant sign. This is the sign bookkeeping for column swaps. -/
theorem detSign_swapPermutationValues {R : Type u}
    [Lean.Grind.CommRing R] {n : Nat}
    (perm : Vector (Fin n) n) (i j : Fin n)
    (hnodup : perm.toList.Nodup) (h : i ≠ j) :
    detSign (R := R) perm = -detSign (R := R) (swapPermutationValues perm i j) := by
  let pi : Fin n := ⟨perm.toList.idxOf i,
    by simpa [Vector.length_toList] using
      _root_.Hex.Matrix.fin_idxOf_lt i (by simp [Vector.length_toList]) hnodup⟩
  let pj : Fin n := ⟨perm.toList.idxOf j,
    by simpa [Vector.length_toList] using
      _root_.Hex.Matrix.fin_idxOf_lt j (by simp [Vector.length_toList]) hnodup⟩
  have hpij : pi ≠ pj := by
    intro hp
    have hpi_get : perm[pi] = i := by
      have hlt : perm.toList.idxOf i < perm.toList.length := by
        simpa [pi, Vector.length_toList] using pi.isLt
      have hget : perm.toList[perm.toList.idxOf i]'hlt = i :=
        List.getElem_idxOf (x := i) (xs := perm.toList) hlt
      exact hget
    have hpj_get : perm[pj] = j := by
      have hlt : perm.toList.idxOf j < perm.toList.length := by
        simpa [pj, Vector.length_toList] using pj.isLt
      have hget : perm.toList[perm.toList.idxOf j]'hlt = j :=
        List.getElem_idxOf (x := j) (xs := perm.toList) hlt
      exact hget
    exact h (by rw [← hpi_get, ← hpj_get, hp])
  have hswap :
      swapPermutationValues perm i j = _root_.Hex.Matrix.transposePermutationValues perm pi pj := by
    simpa [pi, pj] using _root_.Hex.Matrix.swapPermutationValues_eq perm i j hnodup
  rw [hswap]
  exact _root_.Hex.Matrix.detSign_transposeValues (R := R) perm pi pj hnodup hpij















end Matrix
end Hex

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end


