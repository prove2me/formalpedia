-- Prove2me | Definitions.Def_LARLLL_GramSchmidtRational
-- name    : LARLLL_GramSchmidtRational
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T02:14:17.849797+00:00
-- url     : https://prove2.me/theorems/c9556616-4e69-4bb4-8d1d-18c661d164ed
-- title:
--   Checked rational Gram-Schmidt program foundations
-- statement:
--   Exact row-echelon contract interfaces, row-span invariants, and the vector-valued rational Gram-Schmidt loop and its linearity interfaces used by the existing LLL algorithm. This source-faithful bundle introduces no assumption about full LLL bit complexity.
-- source:
--   Apache-2.0 original leanprover/hex libraries, ported and kernel checked in the existing native LLL development. Whole declaration commands were selected using the official Lean declaration/sketch and structural syntax oracles. Exact original module locations, source SHA-256 values, and unchanged checked data values are recorded in the validation receipt. Compiler csimp equality proofs and notices are preserved. Current source SHA-256: f68fcffdafc076507b36ef1f4639dc0570814038db50d7d39266a902ca2f3efd.

import Definitions.Def_LARLLL_Foundation01

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/






set_option autoImplicit true



section

/-!
Echelon-form data and contracts.

`RowEchelonData` is the pure result of an echelon-form algorithm (rank, echelon
matrix, accumulated transform, pivot columns). `IsEchelonForm` is the shared
contract for any echelon form; `IsRowReduced` extends it with the
reduced-row-echelon conditions (pivots are one, entries above pivots vanish).
The `IsEchelonForm` namespace lemmas develop the pivot/free-column partition
used by the span and nullspace APIs.
-/

namespace Hex

universe u

namespace Matrix

/-- Pure data produced by an echelon-form algorithm. -/
structure RowEchelonData (R : Type u) (n m : Nat) where
  /-- Number of pivots, i.e. the rank of the original matrix. -/
  rank : Nat
  /-- The matrix reduced to row-echelon form. -/
  echelon : Matrix R n m
  /-- The accumulated row-operation transform `T` with `T * original = echelon`. -/
  transform : Matrix R n n
  /-- Column index of each pivot, in increasing order. -/
  pivotCols : Vector (Fin m) rank





namespace IsEchelonForm

variable [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
variable {M : Matrix R n m} {D : RowEchelonData R n m}













































end IsEchelonForm

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
Row-span API over the echelon contracts.

The `IsEchelonForm` section transports row combinations across the echelon
transform and builds the decidable row-span tests `spanCoeffs`/`spanContains`
with their soundness lemmas. The `IsRowReduced` section adds the helper theory
(pivot-column structure, single-row combinations) and proves the tests complete
(`spanCoeffs_complete`, `spanContains_iff`).
-/

namespace Hex

universe u

namespace Matrix

variable {R : Type u} {n m : Nat}

namespace IsEchelonForm







variable [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
variable {M : Matrix R n m} {D : RowEchelonData R n m}













end IsEchelonForm

namespace IsRowReduced



variable {M : Matrix R n m} {D : RowEchelonData R n m}

 theorem _root_.Hex.Matrix.IsRowReduced.foldl_indicator_mul_unique {R : Type u} [Lean.Grind.Ring R]
    {n : Nat} (xs : List (Fin n)) (i : Fin n) (f : Fin n → R)
    (hi : i ∈ xs) (hnodup : xs.Nodup) (acc : R) :
    xs.foldl (fun acc l => acc + (if i = l then (1 : R) else 0) * f l) acc =
      acc + f i := by
  induction xs generalizing acc with
  | nil =>
      exact absurd hi List.not_mem_nil
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hi with hieq | hitail
      · subst i
        have hxs_zero :
            ∀ y ∈ xs, (if x = y then (1 : R) else 0) * f y = 0 := by
          intro y hy
          have hxy : x ≠ y := fun heq => (List.nodup_cons.mp hnodup).1 (heq ▸ hy)
          rw [if_neg hxy]
          grind
        rw [if_pos rfl, List.foldl_add_eq_self xs _ _ hxs_zero]
        grind
      · have hxi : i ≠ x := by
          intro heq
          rw [← heq] at hnodup
          exact (List.nodup_cons.mp hnodup).1 hitail
        rw [if_neg hxi]
        have hzero : (0 : R) * f x = 0 := by grind
        rw [hzero]
        have hacc : acc + (0 : R) = acc := by grind
        rw [hacc, ih hitail (List.nodup_cons.mp hnodup).2 acc]

/-- A row-combination vector with a single coefficient `1` at row `i`
and zero elsewhere selects exactly row `i` of the matrix. This packages
the singleton-row case used by span and RREF arguments. -/
theorem vecMul_single {R : Type u} [Lean.Grind.CommRing R]
    {n m : Nat} (M : Matrix R n m) (i : Fin n) :
    vecMul (Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0) M =
      row M i := by
  ext j hj
  let jf : Fin m := ⟨j, hj⟩
  show ((Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0) * M)[jf] =
    (row M i)[jf]
  rw [getElem_vecMul, getElem_row]
  unfold Vector.dotProduct
  have hbody :
      (List.finRange n).foldl
          (fun acc l => acc +
            (col M jf)[l] *
            (Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0)[l]) 0 =
        (List.finRange n).foldl
          (fun acc l => acc + (if i = l then (1 : R) else 0) * M[l][jf]) 0 := by
    apply List.foldl_add_congr
    intro l _hl
    have hind : (Vector.ofFn fun l : Fin n => if i = l then (1 : R) else 0)[l]
        = if i = l then (1 : R) else 0 := by
      simp
    rw [getElem_col, hind]
    by_cases hil : i = l
    · simp [hil, Lean.Grind.CommSemiring.mul_comm]
    · rw [if_neg hil]
      grind
  rw [hbody]
  have hpick := _root_.Hex.Matrix.IsRowReduced.foldl_indicator_mul_unique (R := R) (List.finRange n) i
    (fun l : Fin n => M[l][jf]) (List.mem_finRange i) (List.nodup_finRange n) 0
  have hzero : (0 : R) + M[i][jf] = M[i][jf] := by grind
  exact hpick.trans hzero













end IsRowReduced

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
Principal submatrices and row prefixes.
-/

namespace Hex

universe u

namespace Matrix









/-- Leading principal `k × k` submatrix of a square matrix: the top-left block
indexed by `{0, …, k-1}` along both axes. Includes the empty submatrix
(`k = 0`) and is convenient for Bareiss pivot/minor statements. -/
@[expose]
def principalSubmatrix (M : Matrix R n n) (k : Nat) (hk : k ≤ n) : Matrix R k k :=
  ofFn fun i j =>
    let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
    M[(ii, jj)]



/-- Entry formula for the `k × k` principal submatrix. -/
@[grind =] theorem getElem_principalSubmatrix (M : Matrix R n n) (k : Nat) (hk : k ≤ n)
    (i j : Fin k) :
    (principalSubmatrix M k hk)[i][j] =
      (let ii : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
       let jj : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
       M[ii][jj]) := by
  unfold principalSubmatrix
  rw [getElem_ofFn, getElem_pair_eq_nested]















end Matrix

/-! # Copy-free submatrix views

A `Submatrix R rows cols` is a **view** into a backing `Matrix R N M`: a row/column
offset plus the real-data extent, with the logical `rows × cols` shape carried as
type indices. Reading entry `(i, j)` is pure offset arithmetic into the shared flat
buffer (`base[(r0 + i, c0 + j)]`) when that position holds real data, and `0`
otherwise — the zero-fill lets a view stand for a matrix logically padded past its
data without copying. The backing dims `N, M` never change through a recursion, so
`r0 + i < rhi` (the real-row bound, a prefix of the logical rows) is the exact
real-vs-pad test at every nesting depth. Quadrant-of-a-view is a view (offset
arithmetic, no copy); this is the recursion surface `mulStrassen` runs over
(`HexMatrix/Strassen.lean`). -/



namespace Submatrix

variable {R : Type u} {rows cols : Nat}

































end Submatrix

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
Executable Gram-Schmidt orthogonalization kernel for `hex-gram-schmidt`.

This module is the rational core that the rest of the library builds on. It
defines the projection primitives (`projectionCoeff`, `subtractProjection`),
the per-row reduction `reduceAgainstBasis`, the left-to-right orthogonalization
`basisRows`/`basisMatrix`, the coefficient matrix `coeffMatrix`, and the
supporting entry/prefix helpers (`entry`, `castIntMatrix`, `prefixCombination`,
`prefixRows`, `prefixSpan`). It also proves the foundational facts the
correspondence proofs consume: pairwise orthogonality of `basisRows`, the
residual/projection reconstruction identity, the leading-row equation, and the
zero-norm degeneracy lemmas (a `Rat` vector with zero self-dot-product is the
zero vector).
-/
namespace Hex
namespace GramSchmidt

/-- Coefficient of the orthogonal projection of `row` onto `basisRow`.
When the basis row has zero norm we use `0`, which matches the degenerate
case of Gram-Schmidt where the corresponding projection term vanishes. -/
@[expose]
def projectionCoeff (row basisRow : Vector Rat m) : Rat :=
  let denom := basisRow.dotProduct basisRow
  if denom = 0 then 0 else row.dotProduct basisRow / denom

/-- Subtract the projection of `row` onto `basisRow`. -/
@[expose]
def subtractProjection (row basisRow : Vector Rat m) : Vector Rat m :=
  row - projectionCoeff row basisRow • basisRow

/-- `dot (subtractProjection row basisRow) target` expands as `dot row target`
minus the projection coefficient times `dot basisRow target`. -/
 theorem _root_.Hex.GramSchmidt.dot_subtractProjection (row basisRow target : Vector Rat m) :
    (subtractProjection row basisRow).dotProduct target =
      row.dotProduct target - projectionCoeff row basisRow * basisRow.dotProduct target := by
  simp [subtractProjection, Vector.dotProduct_sub_smul_left]

/-- Reconstruction identity: `row` is the sum of its residual
`subtractProjection row basisRow` and its projection onto `basisRow`. -/
 theorem _root_.Hex.GramSchmidt.subtractProjection_add_projection (row basisRow : Vector Rat m) :
    row = subtractProjection row basisRow + projectionCoeff row basisRow • basisRow := by
  apply Vector.ext
  intro k hk
  change row[k] =
    (subtractProjection row basisRow + projectionCoeff row basisRow • basisRow)[k]
  rw [Vector.getElem_add, subtractProjection, Vector.getElem_sub, Vector.getElem_smul]
  grind

/-- The residual `subtractProjection row basisRow` is orthogonal to `basisRow`
whenever `basisRow` has nonzero norm. -/
 theorem _root_.Hex.GramSchmidt.dot_subtractProjection_self_zero (row basisRow : Vector Rat m)
    (hnorm : basisRow.dotProduct basisRow ≠ 0) :
    (subtractProjection row basisRow).dotProduct basisRow = 0 := by
  rw [_root_.Hex.GramSchmidt.dot_subtractProjection]
  simp [projectionCoeff, hnorm]
  grind

/-- A rational multiplied by itself is nonnegative. -/
 theorem _root_.Hex.GramSchmidt.rat_mul_self_nonneg (x : Rat) : 0 ≤ x * x := by
  simpa [Lean.Grind.Semiring.pow_two] using (Lean.Grind.OrderedRing.sq_nonneg (a := x))

/-- A rational `x` with `x * x ≤ 0` is zero. -/
 theorem _root_.Hex.GramSchmidt.rat_mul_self_eq_zero_of_nonpos (x : Rat) (h : x * x ≤ 0) : x = 0 := by
  have hnonneg : 0 ≤ x * x := _root_.Hex.GramSchmidt.rat_mul_self_nonneg x
  have hsquare : x * x = 0 := by
    grind
  grind

/-- Folding the sum of squares `v[i] * v[i]` only increases the accumulator, so
the starting value is a lower bound for the result. -/
 theorem _root_.Hex.GramSchmidt.foldl_dot_self_start_le (xs : List (Fin m)) (v : Vector Rat m)
    (acc : Rat) (hacc : 0 ≤ acc) :
    acc ≤ xs.foldl (fun sum i => sum + v[i] * v[i]) acc := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hsq : 0 ≤ v[i] * v[i] := _root_.Hex.GramSchmidt.rat_mul_self_nonneg v[i]
      have hnext : 0 ≤ acc + v[i] * v[i] := by grind
      exact Rat.le_trans (by grind) (ih (acc := acc + v[i] * v[i]) hnext)

/-- If the folded sum of squares `v[i] * v[i]` is zero starting from a
nonnegative accumulator, then every entry `v[i]` over the folded list is zero. -/
 theorem _root_.Hex.GramSchmidt.foldl_dot_self_eq_zero_of_mem (xs : List (Fin m)) (v : Vector Rat m)
    (acc : Rat) (hacc : 0 ≤ acc)
    (hzero : xs.foldl (fun sum i => sum + v[i] * v[i]) acc = 0) :
    ∀ i ∈ xs, v[i] = 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons head rest ih =>
      intro i hi
      simp only [List.mem_cons] at hi
      have hsq : 0 ≤ v[head] * v[head] := _root_.Hex.GramSchmidt.rat_mul_self_nonneg v[head]
      have hnext_nonneg : 0 ≤ acc + v[head] * v[head] := by grind
      have hnext_le_zero :
          acc + v[head] * v[head] ≤ 0 := by
        have hle :=
          _root_.Hex.GramSchmidt.foldl_dot_self_start_le (xs := rest) (v := v)
            (acc := acc + v[head] * v[head]) hnext_nonneg
        have hzero' :
            rest.foldl (fun sum i => sum + v[i] * v[i])
              (acc + v[head] * v[head]) = 0 := by
          simpa using hzero
        rw [hzero'] at hle
        exact hle
      have hnext_zero : acc + v[head] * v[head] = 0 := by grind
      have hhead_zero : v[head] = 0 := by
        apply _root_.Hex.GramSchmidt.rat_mul_self_eq_zero_of_nonpos
        grind
      cases hi with
      | inl h =>
          subst i
          exact hhead_zero
      | inr h =>
          exact ih (acc := acc + v[head] * v[head]) hnext_nonneg hzero i h

/-- A vector with zero self-dot-product has every coordinate equal to zero. -/
 theorem _root_.Hex.GramSchmidt.dot_self_eq_zero_get (v : Vector Rat m)
    (hzero : v.dotProduct v = 0) (i : Fin m) :
    v[i] = 0 := by
  have hmem : i ∈ List.finRange m := by
    simp
  exact _root_.Hex.GramSchmidt.foldl_dot_self_eq_zero_of_mem (xs := List.finRange m) (v := v)
    (acc := 0) (by decide)
    (by simpa [Vector.dotProduct, Fin.foldl_eq_finRange_foldl] using hzero) i hmem

/-- Over `Rat`, a vector whose self-dot-product is zero is the zero vector, so
its dot product with any other row also vanishes. Used to discharge the
degenerate zero-norm basis row case when reasoning about orthogonality. -/
theorem dot_zero_of_dot_self_zero (row v : Vector Rat m)
    (hzero : v.dotProduct v = 0) :
    row.dotProduct v = 0 := by
  unfold Vector.dotProduct
  induction List.finRange m with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [_root_.Hex.GramSchmidt.dot_self_eq_zero_get v hzero i, show row[i] * (0 : Rat) = 0 by grind,
        show (0 : Rat) + 0 = 0 by grind]
      change xs.foldl (fun acc i => acc + row[i] * v[i]) 0 = 0
      exact ih

/-- When `basisRow` has zero norm, `subtractProjection row basisRow` is still
orthogonal to `basisRow`. -/
 theorem _root_.Hex.GramSchmidt.dot_subtractProjection_self_zero_of_dot_self_zero
    (row basisRow : Vector Rat m)
    (hnorm : basisRow.dotProduct basisRow = 0) :
    (subtractProjection row basisRow).dotProduct basisRow = 0 := by
  exact dot_zero_of_dot_self_zero (row := subtractProjection row basisRow)
    (v := basisRow) hnorm

/-- The folded dot product is symmetric in `u` and `v` when the two
accumulators start equal. -/
 theorem _root_.Hex.GramSchmidt.foldl_dot_comm_rat (xs : List (Fin m)) (u v : Vector Rat m)
    (accU accV : Rat) (hacc : accU = accV) :
    xs.foldl (fun acc i => acc + u[i] * v[i]) accU =
      xs.foldl (fun acc i => acc + v[i] * u[i]) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp [hacc]
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      grind

/-- The rational dot product is commutative. -/
 theorem _root_.Hex.GramSchmidt.dot_comm_rat (u v : Vector Rat m) :
    u.dotProduct v = v.dotProduct u := by
  simpa [Vector.dotProduct, Fin.foldl_eq_finRange_foldl] using
    _root_.Hex.GramSchmidt.foldl_dot_comm_rat (xs := List.finRange m) (u := u) (v := v)
      (accU := 0) (accV := 0) rfl

/-- Removing a component along `otherBasisRow` that is orthogonal to `basisRow`
leaves the projection coefficient onto `basisRow` unchanged. -/
 theorem _root_.Hex.GramSchmidt.projectionCoeff_subtractProjection_eq
    (row otherBasisRow basisRow : Vector Rat m)
    (horth : otherBasisRow.dotProduct basisRow = 0) :
    projectionCoeff (subtractProjection row otherBasisRow) basisRow =
      projectionCoeff row basisRow := by
  by_cases hnorm : basisRow.dotProduct basisRow = 0
  · simp [projectionCoeff, hnorm]
  · simp [projectionCoeff, _root_.Hex.GramSchmidt.dot_subtractProjection, horth, hnorm]
    grind

/-- Reduce a row against the previously constructed orthogonal basis rows. -/
@[expose]
def reduceAgainstBasis (basisRev : List (Vector Rat m)) (row : Vector Rat m) :
    Vector Rat m :=
  basisRev.foldl subtractProjection row

/-- `reduceAgainstBasis basisRev row` has the same dot product with `target` as `row`
does, whenever `target` is orthogonal to every row in `basisRev`. -/
 theorem _root_.Hex.GramSchmidt.dot_reduceAgainstBasis_zero_of_forall_dot_zero
    (basisRev : List (Vector Rat m)) (row target : Vector Rat m)
    (horth : ∀ basisRow ∈ basisRev, basisRow.dotProduct target = 0) :
    (reduceAgainstBasis basisRev row).dotProduct target = row.dotProduct target := by
  induction basisRev generalizing row with
  | nil =>
      simp [reduceAgainstBasis]
  | cons basisRow rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      change (reduceAgainstBasis rest (subtractProjection row basisRow)).dotProduct target =
        row.dotProduct target
      rw [ih]
      · rw [_root_.Hex.GramSchmidt.dot_subtractProjection, horth basisRow (by simp)]
        grind
      · intro laterBasisRow hlater
        exact horth laterBasisRow (by simp [hlater])

/-- The residual `reduceAgainstBasis basisRev row` stays orthogonal to `target` when both
`row` and every row in `basisRev` are orthogonal to `target`. -/
 theorem _root_.Hex.GramSchmidt.dot_reduceAgainstBasis_zero_of_dot_zero
    (basisRev : List (Vector Rat m)) (row target : Vector Rat m)
    (hrow : row.dotProduct target = 0)
    (horth : ∀ basisRow ∈ basisRev, basisRow.dotProduct target = 0) :
    (reduceAgainstBasis basisRev row).dotProduct target = 0 := by
  rw [_root_.Hex.GramSchmidt.dot_reduceAgainstBasis_zero_of_forall_dot_zero basisRev row target horth, hrow]

/-- `reduceAgainstBasis basisRev row` is orthogonal to every member of a pairwise-orthogonal
`basisRev`. -/
 theorem _root_.Hex.GramSchmidt.dot_reduceAgainstBasis_of_mem
    (basisRev : List (Vector Rat m)) (row basisRow : Vector Rat m)
    (hmem : basisRow ∈ basisRev)
    (horth : basisRev.Pairwise (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0)) :
    (reduceAgainstBasis basisRev row).dotProduct basisRow = 0 := by
  induction basisRev generalizing row with
  | nil =>
      simp at hmem
  | cons head rest ih =>
      rw [reduceAgainstBasis]
      simp only [List.foldl_cons]
      by_cases hhead : head = basisRow
      · subst basisRow
        apply _root_.Hex.GramSchmidt.dot_reduceAgainstBasis_zero_of_dot_zero
        · by_cases hnorm : head.dotProduct head = 0
          · exact _root_.Hex.GramSchmidt.dot_subtractProjection_self_zero_of_dot_self_zero row head hnorm
          · exact _root_.Hex.GramSchmidt.dot_subtractProjection_self_zero row head hnorm
        · intro later hlater
          exact (List.rel_of_pairwise_cons horth hlater).2
      · have htail : basisRow ∈ rest := by
          have hneq : basisRow ≠ head := by
            intro hb
            exact hhead hb.symm
          simp [hneq] at hmem
          exact hmem
        apply ih
        · exact htail
        · exact List.Pairwise.of_cons horth



/-- `projectionCombination row basisRev acc` accumulates onto `acc` the sum of `row`'s
projections onto each row of `basisRev`. -/
 def _root_.Hex.GramSchmidt.projectionCombination (row : Vector Rat m) (basisRev : List (Vector Rat m))
    (acc : Vector Rat m) : Vector Rat m :=
  basisRev.foldl (fun acc basisRow => acc + projectionCoeff row basisRow • basisRow) acc

/-- `projectionCombination` is unchanged when `row` is replaced by `row'` sharing the same
projection coefficient on every row of `basisRev`. -/
 theorem _root_.Hex.GramSchmidt.projectionCombination_congr
    (basisRev : List (Vector Rat m)) (row row' acc : Vector Rat m)
    (hcoeff :
      ∀ basisRow ∈ basisRev, projectionCoeff row basisRow = projectionCoeff row' basisRow) :
    _root_.Hex.GramSchmidt.projectionCombination row basisRev acc = _root_.Hex.GramSchmidt.projectionCombination row' basisRev acc := by
  induction basisRev generalizing acc with
  | nil =>
      simp [_root_.Hex.GramSchmidt.projectionCombination]
  | cons basisRow rest ih =>
      simp only [_root_.Hex.GramSchmidt.projectionCombination, List.foldl_cons]
      have hhead := hcoeff basisRow (by simp)
      rw [hhead]
      exact ih (acc := acc + projectionCoeff row' basisRow • basisRow)
        (by
          intro laterBasisRow hlater
          exact hcoeff laterBasisRow (by simp [hlater]))

/-- `subtractProjection row basisRow` plus the projection term and `acc` reassembles to
`row + acc`. -/
 theorem _root_.Hex.GramSchmidt.subtractProjection_add_projection_with_acc
    (row basisRow acc : Vector Rat m) :
    subtractProjection row basisRow +
        (acc + projectionCoeff row basisRow • basisRow) =
      row + acc := by
  apply Vector.ext
  intro k hk
  have hrow := _root_.Hex.GramSchmidt.subtractProjection_add_projection (row := row) (basisRow := basisRow)
  have hrowk := congrArg (fun v : Vector Rat m => v[k]) hrow
  simp only [Vector.getElem_add, Vector.getElem_smul] at hrowk ⊢
  grind

/-- For a pairwise-orthogonal `basisRev`, the residual plus the accumulated projection
combination reconstructs `row + acc`. -/
 theorem _root_.Hex.GramSchmidt.reduceAgainstBasis_reconstruction_acc
    (basisRev : List (Vector Rat m)) (row acc : Vector Rat m)
    (horth : basisRev.Pairwise (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0)) :
    reduceAgainstBasis basisRev row + _root_.Hex.GramSchmidt.projectionCombination row basisRev acc =
      row + acc := by
  induction basisRev generalizing row acc with
  | nil =>
      simp [reduceAgainstBasis, _root_.Hex.GramSchmidt.projectionCombination]
  | cons basisRow rest ih =>
      simp only [reduceAgainstBasis, List.foldl_cons, _root_.Hex.GramSchmidt.projectionCombination]
      change
        reduceAgainstBasis rest (subtractProjection row basisRow) +
            _root_.Hex.GramSchmidt.projectionCombination row rest
              (acc + projectionCoeff row basisRow • basisRow) =
          row + acc
      rw [← _root_.Hex.GramSchmidt.projectionCombination_congr
        (basisRev := rest)
        (row := subtractProjection row basisRow)
        (row' := row)
        (acc := acc + projectionCoeff row basisRow • basisRow)]
      · rw [ih (row := subtractProjection row basisRow)
          (acc := acc + projectionCoeff row basisRow • basisRow)
          (horth := List.Pairwise.of_cons horth)]
        exact _root_.Hex.GramSchmidt.subtractProjection_add_projection_with_acc row basisRow acc
      · intro laterBasisRow hlater
        exact _root_.Hex.GramSchmidt.projectionCoeff_subtractProjection_eq
          (row := row) (otherBasisRow := basisRow) (basisRow := laterBasisRow)
          (List.rel_of_pairwise_cons horth hlater).1

/-- For a pairwise-orthogonal `basisRev`, `row` equals its residual plus the sum of its
projections onto the basis rows. -/
 theorem _root_.Hex.GramSchmidt.reduceAgainstBasis_reconstruction
    (basisRev : List (Vector Rat m)) (row : Vector Rat m)
    (horth : basisRev.Pairwise (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0)) :
    row =
      reduceAgainstBasis basisRev row +
        _root_.Hex.GramSchmidt.projectionCombination row basisRev 0 := by
  have h :=
    _root_.Hex.GramSchmidt.reduceAgainstBasis_reconstruction_acc (basisRev := basisRev) (row := row)
      (acc := 0) horth
  have hzero : row + (0 : Vector Rat m) = row := by
    apply Vector.ext
    intro k hk
    simp
    grind
  rw [hzero] at h
  exact h.symm

/-- Left-to-right Gram-Schmidt orthogonalization on a list of rows. -/
@[expose]
def basisRowsAux (basisRev pending : List (Vector Rat m)) : List (Vector Rat m) :=
  match pending with
  | [] => basisRev.reverse
  | row :: rows =>
      let next := reduceAgainstBasis basisRev row
      basisRowsAux (next :: basisRev) rows

/-- Left-to-right Gram-Schmidt orthogonalization on a matrix's rows. -/
@[expose]
def basisRows (rows : List (Vector Rat m)) : List (Vector Rat m) :=
  basisRowsAux [] rows

/-- Rebuild a matrix from its row list after Gram-Schmidt orthogonalization. -/
@[expose]
def basisMatrix (b : Matrix Rat n m) : Matrix Rat n m :=
  let rows := basisRows b.rows.toList
  Hex.Matrix.ofRows (Vector.ofFn fun i => rows[i.val]!)

/-- `basisRowsAux basisRev pending` begins with `basisRev.reverse` as a prefix. -/
 theorem _root_.Hex.GramSchmidt.basisRowsAux_reverse_prefix (basisRev pending : List (Vector Rat m)) :
    ∃ suffix, basisRowsAux basisRev pending = basisRev.reverse ++ suffix := by
  induction pending generalizing basisRev with
  | nil =>
      exact ⟨[], by simp [basisRowsAux]⟩
  | cons row rows ih =>
      obtain ⟨suffix, hsuffix⟩ :=
        ih (GramSchmidt.reduceAgainstBasis basisRev row :: basisRev)
      refine ⟨GramSchmidt.reduceAgainstBasis basisRev row :: suffix, ?_⟩
      simp [basisRowsAux, hsuffix, List.reverse_cons, List.append_assoc]

/-- The first row produced by `basisRowsAux [row] rows` is `row` itself. -/
 theorem _root_.Hex.GramSchmidt.basisRowsAux_singleton_head (row : Vector Rat m) (rows : List (Vector Rat m)) :
    (basisRowsAux [row] rows)[0]! = row := by
  obtain ⟨suffix, hsuffix⟩ := _root_.Hex.GramSchmidt.basisRowsAux_reverse_prefix [row] rows
  simp [hsuffix]

/-- `basisRowsAux basisRev pending` has length `basisRev.length + pending.length`. -/
 theorem _root_.Hex.GramSchmidt.basisRowsAux_length (basisRev pending : List (Vector Rat m)) :
    (basisRowsAux basisRev pending).length = basisRev.length + pending.length := by
  induction pending generalizing basisRev with
  | nil =>
      simp [basisRowsAux]
  | cons row rows ih =>
      simpa [basisRowsAux, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (GramSchmidt.reduceAgainstBasis basisRev row :: basisRev)

/-- `basisRows rows` has the same length as `rows`. -/
 theorem _root_.Hex.GramSchmidt.basisRows_length (rows : List (Vector Rat m)) :
    (basisRows rows).length = rows.length := by
  simpa [basisRows] using _root_.Hex.GramSchmidt.basisRowsAux_length ([] : List (Vector Rat m)) rows

/-- `rows.reverse` is pairwise orthogonal whenever `rows` is. -/
 theorem _root_.Hex.GramSchmidt.orthPairwise_reverse (rows : List (Vector Rat m))
    (horth : rows.Pairwise (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0)) :
    rows.reverse.Pairwise (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0) := by
  rw [List.pairwise_iff_getElem] at horth ⊢
  intro i j hirev hjrev hij
  simp [List.length_reverse] at hirev hjrev
  have hji : rows.length - 1 - j < rows.length - 1 - i := by omega
  have hxj : rows.length - 1 - j < rows.length := by omega
  have hxi : rows.length - 1 - i < rows.length := by omega
  have hrel := horth (rows.length - 1 - j) (rows.length - 1 - i) hxj hxi hji
  rw [List.getElem_reverse, List.getElem_reverse]
  exact ⟨hrel.2, hrel.1⟩

/-- `basisRowsAux basisRev pending` is pairwise orthogonal whenever the accumulated basis
`basisRev` is. -/
 theorem _root_.Hex.GramSchmidt.basisRowsAux_pairwise
    (basisRev pending : List (Vector Rat m))
    (horth : basisRev.Pairwise (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0)) :
    (basisRowsAux basisRev pending).Pairwise
      (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0) := by
  induction pending generalizing basisRev with
  | nil =>
      simpa [basisRowsAux] using _root_.Hex.GramSchmidt.orthPairwise_reverse basisRev horth
  | cons row rows ih =>
      apply ih
      apply List.Pairwise.cons
      · intro basisRow hmem
        constructor
        · exact _root_.Hex.GramSchmidt.dot_reduceAgainstBasis_of_mem basisRev row basisRow hmem horth
        · rw [_root_.Hex.GramSchmidt.dot_comm_rat]
          exact _root_.Hex.GramSchmidt.dot_reduceAgainstBasis_of_mem basisRev row basisRow hmem horth
      · exact horth

/-- `basisRows rows` is a pairwise-orthogonal list of rows. -/
 theorem _root_.Hex.GramSchmidt.basisRows_pairwise (rows : List (Vector Rat m)) :
    (basisRows rows).Pairwise (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0) := by
  simpa [basisRows] using
    _root_.Hex.GramSchmidt.basisRowsAux_pairwise ([] : List (Vector Rat m)) rows (by simp)

/-- Row `i` of `basisMatrix b` is the `i`-th entry of `basisRows b.rows.toList`. -/
 theorem _root_.Hex.GramSchmidt.basisMatrix_row_eq_basisRows_get!
    (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    (basisMatrix b).row ⟨i, hi⟩ = (basisRows b.rows.toList)[i]! := by
  simp [basisMatrix, Matrix.row]



 theorem _root_.Hex.GramSchmidt.basisRows_head (b : Matrix Rat n m) (hn : 0 < n) :
    (basisRows b.rows.toList)[0]! = b[0] := by
  have hlen : b.rows.toList.length = n := by simp
  cases hrows : b.rows.toList with
  | nil =>
      simp [hrows] at hlen
      omega
  | cons row rows =>
      have hrow : row = b[0] := by
        have hget := Vector.getElem_toList (xs := b.rows) (i := 0) (h := by simpa [hlen] using hn)
        simpa [hrows, Hex.Matrix.getRow, Fin.getElem_fin] using hget
      simpa [basisRows, basisRowsAux, reduceAgainstBasis, hrows, hrow,
        Hex.Matrix.getRow, Fin.getElem_fin] using
        _root_.Hex.GramSchmidt.basisRowsAux_singleton_head (row := b.getRow ⟨0, hn⟩) (rows := rows)

/-- Gram-Schmidt coefficient matrix for an already-cast rational input. -/
@[expose]
def coeffMatrix (rows basis : Matrix Rat n m) : Matrix Rat n n :=
  Matrix.ofFn fun i j =>
    if _hlt : j.val < i.val then
      projectionCoeff (rows.getRow i) (basis.getRow j)
    else if i = j then
      1
    else
      0

/-- Access a dense matrix entry by row and column indices. -/
@[expose]
def entry (M : Matrix R n m) (i : Fin n) (j : Fin m) : R :=
  (M.row i)[j]

/-- Cast an integer matrix into the rational matrix space used by
Gram-Schmidt. -/
@[expose]
def castIntMatrix (b : Matrix Int n m) : Matrix Rat n m :=
  Hex.Matrix.ofRows (Vector.map (fun row => Vector.map (fun x : Int => (x : Rat)) row) b.rows)

/-- The prefix combination term used in the decomposition theorem shape. -/
@[expose]
def prefixCombination (coeffs : Matrix Rat n n) (basis : Matrix Rat n m) (i : Nat) (hi : i < n) :
    Vector Rat m :=
  Fin.foldl i
    (fun acc j =>
      let jn : Fin n := ⟨j.val, Nat.lt_trans j.isLt hi⟩
      acc + GramSchmidt.entry coeffs ⟨i, hi⟩ jn • basis.row jn)
    0

/-- The row-prefix matrix containing rows `0` through `i`. -/
@[expose]
def prefixRows (M : Matrix R n m) (i : Nat) (hi : i < n) : Matrix R (i + 1) m :=
  Hex.Matrix.ofRows
    (Vector.ofFn fun j => M.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt hi)⟩)

/-- Executable row-span membership in the first `i + 1` rows of a matrix. -/
@[expose]
def prefixSpan (M : Matrix Rat n m) (i : Nat) (hi : i < n) (v : Vector Rat m) : Prop :=
  ∃ c : Vector Rat (i + 1), Matrix.vecMul c (prefixRows M i hi) = v

 theorem _root_.Hex.GramSchmidt.entry_ofFn (f : Fin n → Fin m → R) (i : Fin n) (j : Fin m) :
    entry (Matrix.ofFn f) i j = f i j := by
  simp only [entry, Matrix.row]
  exact Matrix.getElem_ofFn f i j

/-- Index equation: the value at position `basisRev.length + k` of
`basisRowsAux basisRev pending` is the reduction of `pending[k]` against the
basis rows accumulated so far, which equals the reverse of the first
`basisRev.length + k` elements of the output. -/
 theorem _root_.Hex.GramSchmidt.basisRowsAux_get!_eq_reduceAgainstBasis_take
    (basisRev pending : List (Vector Rat m)) (k : Nat) (hk : k < pending.length) :
    (basisRowsAux basisRev pending)[basisRev.length + k]! =
      reduceAgainstBasis
        ((basisRowsAux basisRev pending).take (basisRev.length + k)).reverse
        pending[k]! := by
  induction pending generalizing basisRev k with
  | nil => simp at hk
  | cons row rest ih =>
    have hstep : basisRowsAux basisRev (row :: rest) =
        basisRowsAux (reduceAgainstBasis basisRev row :: basisRev) rest := rfl
    match k, hk with
    | 0, _ =>
      simp only [Nat.add_zero]
      obtain ⟨suffix, hsuffix⟩ :=
        _root_.Hex.GramSchmidt.basisRowsAux_reverse_prefix (reduceAgainstBasis basisRev row :: basisRev) rest
      rw [hstep, hsuffix]
      simp only [List.reverse_cons, List.append_assoc]
      have hlen : basisRev.length = basisRev.reverse.length := by simp
      have htake :
          (basisRev.reverse ++ ([reduceAgainstBasis basisRev row] ++ suffix)).take
              basisRev.length =
            basisRev.reverse := by
        rw [hlen]; exact List.take_append_length
      rw [htake, List.reverse_reverse]
      rw [List.getElem!_eq_getElem?_getD,
        List.getElem?_append_right (by simp)]
      simp
    | k + 1, hk =>
      have hk' : k < rest.length := by simpa using hk
      have ih' := ih (basisRev := reduceAgainstBasis basisRev row :: basisRev) (k := k) hk'
      have hidx : basisRev.length + (k + 1) =
          (reduceAgainstBasis basisRev row :: basisRev).length + k := by
        simp [List.length_cons]; omega
      rw [hstep, hidx]
      simpa [List.getElem!_cons_succ] using ih'

/-- Specialization to the public `basisRows` form. -/
 theorem _root_.Hex.GramSchmidt.basisRows_get!_eq_reduceAgainstBasis_take
    (rows : List (Vector Rat m)) (k : Nat) (hk : k < rows.length) :
    (basisRows rows)[k]! =
      reduceAgainstBasis ((basisRows rows).take k).reverse rows[k]! := by
  simpa [basisRows] using
    _root_.Hex.GramSchmidt.basisRowsAux_get!_eq_reduceAgainstBasis_take
      (basisRev := ([] : List (Vector Rat m))) (pending := rows) (k := k) hk

/-- The first `k` elements of `basisRows rows` are themselves pairwise
orthogonal — they form a Pairwise sublist. -/
 theorem _root_.Hex.GramSchmidt.basisRows_take_pairwise (rows : List (Vector Rat m)) (k : Nat) :
    ((basisRows rows).take k).Pairwise
      (fun x y => x.dotProduct y = 0 ∧ y.dotProduct x = 0) :=
  ((_root_.Hex.GramSchmidt.basisRows_pairwise rows).sublist (List.take_sublist k _))

/-- Pointwise foldl-with-accumulator-split for vector folds. -/
 theorem _root_.Hex.GramSchmidt.foldl_vec_acc_split_pointwise
    {α : Type _} (xs : List α) (f : α → Vector Rat m)
    (acc : Vector Rat m) (idx : Nat) (hidx : idx < m) :
    (xs.foldl (fun a x => a + f x) acc)[idx] =
      acc[idx] + (xs.foldl (fun a x => a + f x) 0)[idx] := by
  induction xs generalizing acc with
  | nil =>
      simp [Vector.getElem_zero]
      grind
  | cons x rest ih =>
      simp only [List.foldl_cons]
      rw [ih (acc := acc + f x), ih (acc := 0 + f x),
        Vector.getElem_add, Vector.getElem_add, Vector.getElem_zero]
      grind

/-- `projectionCombination` extracts the accumulator from the fold. -/
 theorem _root_.Hex.GramSchmidt.projectionCombination_acc_split
    (basisRev : List (Vector Rat m)) (row acc : Vector Rat m) :
    _root_.Hex.GramSchmidt.projectionCombination row basisRev acc =
      acc + _root_.Hex.GramSchmidt.projectionCombination row basisRev 0 := by
  apply Vector.ext
  intro idx hidx
  rw [Vector.getElem_add]
  exact _root_.Hex.GramSchmidt.foldl_vec_acc_split_pointwise basisRev (fun b => projectionCoeff row b • b) acc idx hidx

/-- `projectionCombination` of a concatenated list splits as a sum. -/
 theorem _root_.Hex.GramSchmidt.projectionCombination_append
    (l1 l2 : List (Vector Rat m)) (row : Vector Rat m) :
    _root_.Hex.GramSchmidt.projectionCombination row (l1 ++ l2) 0 =
      _root_.Hex.GramSchmidt.projectionCombination row l1 0 + _root_.Hex.GramSchmidt.projectionCombination row l2 0 := by
  show (l1 ++ l2).foldl
      (fun acc basisRow => acc + projectionCoeff row basisRow • basisRow) 0 =
    l1.foldl (fun acc basisRow => acc + projectionCoeff row basisRow • basisRow) 0 +
      l2.foldl (fun acc basisRow => acc + projectionCoeff row basisRow • basisRow) 0
  rw [List.foldl_append]
  exact _root_.Hex.GramSchmidt.projectionCombination_acc_split (basisRev := l2) (row := row)
    (acc := l1.foldl (fun acc basisRow => acc + projectionCoeff row basisRow • basisRow) 0)

/-- `projectionCombination` for a singleton list. -/
 theorem _root_.Hex.GramSchmidt.projectionCombination_singleton
    (b row : Vector Rat m) :
    _root_.Hex.GramSchmidt.projectionCombination row [b] 0 = projectionCoeff row b • b := by
  show List.foldl (fun acc basisRow => acc + projectionCoeff row basisRow • basisRow) 0 [b] =
    projectionCoeff row b • b
  simp only [List.foldl_cons, List.foldl_nil]
  apply Vector.ext
  intro idx hidx
  simp [Vector.getElem_add, Vector.getElem_zero]
  grind

/-- `projectionCombination` is invariant under list reversal. -/
 theorem _root_.Hex.GramSchmidt.projectionCombination_reverse
    (basisRev : List (Vector Rat m)) (row : Vector Rat m) :
    _root_.Hex.GramSchmidt.projectionCombination row basisRev.reverse 0 =
      _root_.Hex.GramSchmidt.projectionCombination row basisRev 0 := by
  induction basisRev with
  | nil => simp [_root_.Hex.GramSchmidt.projectionCombination]
  | cons b rest ih =>
      rw [List.reverse_cons, _root_.Hex.GramSchmidt.projectionCombination_append, ih,
        _root_.Hex.GramSchmidt.projectionCombination_singleton]
      have hsplit := _root_.Hex.GramSchmidt.projectionCombination_acc_split (basisRev := rest) (row := row)
        (acc := 0 + projectionCoeff row b • b)
      show _root_.Hex.GramSchmidt.projectionCombination row rest 0 + projectionCoeff row b • b =
        _root_.Hex.GramSchmidt.projectionCombination row (b :: rest) 0
      simp only [_root_.Hex.GramSchmidt.projectionCombination, List.foldl_cons] at hsplit ⊢
      rw [hsplit]
      apply Vector.ext
      intro idx hidx
      simp [Vector.getElem_add, Vector.getElem_zero]
      grind

/-- The k-th basis row obtained by the executable Gram-Schmidt iteration is
the input row k reduced against the previously generated basis rows in their
natural (forward) order. -/
 theorem _root_.Hex.GramSchmidt.basisRows_get!_eq_reduceAgainstBasis_forward
    (rows : List (Vector Rat m)) (k : Nat) (hk : k < rows.length) :
    rows[k]! =
      (basisRows rows)[k]! +
        _root_.Hex.GramSchmidt.projectionCombination rows[k]! ((basisRows rows).take k) 0 := by
  have hreduce :=
    _root_.Hex.GramSchmidt.basisRows_get!_eq_reduceAgainstBasis_take (rows := rows) (k := k) hk
  have hpair := _root_.Hex.GramSchmidt.basisRows_take_pairwise (rows := rows) (k := k)
  have horth := _root_.Hex.GramSchmidt.orthPairwise_reverse ((basisRows rows).take k) hpair
  have hrec :=
    _root_.Hex.GramSchmidt.reduceAgainstBasis_reconstruction
      (basisRev := ((basisRows rows).take k).reverse)
      (row := rows[k]!) horth
  rw [← hreduce] at hrec
  rw [_root_.Hex.GramSchmidt.projectionCombination_reverse] at hrec
  exact hrec















end GramSchmidt
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
namespace GramSchmidt
/-! Linearity-of-source helpers for `subtractProjection` and
`reduceAgainstBasis`. These let later proofs pull the reconstruction
sum across the reduction. -/





























































/-- The "by-row" prefix sum: a row-indexed variant of `prefixCombination` that
takes the projection row directly rather than reading it through a coefficient
matrix. Defined via `Fin.foldl` so the conversion to
`prefixCombination` is a pointwise function-level rewrite. -/
 def _root_.Hex.GramSchmidt.prefixSumByRow (row : Vector Rat m) (basis : Matrix Rat n m)
    (i : Nat) (hi : i ≤ n) : Vector Rat m :=
  Fin.foldl i
    (fun acc j =>
      let jn : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hi⟩
      acc + projectionCoeff row (basis.row jn) • basis.row jn)
    0

/-- The strict row prefix containing rows `0` through `k - 1`. This is the
matrix shape naturally paired with `prefixSumByRow`. -/
 def _root_.Hex.GramSchmidt.strictPrefixRows (M : Matrix R n m) (k : Nat) (hk : k ≤ n) :
    Matrix R k m :=
  Hex.Matrix.ofRows (Vector.ofFn fun j => M.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)

/-- Extend coefficients on a strict prefix by a zero coefficient on the new
last row of the inclusive prefix. -/
 def _root_.Hex.GramSchmidt.extendStrictPrefixCoeff (c : Vector Rat k) : Vector Rat (k + 1) :=
  Vector.ofFn fun j =>
    if h : j.val < k then
      let jj : Fin k := ⟨j.val, h⟩
      c[jj]
    else
      0

/-- Coefficients witnessing `prefixSumByRow` as a row combination of the strict
row prefix. -/
 def _root_.Hex.GramSchmidt.projectionCoeffVector (row : Vector Rat m) (basis : Matrix Rat n m)
    (k : Nat) (hk : k ≤ n) : Vector Rat k :=
  Vector.ofFn fun j =>
    projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)

 theorem _root_.Hex.GramSchmidt.vecMul_prefixRows_extendStrictPrefixCoeff
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) (c : Vector Rat i) :
    Matrix.vecMul (_root_.Hex.GramSchmidt.extendStrictPrefixCoeff c) (prefixRows M i hi) =
      Matrix.vecMul c (_root_.Hex.GramSchmidt.strictPrefixRows M i (Nat.le_of_lt hi)) := by
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change
    (Matrix.mulVec (Matrix.transpose (prefixRows M i hi))
        (_root_.Hex.GramSchmidt.extendStrictPrefixCoeff c))[idxFin] =
      (Matrix.mulVec (Matrix.transpose (_root_.Hex.GramSchmidt.strictPrefixRows M i (Nat.le_of_lt hi)))
        c)[idxFin]
  rw [show
      (Matrix.mulVec (Matrix.transpose (prefixRows M i hi))
          (_root_.Hex.GramSchmidt.extendStrictPrefixCoeff c))[idxFin] =
        (List.finRange (i + 1)).foldl
          (fun acc j =>
            acc +
              (M.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt hi)⟩)[idxFin] *
                (_root_.Hex.GramSchmidt.extendStrictPrefixCoeff c)[j])
          0 by
        unfold Matrix.mulVec Vector.dotProduct prefixRows
        simp [Matrix.col]]
  rw [show
      (Matrix.mulVec (Matrix.transpose (_root_.Hex.GramSchmidt.strictPrefixRows M i (Nat.le_of_lt hi)))
          c)[idxFin] =
        (List.finRange i).foldl
          (fun acc j =>
            acc +
              (M.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_of_lt hi)⟩)[idxFin] *
                c[j])
          0 by
        unfold Matrix.mulVec Vector.dotProduct _root_.Hex.GramSchmidt.strictPrefixRows
        simp [Matrix.col]]
  rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  have hlast_not_lt : ¬i < i := Nat.lt_irrefl i
  simp [_root_.Hex.GramSchmidt.extendStrictPrefixCoeff, hlast_not_lt]
  grind

 theorem _root_.Hex.GramSchmidt.vecMul_add_rat
    (M : Matrix Rat n m) (c d : Vector Rat n) :
    Matrix.vecMul (c + d) M =
      Matrix.vecMul c M + Matrix.vecMul d M := by
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change (Matrix.mulVec (Matrix.transpose M) (c + d))[idxFin] =
    (Matrix.vecMul c M + Matrix.vecMul d M)[idxFin]
  simp [Matrix.vecMul, HMul.hMul, Matrix.mulVec, Matrix.col,
    Vector.dotProduct, Vector.getElem_add]
  have hfold :
      ∀ xs : List (Fin n), ∀ accC accD : Rat,
        xs.foldl
            (fun acc row =>
              acc + M[row.val][idxFin.val] * (c[row.val] + d[row.val]))
            (accC + accD) =
          xs.foldl (fun acc row => acc + M[row.val][idxFin.val] * c[row.val]) accC +
            xs.foldl (fun acc row => acc + M[row.val][idxFin.val] * d[row.val]) accD := by
    intro xs
    induction xs with
    | nil =>
        intro accC accD
        simp
    | cons row rows ih =>
        intro accC accD
        simp only [List.foldl_cons]
        have hstep :
            accC + accD + M[row.val][idxFin.val] * (c[row.val] + d[row.val]) =
              (accC + M[row.val][idxFin.val] * c[row.val]) +
                (accD + M[row.val][idxFin.val] * d[row.val]) := by
          grind
        rw [hstep]
        exact ih (accC + M[row.val][idxFin.val] * c[row.val])
          (accD + M[row.val][idxFin.val] * d[row.val])
  have h := hfold (List.finRange n) 0 0
  rw [show (0 : Rat) + 0 = 0 by grind] at h
  exact h

 theorem _root_.Hex.GramSchmidt.vecMul_smul_rat
    (M : Matrix Rat n m) (a : Rat) (c : Vector Rat n) :
    Matrix.vecMul (a • c) M =
      a • Matrix.vecMul c M := by
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change (Matrix.mulVec (Matrix.transpose M) (a • c))[idxFin] =
    (a • Matrix.vecMul c M)[idxFin]
  simp [Matrix.vecMul, HMul.hMul, Matrix.mulVec, Matrix.col,
    Vector.dotProduct, Vector.getElem_smul]
  have hfold :
      ∀ xs : List (Fin n), ∀ acc : Rat,
        xs.foldl
            (fun acc row => acc + M[row.val][idxFin.val] * (a * c[row.val]))
            (a * acc) =
          a * xs.foldl (fun acc row => acc + M[row.val][idxFin.val] * c[row.val]) acc := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        simp
    | cons row rows ih =>
        intro acc
        simp only [List.foldl_cons]
        have hstep :
            a * acc + M[row.val][idxFin.val] * (a * c[row.val]) =
              a * (acc + M[row.val][idxFin.val] * c[row.val]) := by
          grind
        rw [hstep]
        exact ih (acc + M[row.val][idxFin.val] * c[row.val])
  have key := hfold (List.finRange n) 0
  simp only [Rat.mul_zero] at key
  exact key

/-- `prefixSpan_add` says the rational prefix row-span is closed under vector addition. -/
 theorem _root_.Hex.GramSchmidt.prefixSpan_add
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) {u v : Vector Rat m}
    (hu : prefixSpan M i hi u) (hv : prefixSpan M i hi v) :
    prefixSpan M i hi (u + v) := by
  rcases hu with ⟨cu, hcu⟩
  rcases hv with ⟨cv, hcv⟩
  refine ⟨cu + cv, ?_⟩
  rw [_root_.Hex.GramSchmidt.vecMul_add_rat, hcu, hcv]

/-- `prefixSpan_smul` says the rational prefix row-span is closed under scalar multiplication. -/
 theorem _root_.Hex.GramSchmidt.prefixSpan_smul
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) (a : Rat) {u : Vector Rat m}
    (hu : prefixSpan M i hi u) :
    prefixSpan M i hi (a • u) := by
  rcases hu with ⟨cu, hcu⟩
  refine ⟨a • cu, ?_⟩
  rw [_root_.Hex.GramSchmidt.vecMul_smul_rat, hcu]











 def _root_.Hex.GramSchmidt.unitCoeff (j : Fin n) : Vector Rat n :=
  Vector.ofFn fun k => if k = j then 1 else 0

 theorem _root_.Hex.GramSchmidt.foldl_add_eq_acc_rat
    {α : Type} (xs : List α) (f : α → Rat) (acc : Rat)
    (hf : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun acc x => acc + f x) acc = acc := by
  induction xs generalizing acc with
  | nil =>
      simp only [List.foldl_nil]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = 0 := hf x (by simp)
      have hxs : ∀ y ∈ xs, f y = 0 := fun y hy => hf y (List.mem_cons_of_mem _ hy)
      rw [hx]
      have hacc : acc + (0 : Rat) = acc := by grind
      rw [hacc]
      exact ih acc hxs

 theorem _root_.Hex.GramSchmidt.foldl_indicator_mul_unique_rat
    (xs : List (Fin n)) (i : Fin n) (f : Fin n → Rat)
    (hi : i ∈ xs) (hnodup : xs.Nodup) (acc : Rat) :
    xs.foldl (fun acc l => acc + f l * (if l = i then (1 : Rat) else 0)) acc =
      acc + f i := by
  induction xs generalizing acc with
  | nil =>
      exact absurd hi List.not_mem_nil
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hi with hix | hitail
      · subst i
        rw [if_pos rfl]
        have hxs_zero :
            ∀ y ∈ xs, f y * (if y = x then (1 : Rat) else 0) = 0 := by
          intro y hy
          have hyx : y ≠ x := by
            intro heq
            exact (List.nodup_cons.mp hnodup).1 (heq ▸ hy)
          rw [if_neg hyx]
          grind
        have hfold :=
          _root_.Hex.GramSchmidt.foldl_add_eq_acc_rat xs
            (fun l => f l * (if l = x then (1 : Rat) else 0))
            (acc + f x * 1) hxs_zero
        have hfold' :
            xs.foldl (fun acc l => acc + f l * (if l = x then (1 : Rat) else 0))
                (acc + f x * 1) =
              acc + f x * 1 := hfold
        rw [hfold']
        grind
      · have hxi : x ≠ i := by
          intro h
          subst i
          exact (List.nodup_cons.mp hnodup).1 hitail
        rw [if_neg hxi]
        have hzero : f x * (0 : Rat) = 0 := by grind
        rw [hzero]
        have hacc : acc + (0 : Rat) = acc := by grind
        rw [hacc]
        exact ih hitail (List.nodup_cons.mp hnodup).2 acc

 theorem _root_.Hex.GramSchmidt.vecMul_prefixRows_unitCoeff
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) (j : Fin (i + 1)) :
    Matrix.vecMul (_root_.Hex.GramSchmidt.unitCoeff j) (prefixRows M i hi) =
      (prefixRows M i hi).row j := by
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change
    (Matrix.mulVec (Matrix.transpose (prefixRows M i hi)) (_root_.Hex.GramSchmidt.unitCoeff j))[idxFin] =
      ((prefixRows M i hi).row j)[idxFin]
  simp [HMul.hMul, Matrix.mulVec, Matrix.col,
    Vector.dotProduct, _root_.Hex.GramSchmidt.unitCoeff]
  have h :=
    _root_.Hex.GramSchmidt.foldl_indicator_mul_unique_rat
      (xs := List.finRange (i + 1)) (i := j)
      (f := fun row : Fin (i + 1) => (prefixRows M i hi)[row.val][idxFin.val])
      (hi := List.mem_finRange j) (hnodup := List.nodup_finRange (i + 1)) (acc := 0)
  rw [show (0 : Rat) + (prefixRows M i hi)[j.val][idxFin.val] =
      (prefixRows M i hi)[j.val][idxFin.val] by grind] at h
  exact h

 theorem _root_.Hex.GramSchmidt.prefixSpan_row
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) (j : Fin (i + 1)) :
    prefixSpan M i hi ((prefixRows M i hi).row j) := by
  exact ⟨_root_.Hex.GramSchmidt.unitCoeff j, _root_.Hex.GramSchmidt.vecMul_prefixRows_unitCoeff M i hi j⟩

 theorem _root_.Hex.GramSchmidt.vecMul_eq_foldl_rows
    (M : Matrix Rat n m) (c : Vector Rat n) :
    Matrix.vecMul c M =
      Fin.foldl n (fun acc j => acc + c[j] • M.row j) 0 := by
  rw [Fin.foldl_eq_finRange_foldl]
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change (Matrix.mulVec (Matrix.transpose M) c)[idxFin] =
    ((List.finRange n).foldl (fun acc j => acc + c[j] • M.row j) 0)[idxFin]
  rw [show
      (Matrix.mulVec (Matrix.transpose M) c)[idxFin] =
        (List.finRange n).foldl
          (fun acc j => acc + M[j.val][idxFin.val] * c[j])
          0 by
        unfold Matrix.mulVec Vector.dotProduct
        simp [Matrix.col]]
  have hfold :
      ∀ xs : List (Fin n), ∀ accL : Rat, ∀ accR : Vector Rat m,
        accL = accR[idxFin] →
        xs.foldl (fun acc j => acc + M[j.val][idxFin.val] * c[j]) accL =
          (xs.foldl (fun acc j => acc + c[j] • M.row j) accR)[idxFin] := by
    intro xs
    induction xs with
    | nil =>
        intro accL accR hacc
        simp [hacc]
    | cons j rest ih =>
        intro accL accR hacc
        simp only [List.foldl_cons]
        apply ih
        change accL + M[j.val][idxFin.val] * c[j] =
          (accR + c[j] • M.row j)[idxFin.val]
        rw [Vector.getElem_add, Vector.getElem_smul, hacc]
        change accR[idx] + M[j.val][idx] * c[j] =
          accR[idx] + c[j] * M[j.val][idx]
        grind
  exact hfold (List.finRange n) 0 0 (by simp [Vector.getElem_zero])





























/-- `prefixSpan_zero` states that the zero vector is contained in every prefix span, providing the base case for prefix-span closure arguments. -/
 theorem _root_.Hex.GramSchmidt.prefixSpan_zero
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) :
    prefixSpan M i hi 0 := by
  let j : Fin (i + 1) := ⟨0, Nat.succ_pos i⟩
  have hz := _root_.Hex.GramSchmidt.prefixSpan_smul M i hi 0 (_root_.Hex.GramSchmidt.prefixSpan_row M i hi j)
  have hzero : (0 : Rat) • (prefixRows M i hi).row j = 0 := by
    apply Vector.ext
    intro idx hidx
    rw [Vector.getElem_smul, Vector.getElem_zero]
    change (0 : Rat) * ((prefixRows M i hi).row j)[idx] = 0
    grind
  simpa [hzero] using hz

/-- `prefixSpan_vecMul` states that any row combination of prefix rows already in another prefix span remains in that prefix span. -/
 theorem _root_.Hex.GramSchmidt.prefixSpan_vecMul
    (A B : Matrix Rat n m) (i : Nat) (hi : i < n) (c : Vector Rat (i + 1))
    (hrows : ∀ j : Fin (i + 1), prefixSpan B i hi ((prefixRows A i hi).row j)) :
    prefixSpan B i hi (Matrix.vecMul c (prefixRows A i hi)) := by
  rw [_root_.Hex.GramSchmidt.vecMul_eq_foldl_rows, Fin.foldl_eq_finRange_foldl]
  have hfold :
      ∀ xs : List (Fin (i + 1)), ∀ acc : Vector Rat m,
        prefixSpan B i hi acc →
          prefixSpan B i hi
            (xs.foldl
              (fun acc j => acc + c[j] • (prefixRows A i hi).row j) acc) := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc
        simpa using hacc
    | cons j rest ih =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih
        exact _root_.Hex.GramSchmidt.prefixSpan_add B i hi hacc
          (_root_.Hex.GramSchmidt.prefixSpan_smul B i hi c[j] (hrows j))
  exact hfold (List.finRange (i + 1)) 0 (_root_.Hex.GramSchmidt.prefixSpan_zero B i hi)

/-- `strictPrefixRows_succ_eq_prefixRows` identifies the strict prefix of length `i + 1` with the inclusive prefix through row `i`. -/
 theorem _root_.Hex.GramSchmidt.strictPrefixRows_succ_eq_prefixRows
    (M : Matrix Rat n m) (i : Nat) (hi : i + 1 < n) :
    _root_.Hex.GramSchmidt.strictPrefixRows M (i + 1) (Nat.le_of_lt hi) =
      prefixRows M i (Nat.lt_of_succ_lt hi) := by
  apply Hex.Matrix.ext
  apply Vector.ext
  intro row hrow
  apply Vector.ext
  intro col hcol
  rfl

/-- `prefixSpan_mono_succ` lifts prefix-span membership across one successor step in the prefix length. -/
 theorem _root_.Hex.GramSchmidt.prefixSpan_mono_succ
    (M : Matrix Rat n m) (i : Nat) (hi : i + 1 < n) {v : Vector Rat m}
    (hv : prefixSpan M i (Nat.lt_of_succ_lt hi) v) :
    prefixSpan M (i + 1) hi v := by
  rcases hv with ⟨c, hc⟩
  refine ⟨_root_.Hex.GramSchmidt.extendStrictPrefixCoeff c, ?_⟩
  rw [_root_.Hex.GramSchmidt.vecMul_prefixRows_extendStrictPrefixCoeff,
    _root_.Hex.GramSchmidt.strictPrefixRows_succ_eq_prefixRows (hi := hi)]
  exact hc

/-- `prefixSpan_mono_le` lifts prefix-span membership along any ordered pair of prefix indices. -/
 theorem _root_.Hex.GramSchmidt.prefixSpan_mono_le
    (M : Matrix Rat n m) {j i : Nat} (hj : j < n) (hi : i < n) (hji : j ≤ i)
    {v : Vector Rat m} (hv : prefixSpan M j hj v) :
    prefixSpan M i hi v := by
  induction hji with
  | refl =>
      exact hv
  | step hji ih =>
      exact _root_.Hex.GramSchmidt.prefixSpan_mono_succ M _ hi (ih (Nat.lt_of_succ_lt hi))

/-- `prefixSpan_matrix_row` records that each matrix row belongs to the prefix span ending at that row. -/
 theorem _root_.Hex.GramSchmidt.prefixSpan_matrix_row
    (M : Matrix Rat n m) (j : Fin n) :
    prefixSpan M j.val j.isLt (M.row j) := by
  let last : Fin (j.val + 1) := ⟨j.val, Nat.lt_succ_self j.val⟩
  simpa [prefixRows, Matrix.row] using _root_.Hex.GramSchmidt.prefixSpan_row M j.val j.isLt last





 theorem _root_.Hex.GramSchmidt.prefixSpan_strictPrefix_vecMul
    (M : Matrix Rat n m) (i : Nat) (hi : i < n) (c : Vector Rat i) :
    prefixSpan M i hi
      (Matrix.vecMul c (_root_.Hex.GramSchmidt.strictPrefixRows M i (Nat.le_of_lt hi))) := by
  cases i with
  | zero =>
      have hcomb :
          Matrix.vecMul c (_root_.Hex.GramSchmidt.strictPrefixRows M 0 (Nat.le_of_lt hi)) = 0 := by
        rw [_root_.Hex.GramSchmidt.vecMul_eq_foldl_rows]
        simp
      simpa [hcomb] using _root_.Hex.GramSchmidt.prefixSpan_zero M 0 hi
  | succ k =>
      have hk : k < n := Nat.lt_of_succ_lt hi
      rw [_root_.Hex.GramSchmidt.strictPrefixRows_succ_eq_prefixRows (M := M) (i := k) (hi := hi)]
      have hspan :
          prefixSpan M k hk
            (Matrix.vecMul c (prefixRows M k hk)) := by
        apply _root_.Hex.GramSchmidt.prefixSpan_vecMul
        intro row
        have hself :=
          _root_.Hex.GramSchmidt.prefixSpan_matrix_row M (⟨row.val, Nat.lt_trans row.isLt hi⟩ : Fin n)
        have hmono :=
          _root_.Hex.GramSchmidt.prefixSpan_mono_le M (Nat.lt_trans row.isLt hi) hk
            (Nat.le_of_lt_succ row.isLt) hself
        have htarget :
            M.row (⟨row.val, Nat.lt_trans row.isLt hi⟩ : Fin n) =
              (prefixRows M k hk).row row := by
          apply Vector.ext
          intro col hcol
          simp [prefixRows, Matrix.row]
        rw [htarget] at hmono
        exact hmono
      exact _root_.Hex.GramSchmidt.prefixSpan_mono_succ M k hi hspan

 theorem _root_.Hex.GramSchmidt.prefixSpan_strictRowCombination
    (A B : Matrix Rat n m) (i : Nat) (hi : i < n) (c : Vector Rat i)
    (hrows : ∀ j : Fin i,
      prefixSpan B i hi ((_root_.Hex.GramSchmidt.strictPrefixRows A i (Nat.le_of_lt hi)).row j)) :
    prefixSpan B i hi
      (Matrix.vecMul c (_root_.Hex.GramSchmidt.strictPrefixRows A i (Nat.le_of_lt hi))) := by
  rw [_root_.Hex.GramSchmidt.vecMul_eq_foldl_rows, Fin.foldl_eq_finRange_foldl]
  have hfold :
      ∀ xs : List (Fin i), ∀ acc : Vector Rat m,
        prefixSpan B i hi acc →
          prefixSpan B i hi
            (xs.foldl
              (fun acc j => acc + c[j] • (_root_.Hex.GramSchmidt.strictPrefixRows A i (Nat.le_of_lt hi)).row j)
              acc) := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc
        simpa using hacc
    | cons j rest ih =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih
        exact _root_.Hex.GramSchmidt.prefixSpan_add B i hi hacc
          (_root_.Hex.GramSchmidt.prefixSpan_smul B i hi c[j] (hrows j))
  exact hfold (List.finRange i) 0 (_root_.Hex.GramSchmidt.prefixSpan_zero B i hi)

 theorem _root_.Hex.GramSchmidt.foldl_projectionCoeff_vecMul_comm
    (xs : List (Fin k)) (row : Vector Rat m) (basis : Matrix Rat n m)
    (hk : k ≤ n) (idx : Fin m) (acc : Rat) :
    xs.foldl
        (fun acc j =>
          acc +
            (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx] *
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩))
        acc =
      xs.foldl
        (fun acc j =>
          acc +
            projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
              (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx])
        acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons j rest ih =>
      simp only [List.foldl_cons]
      have hcomm :
          (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx] *
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) =
            projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
              (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx] := by
        grind
      rw [hcomm]
      exact ih (acc := acc +
        projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
          (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx])

 theorem _root_.Hex.GramSchmidt.foldl_projectionCombination_getElem
    (xs : List (Fin k)) (row : Vector Rat m) (basis : Matrix Rat n m)
    (hk : k ≤ n) (idx : Fin m) (acc : Vector Rat m) :
    (xs.foldl
        (fun acc j =>
          acc + projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) •
            basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)
        acc)[idx] =
      xs.foldl
        (fun acc j =>
          acc +
            projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
              (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx])
        acc[idx] := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons j rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      have hstart :
          (acc +
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) •
                basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx] =
            acc[idx] +
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
                (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx] := by
        change
          (acc +
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) •
                basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx.val] =
            acc[idx.val] +
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
                (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idx.val]
        rw [Vector.getElem_add, Vector.getElem_smul]
        rfl
      rw [hstart]

/-- `prefixSumByRow` is an executable row combination of the first `k` rows of
the basis matrix. -/
 theorem _root_.Hex.GramSchmidt.vecMul_strictPrefixRows_projectionCoeffVector
    (row : Vector Rat m) (basis : Matrix Rat n m) (k : Nat) (hk : k ≤ n) :
    Matrix.vecMul (_root_.Hex.GramSchmidt.projectionCoeffVector row basis k hk) (_root_.Hex.GramSchmidt.strictPrefixRows basis k hk) =
      _root_.Hex.GramSchmidt.prefixSumByRow row basis k hk := by
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change
    (Matrix.mulVec (Matrix.transpose (_root_.Hex.GramSchmidt.strictPrefixRows basis k hk))
        (_root_.Hex.GramSchmidt.projectionCoeffVector row basis k hk))[idxFin] =
      (_root_.Hex.GramSchmidt.prefixSumByRow row basis k hk)[idxFin]
  rw [show
      (Matrix.mulVec (Matrix.transpose (_root_.Hex.GramSchmidt.strictPrefixRows basis k hk))
          (_root_.Hex.GramSchmidt.projectionCoeffVector row basis k hk))[idxFin] =
        (List.finRange k).foldl
          (fun acc j =>
            acc +
              (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idxFin] *
                projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩))
          0 by
        unfold Matrix.mulVec Vector.dotProduct _root_.Hex.GramSchmidt.strictPrefixRows _root_.Hex.GramSchmidt.projectionCoeffVector
        simp [Matrix.col]]
  rw [show
      (_root_.Hex.GramSchmidt.prefixSumByRow row basis k hk)[idxFin] =
        (List.finRange k).foldl
          (fun acc j =>
            acc +
              projectionCoeff row (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) *
                (basis.row ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩)[idxFin])
          0 by
        unfold _root_.Hex.GramSchmidt.prefixSumByRow
        rw [Fin.foldl_eq_finRange_foldl]
        simpa [Vector.getElem_zero] using
          _root_.Hex.GramSchmidt.foldl_projectionCombination_getElem
            (xs := List.finRange k) (row := row) (basis := basis) (hk := hk)
            (idx := idxFin) (acc := 0)]
  simpa [Matrix.row] using _root_.Hex.GramSchmidt.foldl_projectionCoeff_vecMul_comm
    (xs := List.finRange k) (row := row) (basis := basis) (hk := hk)
    (idx := idxFin) (acc := 0)

/-- The recursive shape of `prefixSumByRow`: pulling off the last index. -/
 theorem _root_.Hex.GramSchmidt.prefixSumByRow_succ
    (row : Vector Rat m) (basis : Matrix Rat n m) (k : Nat) (hk : k + 1 ≤ n) :
    _root_.Hex.GramSchmidt.prefixSumByRow row basis (k + 1) hk =
      _root_.Hex.GramSchmidt.prefixSumByRow row basis k (Nat.le_of_succ_le hk) +
        projectionCoeff row (basis.row ⟨k, Nat.lt_of_succ_le hk⟩) •
          basis.row ⟨k, Nat.lt_of_succ_le hk⟩ := by
  unfold _root_.Hex.GramSchmidt.prefixSumByRow
  rw [Fin.foldl_eq_finRange_foldl, Fin.foldl_eq_finRange_foldl,
    List.finRange_succ_last, List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  rfl

/-- `prefixCombination` over `coeffMatrix b (basisMatrix b)` agrees with
`prefixSumByRow` taking row `b.row ⟨i, hi⟩`. -/
 theorem _root_.Hex.GramSchmidt.prefixCombination_eq_prefixSumByRow
    (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    prefixCombination (coeffMatrix b (basisMatrix b)) (basisMatrix b) i hi =
      _root_.Hex.GramSchmidt.prefixSumByRow (b.row ⟨i, hi⟩) (basisMatrix b) i (Nat.le_of_lt hi) := by
  unfold prefixCombination _root_.Hex.GramSchmidt.prefixSumByRow
  congr 1
  funext acc j
  show acc + entry (coeffMatrix b (basisMatrix b)) ⟨i, hi⟩
        ⟨j.val, Nat.lt_trans j.isLt hi⟩ • (basisMatrix b).row ⟨j.val, _⟩ =
      acc + projectionCoeff (b.row ⟨i, hi⟩)
        ((basisMatrix b).row ⟨j.val, _⟩) • (basisMatrix b).row ⟨j.val, _⟩
  have hjlt : j.val < i := j.isLt
  have hentry : entry (coeffMatrix b (basisMatrix b)) ⟨i, hi⟩
        ⟨j.val, Nat.lt_trans j.isLt hi⟩ =
      projectionCoeff (b.row ⟨i, hi⟩)
        ((basisMatrix b).row ⟨j.val, Nat.lt_trans j.isLt hi⟩) := by
    simp [coeffMatrix, _root_.Hex.GramSchmidt.entry_ofFn, hjlt, Matrix.row]
  rw [hentry]

/-- `prefixSumByRow` with row free equals `projectionCombination` over the
first `i` rows of `basisRows b.rows.toList`. -/
 theorem _root_.Hex.GramSchmidt.prefixSumByRow_eq_projectionCombination
    (b : Matrix Rat n m) (row : Vector Rat m) (i : Nat) (hi : i ≤ n) :
    _root_.Hex.GramSchmidt.prefixSumByRow row (basisMatrix b) i hi =
      _root_.Hex.GramSchmidt.projectionCombination row ((basisRows b.rows.toList).take i) 0 := by
  have hlen : (basisRows b.rows.toList).length = n := by simp [_root_.Hex.GramSchmidt.basisRows_length]
  induction i with
  | zero =>
      simp [_root_.Hex.GramSchmidt.prefixSumByRow, _root_.Hex.GramSchmidt.projectionCombination]
  | succ k ih =>
      have hk_lt : k < n := Nat.lt_of_succ_le hi
      have hkrows : k < (basisRows b.rows.toList).length := by rw [hlen]; exact hk_lt
      rw [_root_.Hex.GramSchmidt.prefixSumByRow_succ, ih (Nat.le_of_succ_le hi)]
      have htake : (basisRows b.rows.toList).take (k + 1) =
          (basisRows b.rows.toList).take k ++ [(basisRows b.rows.toList)[k]!] := by
        rw [List.take_succ_eq_append_getElem hkrows]
        congr 1
        simp [List.getElem!_eq_getElem?_getD,
          List.getElem?_eq_getElem hkrows]
      rw [htake, _root_.Hex.GramSchmidt.projectionCombination_append, _root_.Hex.GramSchmidt.projectionCombination_singleton]
      have hbasisrow : (basisMatrix b).row ⟨k, hk_lt⟩ = (basisRows b.rows.toList)[k]! := by
        rw [_root_.Hex.GramSchmidt.basisMatrix_row_eq_basisRows_get!]
      rw [hbasisrow]

/-- The coefficient-matrix prefix term is an executable row combination of the
earlier generated basis rows. -/
 theorem _root_.Hex.GramSchmidt.prefixCombination_eq_strictPrefixRowCombination
    (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    prefixCombination (coeffMatrix b (basisMatrix b)) (basisMatrix b) i hi =
      Matrix.vecMul (_root_.Hex.GramSchmidt.projectionCoeffVector (b.row ⟨i, hi⟩) (basisMatrix b) i (Nat.le_of_lt hi)) (_root_.Hex.GramSchmidt.strictPrefixRows (basisMatrix b) i (Nat.le_of_lt hi)) := by
  rw [_root_.Hex.GramSchmidt.prefixCombination_eq_prefixSumByRow]
  exact (_root_.Hex.GramSchmidt.vecMul_strictPrefixRows_projectionCoeffVector
    (row := b.row ⟨i, hi⟩) (basis := basisMatrix b) (k := i)
    (hk := Nat.le_of_lt hi)).symm

/-- Decomposition invariant: each input row equals its reduced basis row plus
the prefix combination of earlier basis rows weighted by `coeffMatrix`. -/
 theorem _root_.Hex.GramSchmidt.basisMatrix_reconstruction_invariant
    (b : Matrix Rat n m) (i : Nat) (hi : i < n) :
    b.row ⟨i, hi⟩ =
      (basisMatrix b).row ⟨i, hi⟩ +
        prefixCombination (coeffMatrix b (basisMatrix b)) (basisMatrix b) i hi := by
  have hilen : i < b.rows.toList.length := by simpa using hi
  have htoList_get : b.rows.toList[i]! = b.row ⟨i, hi⟩ := by
    simp [Matrix.row, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem hilen, Vector.getElem_toList, Hex.Matrix.getRow]
  have hreduce_forward :=
    _root_.Hex.GramSchmidt.basisRows_get!_eq_reduceAgainstBasis_forward
      (rows := b.rows.toList) (k := i) hilen
  rw [htoList_get] at hreduce_forward
  rw [hreduce_forward, ← _root_.Hex.GramSchmidt.basisMatrix_row_eq_basisRows_get! b i hi]
  congr 1
  rw [_root_.Hex.GramSchmidt.prefixCombination_eq_prefixSumByRow,
    _root_.Hex.GramSchmidt.prefixSumByRow_eq_projectionCombination]

end GramSchmidt
end Hex

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end


