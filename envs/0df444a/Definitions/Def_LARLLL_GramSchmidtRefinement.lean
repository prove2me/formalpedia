-- Prove2me | Definitions.Def_LARLLL_GramSchmidtRefinement
-- name    : LARLLL_GramSchmidtRefinement
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T02:46:27.291359+00:00
-- url     : https://prove2.me/theorems/03f7e1e4-593e-42e1-80a0-a5dd8f6da34d
-- title:
--   Checked fraction-free Gram-Schmidt refinement foundations
-- statement:
--   The original Bareiss and Gram-Schmidt refinement data and their proof-carrying auxiliary invariants used to connect the concrete integer LLL state to rational orthogonalization.
-- source:
--   Apache-2.0 leanprover/hex source and the already checked native LLL adapters. Exact original module locations and SHA-256 values are recorded in the validation receipt. Whole original declaration commands were retained using the official Lean declaration/sketch and structural syntax oracles, with original notices, checked computational definitions, and csimp proof logic preserved. All retained declaration types and safe non-theorem values were compared to the original environment using kernel-checked reflexivity after expanding safe generated implementation helpers. Source SHA-256: f5095a3d8b343d6a3eca95a915fc474e873f84892da6c31870e2bed303981673.

import Definitions.Def_LARLLL_KernelTransport

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/






set_option autoImplicit true



section

/-!
No-pivot Bareiss loop invariant for `hex-matrix-theory`.

This module proves the recursive bordered-minor invariant of the no-pivot
Bareiss recurrence: after `k` regular Bareiss steps, the trailing entries of
the working matrix agree with the corresponding bordered-minor determinants of
the source matrix, and the previous pivot agrees with the determinant of the
leading prefix of size `k`. As an immediate corollary, when all leading-prefix
determinants are nonzero (`NonzeroBareissPivots`), the loop never takes the
singular branch.

The invariant proof composes the bordered-minor `stepMatrix` update lemma
(`Hex.Matrix.stepMatrixWith_borderedMinor_update`) with the bordered-minor
specialization of Desnanot-Jacobi (`desnanot_jacobi_borderedMinor` in the
parent module) and the exact-division equation
(`bareissExactDiv_borderedMinor_of_mul_eq`).
-/

namespace HexMatrixTheory

universe u

variable {R : Type u} [CommRing R] [DecidableEq R] {n : Nat}
variable {quot : R → R → R}
variable {hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a}

/-- An exact quotient makes a nontrivial commutative ring an integral domain. -/
theorem isDomain_of_quot (quot : R → R → R)
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (h1 : (1 : R) ≠ 0) : IsDomain R := by
  let _ : Div R := ⟨quot⟩
  have _ : Hex.ExactDivLaws R := ⟨hquot⟩
  let _ : Nontrivial R := ⟨⟨1, 0, h1⟩⟩
  let _ : NoZeroDivisors R := ⟨by
    intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    by_cases hb : b = 0
    · exact Or.inr hb
    exact (Hex.ExactDivLaws.mul_ne_zero ha hb hab).elim⟩
  exact NoZeroDivisors.to_isDomain R

/-- The `k`-bordered minor of `M` at the corner row/column `⟨k, hk⟩` is exactly
the `(k + 1)`-leading prefix of `M`. This identifies the trailing-corner entry
under the no-pivot Bareiss invariant with a leading-prefix determinant. -/
theorem borderedMinor_corner_eq_principalSubmatrix {R : Type u}
    (M : Hex.Matrix R n n) (k : Nat) (hk : k < n) :
    Hex.Matrix.borderedMinor M k hk ⟨k, hk⟩ ⟨k, hk⟩ =
      Hex.Matrix.principalSubmatrix M (k + 1) (Nat.succ_le_of_lt hk) := by
  apply Hex.Matrix.ext_getElem
  intro r c
  rw [Hex.Matrix.getElem_principalSubmatrix]
  simp only [Hex.Matrix.borderedMinor]
  rw [Hex.Matrix.getElem_ofFn]
  simp only [Hex.Matrix.getElem_pair_eq_nested]
  have hr1 := r.isLt
  have hc1 := c.isLt
  have hrr : (if hr : r.val < k then (⟨r.val, Nat.lt_trans hr hk⟩ : Fin n) else ⟨k, hk⟩) =
      (⟨r.val, Nat.lt_of_lt_of_le r.isLt (Nat.succ_le_of_lt hk)⟩ : Fin n) := by
    split
    · rfl
    · simp only [Fin.mk.injEq]; omega
  have hcc : (if hc : c.val < k then (⟨c.val, Nat.lt_trans hc hk⟩ : Fin n) else ⟨k, hk⟩) =
      (⟨c.val, Nat.lt_of_lt_of_le c.isLt (Nat.succ_le_of_lt hk)⟩ : Fin n) := by
    split
    · rfl
    · simp only [Fin.mk.injEq]; omega
  rw [hrr, hcc]



/-- Bordered-minor invariant of the no-pivot Bareiss recurrence:
- `singularStep` is `none` (no pivot has been zero yet);
- the previous pivot equals the determinant of the leading prefix of size
  `state.step` (which is `1` for `state.step = 0`);
- the previous pivot is nonzero (so the next step's exact division is valid);
- every trailing entry `(i, j)` with `state.step ≤ i.val` and
  `state.step ≤ j.val` agrees with the determinant of the
  `state.step`-bordered minor with trailing row `i` and column `j`.

The implication on diagonal entries (`state.matrix[k][k]` agrees with the
leading-prefix determinant of size `k + 1`) follows from `trailing_eq` taken
at `i = j = ⟨k, _⟩` together with `borderedMinor_corner_eq_principalSubmatrix`. -/
structure BareissNoPivotInvariant
    (source : Hex.Matrix R n n) (state : Hex.Matrix.BareissState R n) : Prop where
  singular_none : state.singularStep = none
  step_le : state.step ≤ n
  prevPivot_eq :
    state.prevPivot =
      Hex.Matrix.det (Hex.Matrix.principalSubmatrix source state.step step_le)
  prevPivot_ne : state.prevPivot ≠ 0
  trailing_eq :
    ∀ (h : state.step < n) (i j : Fin n)
        (_ : state.step ≤ i.val) (_ : state.step ≤ j.val),
      state.matrix[i][j] =
        Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step h i j)

/-- The initial Bareiss no-pivot state satisfies the bordered-minor invariant:
the matrix is the source itself, and the previous-pivot convention is
`det (principalSubmatrix _ 0 _) = 1`. -/
theorem bareissNoPivotInvariant_initialWith {R : Type u} [CommRing R]
    (M : Hex.Matrix R n n) (h1 : (1 : R) ≠ 0) :
    BareissNoPivotInvariant M (Hex.Matrix.noPivotInitialState M) where
  singular_none := rfl
  step_le := Nat.zero_le _
  prevPivot_eq := by
    show (1 : R) = Hex.Matrix.det (Hex.Matrix.principalSubmatrix M 0 (Nat.zero_le n))
    simp
  prevPivot_ne := by
    show (1 : R) ≠ 0
    exact h1
  trailing_eq := by
    intro h i j _hi _hj
    have h0 : 0 < n := by omega
    -- For `state.step = 0`, the bordered minor is the `1 × 1` block with the
    -- single entry `M[i][j]`.
    show M[i][j] = Hex.Matrix.det (Hex.Matrix.borderedMinor M 0 h0 i j)
    rw [Hex.Matrix.det_one_by_one]
    show M[i][j] =
        (Hex.Matrix.borderedMinor M 0 h0 i j)[(Fin.last 0)][(Fin.last 0)]
    rw [Hex.Matrix.borderedMinor_entry_last_last]

/-- Integer compatibility form of `bareissNoPivotInvariant_initialWith`. -/
theorem bareissNoPivotInvariant_initial (M : Hex.Matrix Int n n) :
    BareissNoPivotInvariant M (Hex.Matrix.noPivotInitialState M) :=
  bareissNoPivotInvariant_initialWith M (by omega)

/-- One regular no-pivot Bareiss step preserves the bordered-minor invariant.
Given a state satisfying the invariant with `state.step + 1 < n` and a nonzero
diagonal pivot, the state produced by one `noPivotLoop` iteration also
satisfies the invariant. -/
 theorem _root_.HexMatrixTheory.bareissNoPivotInvariant_step
    {R : Type u} [CommRing R]
    (quot : R → R → R)
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (source : Hex.Matrix R n n) (state : Hex.Matrix.BareissState R n)
    (hinv : BareissNoPivotInvariant source state)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] ≠ 0) :
    BareissNoPivotInvariant source
      { step := state.step + 1
        matrix := Hex.Matrix.stepMatrixWith quot state.matrix state.step
          (state.matrix[(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
            (⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)]) state.prevPivot
        prevPivot := state.matrix[(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
          (⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)]
        rowSwaps := state.rowSwaps
        singularStep := none } where
  singular_none := rfl
  step_le := Nat.le_of_lt hDone
  prevPivot_eq := by
    -- Pivot at step k equals det (principalSubmatrix source (k + 1) _), via
    -- trailing_eq @ (i = j = ⟨k, _⟩) and borderedMinor_corner_eq_principalSubmatrix.
    have hk : state.step < n := Nat.lt_of_succ_lt hDone
    have hkk :
        state.matrix[(⟨state.step, hk⟩ : Fin n)][(⟨state.step, hk⟩ : Fin n)] =
          Hex.Matrix.det
            (Hex.Matrix.borderedMinor source state.step hk
              (⟨state.step, hk⟩ : Fin n) (⟨state.step, hk⟩ : Fin n)) :=
      hinv.trailing_eq hk ⟨state.step, hk⟩ ⟨state.step, hk⟩
        (Nat.le_refl _) (Nat.le_refl _)
    show state.matrix[(⟨state.step, hk⟩ : Fin n)][(⟨state.step, hk⟩ : Fin n)] = _
    rw [hkk, borderedMinor_corner_eq_principalSubmatrix source state.step hk]
  prevPivot_ne := hp
  trailing_eq := by
    intro hnext i j hi hj
    -- Unfold the structure projection so omega can see through it.
    change state.step + 1 ≤ i.val at hi
    change state.step + 1 ≤ j.val at hj
    have hk : state.step < n := Nat.lt_of_succ_lt hDone
    have hi' : state.step < i.val := hi
    have hj' : state.step < j.val := hj
    -- The pivot for the borderedMinor update is the `(k, k)` entry of
    -- `state.matrix`, which by `trailing_eq` equals
    -- `det (borderedMinor source state.step _ ⟨k, _⟩ ⟨k, _⟩)`.
    have hpivot_eq :
        state.matrix[(⟨state.step, hk⟩ : Fin n)][(⟨state.step, hk⟩ : Fin n)] =
          Hex.Matrix.det
            (Hex.Matrix.borderedMinor source state.step hk
              (⟨state.step, Nat.lt_trans hj' j.isLt⟩ : Fin n)
              (⟨state.step, Nat.lt_trans hi' i.isLt⟩ : Fin n)) :=
      hinv.trailing_eq hk ⟨state.step, hk⟩ ⟨state.step, hk⟩
        (Nat.le_refl _) (Nat.le_refl _)
    -- `current[i][j]` agrees with the bordered minor at (i, j), via trailing_eq.
    have hentry :
        state.matrix[i][j] =
          Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step hk i j) :=
      hinv.trailing_eq hk i j (Nat.le_of_lt hi') (Nat.le_of_lt hj')
    -- `current[i][⟨k, _⟩]` agrees with the bordered minor at (i, ⟨k, _⟩).
    have hleft :
        state.matrix[i][(⟨state.step, Nat.lt_trans hi' i.isLt⟩ : Fin n)] =
          Hex.Matrix.det
            (Hex.Matrix.borderedMinor source state.step hk i
              (⟨state.step, Nat.lt_trans hi' i.isLt⟩ : Fin n)) :=
      hinv.trailing_eq hk i ⟨state.step, Nat.lt_trans hi' i.isLt⟩
        (Nat.le_of_lt hi') (Nat.le_refl _)
    -- `current[⟨k, _⟩][j]` agrees with the bordered minor at (⟨k, _⟩, j).
    have htop :
        state.matrix[(⟨state.step, Nat.lt_trans hj' j.isLt⟩ : Fin n)][j] =
          Hex.Matrix.det
            (Hex.Matrix.borderedMinor source state.step hk
              (⟨state.step, Nat.lt_trans hj' j.isLt⟩ : Fin n) j) :=
      hinv.trailing_eq hk ⟨state.step, Nat.lt_trans hj' j.isLt⟩ j
        (Nat.le_refl _) (Nat.le_of_lt hj')
    -- Desnanot-Jacobi gives the exact-division premise.
    have hdesnanot :
        Hex.Matrix.det (Hex.Matrix.borderedMinor source (state.step + 1) hnext i j) *
            state.prevPivot =
          Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step hk
              (⟨state.step, Nat.lt_trans hj' j.isLt⟩ : Fin n)
              (⟨state.step, Nat.lt_trans hi' i.isLt⟩ : Fin n)) *
            Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step hk i j) -
            Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step hk
              i (⟨state.step, Nat.lt_trans hi' i.isLt⟩ : Fin n)) *
            Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step hk
              (⟨state.step, Nat.lt_trans hj' j.isLt⟩ : Fin n) j) := by
      rw [hinv.prevPivot_eq]
      exact desnanot_jacobi_borderedMinor source state.step hk hnext i j hi' hj'
    have hexact :
        quot
            (Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step hk
              (⟨state.step, Nat.lt_trans hj' j.isLt⟩ : Fin n)
              (⟨state.step, Nat.lt_trans hi' i.isLt⟩ : Fin n)) *
              Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step hk i j) -
              Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step hk
                i (⟨state.step, Nat.lt_trans hi' i.isLt⟩ : Fin n)) *
              Hex.Matrix.det (Hex.Matrix.borderedMinor source state.step hk
                (⟨state.step, Nat.lt_trans hj' j.isLt⟩ : Fin n) j))
            state.prevPivot =
          Hex.Matrix.det (Hex.Matrix.borderedMinor source (state.step + 1) hnext i j) :=
      Hex.Matrix.exactQuot_borderedMinor_of_mul_eq quot hquot source state.step hk hnext i j
        hi' hj' state.prevPivot hinv.prevPivot_ne hdesnanot
    -- Apply `stepMatrix_borderedMinor_update` to obtain the updated entry.
    show (Hex.Matrix.stepMatrixWith quot state.matrix state.step
        (state.matrix[(⟨state.step, hk⟩ : Fin n)][(⟨state.step, hk⟩ : Fin n)])
        state.prevPivot)[i][j] =
      Hex.Matrix.det (Hex.Matrix.borderedMinor source (state.step + 1) hnext i j)
    exact Hex.Matrix.stepMatrixWith_borderedMinor_update quot source state.matrix
      state.step hk hnext i j hi' hj'
      (state.matrix[(⟨state.step, hk⟩ : Fin n)][(⟨state.step, hk⟩ : Fin n)])
      state.prevPivot hpivot_eq hentry hleft htop hexact





























/-- Sign contributed by the row swaps recorded in a Bareiss state. -/
@[expose]
def bareissStateSign (state : Hex.Matrix.BareissState R n) : R :=
  if state.rowSwaps % 2 = 0 then 1 else -1

/-- Row-pivoted Bareiss invariant. The current working state is interpreted as
a no-pivot Bareiss state for a logical source obtained from the original source
by the row swaps already performed; the sign field records the determinant
relation back to the original source. -/
@[expose]
def BareissPivotInvariant
    (source : Hex.Matrix R n n) (state : Hex.Matrix.BareissState R n) : Prop :=
  ∃ logicalSource : Hex.Matrix R n n,
    Hex.Matrix.det source = bareissStateSign state * Hex.Matrix.det logicalSource ∧
      BareissNoPivotInvariant logicalSource state





















/-- Outcome-driven companion of `noPivotLoop_invariant`: if the no-pivot
Bareiss loop run from a valid invariant state does NOT record a singular step
during its `fuel` iterations, the invariant continues to hold afterward. The
non-singular outcome guarantees every visited pivot was nonzero, which is the
hypothesis the inductive step needs.

This is the no-pivot analog of `pivotLoop_invariant_of_singularStep_eq_none`. -/
theorem noPivotLoopWith_invariant_of_singularStep_eq_none
    (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (source : Hex.Matrix R n n)
    (fuel : Nat) (state : Hex.Matrix.BareissState R n)
    (hinv : BareissNoPivotInvariant source state)
    (hregular : (Hex.Matrix.noPivotLoopWith quot fuel state).singularStep = none) :
    BareissNoPivotInvariant source (Hex.Matrix.noPivotLoopWith quot fuel state) := by
  induction fuel generalizing state with
  | zero =>
      simpa only [Hex.Matrix.noPivotLoopWith_zero_fuel (quot := quot)] using hinv
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp0 :
            state.matrix[(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
              (⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0
        · rw [Hex.Matrix.noPivotLoopWith_of_singular (quot := quot) fuel state hDone hp0] at hregular
          simp at hregular
        · rw [Hex.Matrix.noPivotLoopWith_of_regular (quot := quot) fuel state hDone hp0]
          apply ih
          · exact _root_.HexMatrixTheory.bareissNoPivotInvariant_step quot hquot source state hinv hDone hp0
          · simpa [Hex.Matrix.noPivotLoopWith_of_regular (quot := quot) fuel state hDone hp0]
              using hregular
      · simpa [Hex.Matrix.noPivotLoopWith_done (quot := quot) fuel state hDone] using hinv

/-- Integer compatibility form of
`noPivotLoopWith_invariant_of_singularStep_eq_none`. -/
theorem noPivotLoop_invariant_of_singularStep_eq_none
    (source : Hex.Matrix Int n n)
    (fuel : Nat) (state : Hex.Matrix.BareissState Int n)
    (hinv : BareissNoPivotInvariant source state)
    (hregular : (Hex.Matrix.noPivotLoop fuel state).singularStep = none) :
    BareissNoPivotInvariant source (Hex.Matrix.noPivotLoop fuel state) :=
  noPivotLoopWith_invariant_of_singularStep_eq_none Int.mul_ediv_cancel
    source fuel state hinv hregular















/-! # Failed Bareiss column dependence

Helper for the row-pivoted singular Bareiss branch: if the pivot search at
level `k` fails (the entire `k`-bordered trailing column is zero) and the
preceding leading-prefix determinant is nonzero, then there is an explicit
linear combination of the columns of `source` — with coefficients given by the
signed `k × k` cofactors of the leading prefix augmented with column `k` —
that vanishes at every row. The coefficient on column `k` is
`Hex.Matrix.det (Hex.Matrix.principalSubmatrix source k _)`, which is nonzero by
hypothesis. -/

/-- The `k × (k+1)` top block used to define the failed-pivot column
dependence: leading `k` rows of `source`, restricted to columns `0..k-1`
followed by column `k`. -/
@[expose]
def failedBareissTopBlock
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) :
    Matrix (Fin k) (Fin (k + 1)) R :=
  fun s c =>
    if hc : c.val < k then
      matrixEquiv source (⟨s.val, Nat.lt_trans s.isLt hk⟩ : Fin n)
        (⟨c.val, Nat.lt_trans hc hk⟩ : Fin n)
    else
      matrixEquiv source (⟨s.val, Nat.lt_trans s.isLt hk⟩ : Fin n) ⟨k, hk⟩

/-- Coefficient function for the failed-pivot column dependence. The value at
`c` is `(-1)^(k + c.val) * det(failedBareissTopBlock with column c removed)` for
`c.val ≤ k` and `0` otherwise. The coefficient on column `k` is
`det (principalSubmatrix source k _)`; see `failedBareissColumn_at_pivot`. -/
@[expose]
noncomputable def failedBareissColumn
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) :
    Fin n → R :=
  fun c =>
    if hc : c.val ≤ k then
      (-1) ^ (k + c.val) *
        Matrix.det
          ((failedBareissTopBlock source k hk).submatrix id
            (⟨c.val, Nat.lt_succ_of_le hc⟩ : Fin (k + 1)).succAbove)
    else 0





















































end HexMatrixTheory

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
Mathlib-side determinantal theory for the integer Gram-Schmidt surface of
`hex-gram-schmidt`.

This module relates the executable leading integer Gram determinant `gramDet`
to products of squared norms of the orthogonal Gram-Schmidt basis rows.  Its
spine is a rational column-operation reduction from `leadingGramMatrixInt`
(via the interpolating `progressMatrix`, the triangular `auxMatrix`, and the
`Int → Rat` cast law `det_intCast`) to the diagonal norm-squared matrix,
giving `gramDet_succ_rat` and `leadingGramMatrixInt_det_nonneg`.  Along the
way it builds the Cramer machinery (`scaledCoeffMatrix` solved through the
chosen `originalProjectionCoords`) that the sibling module uses to read off
the Gram-Schmidt coefficients `coeffs`.
-/

namespace Hex
namespace GramSchmidt
namespace Int







/-! # Gram determinant as a squared-norm product

The remaining theorems below build the rational column-operation reduction
from the leading Gram matrix to the diagonal Gram-Schmidt norm-squared
matrix, plus the integer→rational cast law for `det`. -/







/-- The cast of an Int matrix to a Rat matrix by entry-wise Int.cast. -/
 def _root_.Hex.GramSchmidt.Int.castIntDetMatrix {k : Nat} (M : Matrix Int k k) : Matrix Rat k k :=
  Matrix.ofFn fun i j => ((M[(i, j)] : Int) : Rat)



























/-- Cast an Int matrix row to a Rat row by entry-wise `Int.cast`. -/
 def _root_.Hex.GramSchmidt.Int.castIntRow (b : Matrix Int n m) (i : Fin n) : Vector Rat m :=
  Vector.map (fun x : Int => (x : Rat)) (b.row i)

/-- Cast an Int matrix to the Rat matrix whose rows are `castIntRow`. -/
 def _root_.Hex.GramSchmidt.Int.castIntMatrixRat (b : Matrix Int n m) : Matrix Rat n m :=
  Hex.Matrix.ofRows (b.rows.map (fun row => row.map (fun x : Int => (x : Rat))))





/-- Coefficients of the projection of row `i` onto the Gram-Schmidt prefix
`0, ..., j`, indexed by that prefix. -/
 noncomputable def _root_.Hex.GramSchmidt.Int.projectionCoeffPrefix
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    Vector Rat (j + 1) :=
  Vector.ofFn fun q =>
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩
      ⟨q.val, Nat.lt_of_lt_of_le q.isLt (Nat.succ_le_of_lt hj)⟩

/-- The Gram-Schmidt prefix projection of row `i` onto rows `0, ..., j`, still
written in the orthogonal basis rows. -/
 noncomputable def _root_.Hex.GramSchmidt.Int.basisPrefixProjection
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    Vector Rat m :=
  Matrix.vecMul (_root_.Hex.GramSchmidt.Int.projectionCoeffPrefix b i j hi hj) (GramSchmidt.prefixRows (basis b) j hj)

 theorem _root_.Hex.GramSchmidt.Int.basisPrefixProjection_mem_basisSpan
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    GramSchmidt.prefixSpan (basis b) j hj
      (_root_.Hex.GramSchmidt.Int.basisPrefixProjection b i j hi hj) := by
  exact ⟨_root_.Hex.GramSchmidt.Int.projectionCoeffPrefix b i j hi hj, rfl⟩

 theorem _root_.Hex.GramSchmidt.Int.basisPrefixProjection_mem_originalSpan
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    GramSchmidt.prefixSpan (_root_.Hex.GramSchmidt.Int.castIntMatrixRat b) j hj
      (_root_.Hex.GramSchmidt.Int.basisPrefixProjection b i j hi hj) := by
  have key := ((basis_span b j hj (_root_.Hex.GramSchmidt.Int.basisPrefixProjection b i j hi hj)).mp
      (_root_.Hex.GramSchmidt.Int.basisPrefixProjection_mem_basisSpan b i j hi hj))
  simp only [_root_.Hex.GramSchmidt.Int.castIntMatrixRat, Hex.GramSchmidt.castIntMatrix] at key ⊢
  exact key

/-- Original-row coordinates for the projection of row `i` onto the row prefix
`0, ..., j`. The coordinates are chosen through the proved span equivalence
between original rows and Gram-Schmidt rows. -/
 noncomputable def _root_.Hex.GramSchmidt.Int.originalProjectionCoords
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    Vector Rat (j + 1) :=
  Classical.choose (_root_.Hex.GramSchmidt.Int.basisPrefixProjection_mem_originalSpan b i j hi hj)









/-- Auxiliary matrix `M_final` whose `(i, j)` entry is the rational inner
product `⟨b_i, b*_j⟩` between the cast integer row `b_i` and the
Gram-Schmidt orthogonal basis row `b*_j`. -/
 noncomputable def _root_.Hex.GramSchmidt.Int.auxMatrix (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) :
    Matrix Rat k k :=
  Matrix.ofFn fun i j =>
    (_root_.Hex.GramSchmidt.Int.castIntRow b (GramSchmidt.liftFinLE i hk)).dotProduct
      ((basis b).row (GramSchmidt.liftFinLE j hk))











/-- Interpolating matrix between `leadingGramMatrixRat (castIntMatrix b)` (at
`s = 0`) and `auxMatrix b k hk` (at `s = k`). Columns with index `< s` have
already been replaced by basis-row dot products; columns with index `≥ s`
still hold the original `b`-row dot products. -/
 noncomputable def _root_.Hex.GramSchmidt.Int.progressMatrix (b : Matrix Int n m) (k : Nat)
    (hk : k ≤ n) (s : Nat) : Matrix Rat k k :=
  Matrix.ofFn fun i j =>
    if j.val < s then
      (_root_.Hex.GramSchmidt.Int.castIntRow b (GramSchmidt.liftFinLE i hk)).dotProduct
        ((basis b).row (GramSchmidt.liftFinLE j hk))
    else
      (_root_.Hex.GramSchmidt.Int.castIntRow b (GramSchmidt.liftFinLE i hk)).dotProduct
        (_root_.Hex.GramSchmidt.Int.castIntRow b (GramSchmidt.liftFinLE j hk))







/-- The col-op coefficient list for the `s`-th transition step: indices
`p : Fin s` lifted into `Fin k`. -/
 def _root_.Hex.GramSchmidt.Int.progressMatrixSources (k : Nat) (s : Nat) (hs : s < k) :
    List (Fin k) :=
  (List.finRange s).map fun p => ⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.le_of_lt hs)⟩



/-- The col-op coefficient for source `src : Fin k`: equals
`-(coeffs b)[s][src.val]`. -/
 noncomputable def _root_.Hex.GramSchmidt.Int.progressMatrixCoeff (b : Matrix Int n m) (k : Nat)
    (hk : k ≤ n) (s : Nat) (hs : s < k) (src : Fin k) : Rat :=
  -(GramSchmidt.entry (coeffs b)
    ⟨s, Nat.lt_of_lt_of_le hs hk⟩
    ⟨src.val, Nat.lt_of_lt_of_le src.isLt hk⟩)



































end Int
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

/-!
Mathlib-side determinantal identification of the canonical Bareiss
Gram-Schmidt coefficients for `hex-gram-schmidt`.

This module finishes the Cramer identity
`scaledCoeffMatrix_det_eq_gramDet_mul_coeffs`, expressing the scaled
coefficient determinant as `gramDet (j+1) * coeffs[i][j]`.  Its second half
introduces the augmented `(n+1) × (n+1)` matrix `augmentedGram`, whose upper
block is `gramMatrix b` and whose trailing column carries a standard basis
vector, and proves `noPivotLoop_augmentedGram_invariant`: the no-pivot Bareiss
pass on the augmented matrix mirrors the pass on `gramMatrix b` while its
trailing column tracks `bareissGramCanonicalCoeff`.  This yields
`bareissGramCanonicalCoeff_eq_augmentedGram_entry` and its bordered-minor
form, identifying the canonical row coefficients with a Bareiss minor
determinant.
-/

namespace Hex
namespace GramSchmidt
namespace Int


/-- Substitution helper for the diagonal `(i, i)` matrix entry under a Fin
equality. Folded out of `subst`/`rfl` so callers can rewrite the index without
dragging the dependent proof component through the motive. -/
 theorem _root_.InfoLossLAR.NativeLLL.Shared.h74bc156927f74ab6 {n : Nat} (M : Matrix Int n n)
    {i j : Fin n} (h : i = j) :
    M[i][i] = M[j][j] := by
  subst h; rfl

/-- If the `s`-fueled no-pivot Bareiss prefix already recorded a singular step,
that step persists into any longer pass. The longer pass's recorded singular
index therefore matches the earlier one. -/
 theorem _root_.InfoLossLAR.NativeLLL.Shared.h590e675636c058f5
    {n : Nat} (state : Matrix.BareissState Int n) (a b : Nat) (k : Fin n)
    (h_sing_a : (Matrix.noPivotLoop a state).singularStep = some k.val)
    (h_step_a : (Matrix.noPivotLoop a state).step = k.val)
    (h_zero_a :
      (Matrix.noPivotLoop a state).matrix[k][k] = 0)
    (hk : k.val + 1 < n) :
    Matrix.noPivotLoop (a + b) state = Matrix.noPivotLoop a state := by
  rw [Matrix.noPivotLoop_add a b state]
  set S := Matrix.noPivotLoop a state with hS_def
  have hDone : S.step + 1 < n := by rw [h_step_a]; exact hk
  have hp_zero :
      S.matrix[(⟨S.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨S.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0 := by
    have h_fin :
        (⟨S.step, Nat.lt_of_succ_lt hDone⟩ : Fin n) = k :=
      Fin.ext h_step_a
    exact (_root_.InfoLossLAR.NativeLLL.Shared.h74bc156927f74ab6 S.matrix h_fin).trans h_zero_a
  have h_sing_step : S.singularStep = some S.step := by
    rw [h_sing_a, h_step_a]
  exact Matrix.noPivotLoop_id_at_singular_fixedpoint (n := n) b S hDone hp_zero h_sing_step

/-! # Augmented Gram matrix for determinantal identification of
`bareissGramCanonicalCoeff`

The canonical row-coefficient vector of the initial no-pivot Bareiss trajectory
on `gramMatrix b` is identified with a trailing-column entry of the no-pivot
Bareiss pass on an `(n + 1) × (n + 1)` augmented matrix.  The upper `n × n`
block of the augmented matrix is `gramMatrix b`; the trailing column at upper
rows carries the standard basis vector `δ_a` at the chosen coefficient slot
`a`; the trailing row is structurally zero.

Because the trailing row is zero and the no-pivot Bareiss update at slot
`(i, j)` with `i, j < n` only consults the upper block, the upper-block
trajectory on the augmented matrix exactly mirrors the trajectory on
`gramMatrix b`.  Because the trailing-column update at row `i < n` and step
`k < i.val` mirrors the canonical-coefficient Bareiss step, the trailing
column at upper rows tracks `bareissGramCanonicalCoeff b fuel i` at slot `a`.
-/

/-- Augmented `(n + 1) × (n + 1)` matrix used to identify
`bareissGramCanonicalCoeff b fuel i [a]` with a trailing-column entry of the
no-pivot Bareiss pass.  Upper block is `gramMatrix b`; trailing column at
upper rows is the standard basis vector `δ_a`; trailing row is zero. -/
@[expose]
def augmentedGram (b : Matrix Int n m) (a : Fin n) :
    Hex.Matrix Int (n + 1) (n + 1) :=
  Matrix.ofFn fun i j : Fin (n + 1) =>
    if hi : i.val < n then
      if hj : j.val < n then
        (Matrix.gramMatrix b)[((⟨i.val, hi⟩ : Fin n), (⟨j.val, hj⟩ : Fin n))]
      else
        if i.val = a.val then (1 : Int) else 0
    else
      0

/-- Upper-block entry of `augmentedGram b a` agrees with `gramMatrix b`. -/
theorem augmentedGram_upper_block
    (b : Matrix Int n m) (a : Fin n) (i j : Fin n) :
    (augmentedGram b a)[(⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))][
        (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (n + 1))] =
      (Matrix.gramMatrix b)[i][j] := by
  unfold augmentedGram
  rw [Matrix.getElem_ofFn]
  simp [i.isLt, j.isLt]

/-- Trailing-column entry of `augmentedGram b a` at an upper row `i : Fin n`
is `1` when `i = a` and `0` otherwise. -/
theorem augmentedGram_trailing_col
    (b : Matrix Int n m) (a : Fin n) (i : Fin n) :
    (augmentedGram b a)[(⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))][
        Fin.last n] =
      (if i = a then (1 : Int) else 0) := by
  unfold augmentedGram
  rw [Matrix.getElem_ofFn]
  have h_iff : (i.val = a.val) ↔ (i = a) := ⟨Fin.ext, fun h => by rw [h]⟩
  simp [i.isLt, h_iff]



/-- Substitution helper: matrix entries agree when Fin indices are equal.
Used to reindex matrix-entry equalities across propositionally-equal Fin
indices without provoking motive issues from `rw`. -/
 theorem _root_.Hex.GramSchmidt.Int.matrix_entry_eq_of_eq {n m : Nat} (M : Hex.Matrix Int n m)
    {i i' : Fin n} {j j' : Fin m} (hi : i = i') (hj : j = j') :
    M[i][j] = M[i'][j'] := by
  subst hi; subst hj; rfl

/-- Local copy of `HexMatrixTheory.trailing_eq_at_step` (private there):
re-state `BareissNoPivotInvariant.trailing_eq` with the step value supplied
externally so the dependent bordered-minor type matches the desired
`s = state.step` substitution cleanly. -/
theorem trailing_eq_at_step_local
    {n' : Nat} {M : Hex.Matrix Int n' n'} {state : Matrix.BareissState Int n'}
    (hinv : HexMatrixTheory.BareissNoPivotInvariant M state)
    (s : Nat) (hs : s < n') (hstep : s = state.step)
    (a c : Fin n') (hsa : s ≤ a.val) (hsc : s ≤ c.val) :
    state.matrix[a][c] =
      Hex.Matrix.det (Hex.Matrix.borderedMinor M s hs a c) := by
  subst hstep
  exact hinv.trailing_eq hs a c hsa hsc

/-- Auxiliary monotonicity: if a no-pivot Bareiss state reaches
`fuel + 1` iterations from `noPivotInitialState M` without recording a singular
step, then the prefix at `fuel` iterations is also non-singular.  Singular
states are fixed points of further iteration, so a non-singular outcome at
`fuel + 1` forces a non-singular prefix. -/
 theorem _root_.Hex.GramSchmidt.Int.noPivotLoop_singularStep_none_of_succ
    {n : Nat} (M : Matrix Int n n) (fuel : Nat)
    (h_no_sing :
      (Matrix.noPivotLoop (fuel + 1)
          (Matrix.noPivotInitialState M)).singularStep = none) :
    (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).singularStep = none := by
  set init := Matrix.noPivotInitialState M with hinit
  have h_init : init.singularStep = none := rfl
  rcases noPivotLoop_singular_inv (n := n) fuel init h_init with hnone | ⟨k, hsing, hstep, hzero, hklt⟩
  · exact hnone
  · -- Singular at fuel persists to fuel + 1, contradicting h_no_sing.
    exfalso
    have hpersist : Matrix.noPivotLoop (fuel + 1) init = Matrix.noPivotLoop fuel init :=
      _root_.InfoLossLAR.NativeLLL.Shared.h590e675636c058f5 init fuel 1 k hsing hstep hzero hklt
    rw [hpersist, hsing] at h_no_sing
    nomatch h_no_sing

-- Encapsulation makes the nested entry reads and the canonical-coefficient
-- rewrites over the recursive `noPivotLoop` term defeq-heavy here; a modest
-- bump (down from the original 1000000) covers it.
set_option maxHeartbeats 400000 in
/-- Combined invariant relating the no-pivot Bareiss trajectory on the
augmented matrix to the trajectory on `gramMatrix b`.  Under `fuel + 1 ≤ n`
and a non-singular prefix on the Gram side, the augmented loop tracks the
Gram loop on (i) `step`, (ii) `prevPivot`, (iii) the upper `n × n` block,
and (iv) carries the canonical row coefficient in its trailing column. -/
theorem noPivotLoop_augmentedGram_invariant
    (b : Matrix Int n m) (a : Fin n) (fuel : Nat) :
    fuel + 1 ≤ n →
      (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none →
      (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (augmentedGram b a))).step =
        (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step ∧
      (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (augmentedGram b a))).prevPivot =
        (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).prevPivot ∧
      (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (augmentedGram b a))).singularStep = none ∧
      (∀ i j : Fin n,
        (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (augmentedGram b a))).matrix[
          (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))][
          (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (n + 1))] =
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][j]) ∧
      (∀ i : Fin n,
        (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (augmentedGram b a))).matrix[
          (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))][Fin.last n] =
          (bareissGramCanonicalCoeff b fuel i)[a]) := by
  induction fuel with
  | zero =>
      intro _ _
      refine ⟨rfl, rfl, rfl, ?_, ?_⟩
      · intro i j
        change (augmentedGram b a)[(⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))][
            (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (n + 1))] =
          (Matrix.gramMatrix b)[i][j]
        exact augmentedGram_upper_block b a i j
      · intro i
        change (augmentedGram b a)[(⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))][
            Fin.last n] =
          (Vector.ofFn fun k : Fin n => if i = k then (1 : Int) else 0)[a]
        rw [augmentedGram_trailing_col]
        simp
  | succ fuel ih =>
      intro hfuel h_no_sing
      -- Pull the previous-fuel invariant out of the inductive hypothesis.
      have hfuel_prev : fuel + 1 ≤ n := by omega
      have h_no_sing_prev :
          (Matrix.noPivotLoop fuel
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none :=
        _root_.Hex.GramSchmidt.Int.noPivotLoop_singularStep_none_of_succ (Matrix.gramMatrix b) fuel h_no_sing
      obtain ⟨h_step_prev, h_prev_prev, h_sing_aug_prev, h_block_prev, h_trail_prev⟩ :=
        ih hfuel_prev h_no_sing_prev
      -- Set up shorthand for the previous-fuel states.
      set stateG := Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)) with hstateG
      set stateA := Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (augmentedGram b a)) with hstateA
      -- Gram side has not finished and pivot is nonzero (else singular at fuel + 1).
      have h_step_G_fuel : stateG.step = fuel := by
        have h := Matrix.noPivotLoop_step_eq_add_of_singularStep_none fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl (by
            show 0 + fuel + 1 ≤ n; omega) h_no_sing_prev
        simp only [Matrix.noPivotInitialState, Nat.zero_add] at h
        rw [hstateG]
        exact h
      have hDone_G : stateG.step + 1 < n := by rw [h_step_G_fuel]; omega
      have hk_G_lt : stateG.step < n := Nat.lt_of_succ_lt hDone_G
      -- Pivot non-zero on the Gram side.
      have h_pivot_G_ne :
          stateG.matrix[(⟨stateG.step, hk_G_lt⟩ : Fin n)][
              (⟨stateG.step, hk_G_lt⟩ : Fin n)] ≠ 0 := by
        intro hzero
        -- Singular branch at fuel + 1 would record a singular step,
        -- contradicting `h_no_sing`.
        have h_sing_branch : Matrix.noPivotLoop 1 stateG
            = { stateG with singularStep := some stateG.step } :=
          Matrix.noPivotLoop_of_singular 0 stateG hDone_G hzero
        have h_succ_eq :
            Matrix.noPivotLoop (fuel + 1)
              (Matrix.noPivotInitialState (Matrix.gramMatrix b)) =
            Matrix.noPivotLoop 1 stateG := by
          rw [Matrix.noPivotLoop_add fuel 1]
        rw [h_succ_eq, h_sing_branch] at h_no_sing
        simp at h_no_sing
      -- Augmented side: step matches, so it has not finished either.
      have h_step_A_fuel : stateA.step = fuel := h_step_prev.trans h_step_G_fuel
      have hDone_A : stateA.step + 1 < n + 1 := by rw [h_step_A_fuel]; omega
      have hk_A_lt : stateA.step < n + 1 := Nat.lt_of_succ_lt hDone_A
      -- Pivot at the lifted index on the augmented side equals the Gram pivot.
      have h_pivot_A_eq :
          stateA.matrix[(⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))][
              (⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))] =
            stateG.matrix[(⟨stateG.step, hk_G_lt⟩ : Fin n)][
              (⟨stateG.step, hk_G_lt⟩ : Fin n)] := by
        have h_idx :
            (⟨stateA.step, hk_A_lt⟩ : Fin (n + 1)) =
              (⟨(⟨stateG.step, hk_G_lt⟩ : Fin n).val,
                Nat.lt_succ_of_lt (⟨stateG.step, hk_G_lt⟩ : Fin n).isLt⟩ :
                  Fin (n + 1)) := Fin.ext h_step_prev
        calc stateA.matrix[(⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))][
              (⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))]
            = stateA.matrix[(⟨(⟨stateG.step, hk_G_lt⟩ : Fin n).val,
                Nat.lt_succ_of_lt (⟨stateG.step, hk_G_lt⟩ : Fin n).isLt⟩ :
                  Fin (n + 1))][(⟨(⟨stateG.step, hk_G_lt⟩ : Fin n).val,
                Nat.lt_succ_of_lt (⟨stateG.step, hk_G_lt⟩ : Fin n).isLt⟩ :
                  Fin (n + 1))] := _root_.Hex.GramSchmidt.Int.matrix_entry_eq_of_eq _ h_idx h_idx
          _ = stateG.matrix[(⟨stateG.step, hk_G_lt⟩ : Fin n)][
                (⟨stateG.step, hk_G_lt⟩ : Fin n)] :=
              h_block_prev ⟨stateG.step, hk_G_lt⟩ ⟨stateG.step, hk_G_lt⟩
      have h_pivot_A_ne :
          stateA.matrix[(⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))][
              (⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))] ≠ 0 := by
        rw [h_pivot_A_eq]; exact h_pivot_G_ne
      -- Peel off the last iteration on both sides.
      have h_G_succ :
          Matrix.noPivotLoop (fuel + 1)
              (Matrix.noPivotInitialState (Matrix.gramMatrix b)) =
            Matrix.noPivotLoop 0
              { step := stateG.step + 1
                matrix := Matrix.stepMatrix stateG.matrix stateG.step
                  stateG.matrix[(⟨stateG.step, hk_G_lt⟩ : Fin n)][
                    (⟨stateG.step, hk_G_lt⟩ : Fin n)] stateG.prevPivot
                prevPivot := stateG.matrix[(⟨stateG.step, hk_G_lt⟩ : Fin n)][
                  (⟨stateG.step, hk_G_lt⟩ : Fin n)]
                rowSwaps := stateG.rowSwaps
                singularStep := none } := by
        rw [Matrix.noPivotLoop_add fuel 1]
        exact Matrix.noPivotLoop_of_regular 0 stateG hDone_G h_pivot_G_ne
      have h_A_succ :
          Matrix.noPivotLoop (fuel + 1)
              (Matrix.noPivotInitialState (augmentedGram b a)) =
            Matrix.noPivotLoop 0
              { step := stateA.step + 1
                matrix := Matrix.stepMatrix stateA.matrix stateA.step
                  stateA.matrix[(⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))][
                    (⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))] stateA.prevPivot
                prevPivot := stateA.matrix[(⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))][
                  (⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))]
                rowSwaps := stateA.rowSwaps
                singularStep := none } := by
        rw [Matrix.noPivotLoop_add fuel 1]
        exact Matrix.noPivotLoop_of_regular 0 stateA hDone_A h_pivot_A_ne
      -- Both peeled states are zero-fuel, so the loop returns them unchanged.
      rw [h_G_succ, h_A_succ, Matrix.noPivotLoop_zero_fuel, Matrix.noPivotLoop_zero_fuel]
      -- Now project each component of the invariant.
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- Step equality.
        show stateA.step + 1 = stateG.step + 1
        exact congrArg (· + 1) h_step_prev
      · -- prevPivot equality.
        show stateA.matrix[(⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))][
              (⟨stateA.step, hk_A_lt⟩ : Fin (n + 1))] =
            stateG.matrix[(⟨stateG.step, hk_G_lt⟩ : Fin n)][
              (⟨stateG.step, hk_G_lt⟩ : Fin n)]
        exact h_pivot_A_eq
      · -- singularStep = none.
        rfl
      · -- Upper-block invariant.
        intro i j
        -- Set up the lifted indices and `k` index used in `stepMatrix`.
        set iA : Fin (n + 1) := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ with hiA
        set jA : Fin (n + 1) := ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ with hjA
        -- Case-split on whether step `fuel = stateG.step` updates this entry.
        by_cases hi_lt : stateG.step < i.val
        · by_cases hj_lt : stateG.step < j.val
          · -- Trailing block: Bareiss update fires on both sides.
            have hi_lt_A : stateA.step < iA.val := by
              show stateA.step < i.val
              rw [h_step_prev]; exact hi_lt
            have hj_lt_A : stateA.step < jA.val := by
              show stateA.step < j.val
              rw [h_step_prev]; exact hj_lt
            rw [Matrix.stepMatrix_update_eq stateA.matrix stateA.step _ _ iA jA
              hi_lt_A hj_lt_A]
            rw [Matrix.stepMatrix_update_eq stateG.matrix stateG.step _ _ i j
              hi_lt hj_lt]
            dsimp only []
            -- Rewrite the four matrix entries on the LHS using the block IH.
            have h_ij_A : stateA.matrix[iA][jA] = stateG.matrix[i][j] :=
              h_block_prev i j
            -- (colK : Fin (n+1)) for aug, (colK_G : Fin n) for gram.
            -- These have step.val = stateG.step (by h_step_prev) and we use
            -- the IH at row=i, col=⟨stateG.step, hk_G_lt⟩, and so on.
            have h_step_lift_eq :
                (⟨stateA.step, Nat.lt_trans hi_lt_A iA.isLt⟩ : Fin (n + 1)) =
                  (⟨(⟨stateG.step, hk_G_lt⟩ : Fin n).val,
                    Nat.lt_succ_of_lt (⟨stateG.step, hk_G_lt⟩ : Fin n).isLt⟩ :
                      Fin (n + 1)) := by
              apply Fin.ext
              show stateA.step = stateG.step
              exact h_step_prev
            have h_iL_A :
                stateA.matrix[iA][(⟨stateA.step, Nat.lt_trans hi_lt_A iA.isLt⟩ :
                    Fin (n + 1))] =
                  stateG.matrix[i][(⟨stateG.step, hk_G_lt⟩ : Fin n)] := by
              calc stateA.matrix[iA][(⟨stateA.step, Nat.lt_trans hi_lt_A iA.isLt⟩ :
                      Fin (n + 1))]
                  = stateA.matrix[(⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))][
                      (⟨(⟨stateG.step, hk_G_lt⟩ : Fin n).val,
                        Nat.lt_succ_of_lt (⟨stateG.step, hk_G_lt⟩ : Fin n).isLt⟩ :
                          Fin (n + 1))] := _root_.Hex.GramSchmidt.Int.matrix_entry_eq_of_eq _ rfl h_step_lift_eq
                _ = stateG.matrix[i][(⟨stateG.step, hk_G_lt⟩ : Fin n)] :=
                    h_block_prev i ⟨stateG.step, hk_G_lt⟩
            have h_kJ_A :
                stateA.matrix[(⟨stateA.step, Nat.lt_trans hj_lt_A jA.isLt⟩ :
                    Fin (n + 1))][jA] =
                  stateG.matrix[(⟨stateG.step, hk_G_lt⟩ : Fin n)][j] := by
              calc stateA.matrix[(⟨stateA.step, Nat.lt_trans hj_lt_A jA.isLt⟩ :
                      Fin (n + 1))][jA]
                  = stateA.matrix[(⟨(⟨stateG.step, hk_G_lt⟩ : Fin n).val,
                      Nat.lt_succ_of_lt (⟨stateG.step, hk_G_lt⟩ : Fin n).isLt⟩ :
                        Fin (n + 1))][(⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (n + 1))] :=
                    _root_.Hex.GramSchmidt.Int.matrix_entry_eq_of_eq _ h_step_lift_eq rfl
                _ = stateG.matrix[(⟨stateG.step, hk_G_lt⟩ : Fin n)][j] :=
                    h_block_prev ⟨stateG.step, hk_G_lt⟩ j
            rw [h_ij_A, h_iL_A, h_kJ_A, h_pivot_A_eq, h_prev_prev]
          · -- Trailing row, but column ≤ step. Then both sides preserve the entry.
            -- On aug, the `stepMatrix` update condition `k < i ∧ k < j` fails because `j ≤ k`.
            -- Could be `j.val < k` (no update) or `j.val = k` (clear pivot col below;
            -- value 0, which matches Gram side since both are 0 below pivot).
            by_cases hj_eq : j.val = stateG.step
            · -- Clear pivot column below: both sides set to 0.
              have hj_eq_A : jA.val = stateA.step := by
                show j.val = stateA.step
                rw [h_step_prev]; exact hj_eq
              have hi_lt_A : stateA.step < iA.val := by
                show stateA.step < i.val
                rw [h_step_prev]; exact hi_lt
              rw [Matrix.stepMatrix_pivot_col_below stateA.matrix stateA.step _ _ iA jA
                hi_lt_A hj_eq_A]
              rw [Matrix.stepMatrix_pivot_col_below stateG.matrix stateG.step _ _ i j
                hi_lt hj_eq]
            · -- Column strictly below pivot: both sides preserve their value.
              have hj_lt_step : j.val < stateG.step := by omega
              have hj_lt_step_A : jA.val < stateA.step := by
                show j.val < stateA.step
                rw [h_step_prev]; exact hj_lt_step
              have h_not_update_A : ¬ (stateA.step < iA.val ∧ stateA.step < jA.val) := by
                intro ⟨_, h⟩; omega
              have h_not_col_A : ¬ (stateA.step < iA.val ∧ jA.val = stateA.step) := by
                intro ⟨_, h⟩; omega
              have h_not_update_G : ¬ (stateG.step < i.val ∧ stateG.step < j.val) := by
                intro ⟨_, h⟩; omega
              have h_not_col_G : ¬ (stateG.step < i.val ∧ j.val = stateG.step) := by
                intro ⟨_, h⟩; omega
              rw [Matrix.stepMatrix_eq_of_not_update stateA.matrix stateA.step _ _ iA jA
                h_not_update_A h_not_col_A]
              rw [Matrix.stepMatrix_eq_of_not_update stateG.matrix stateG.step _ _ i j
                h_not_update_G h_not_col_G]
              exact h_block_prev i j
        · -- Row ≤ step: no update on either side.
          have hi_le_step : i.val ≤ stateG.step := Nat.le_of_not_lt hi_lt
          have hi_le_step_A : iA.val ≤ stateA.step := by
            show i.val ≤ stateA.step
            rw [h_step_prev]; exact hi_le_step
          have h_not_update_A : ¬ (stateA.step < iA.val ∧ stateA.step < jA.val) := by
            intro ⟨h, _⟩; exact Nat.not_lt_of_ge hi_le_step_A h
          have h_not_col_A : ¬ (stateA.step < iA.val ∧ jA.val = stateA.step) := by
            intro ⟨h, _⟩; exact Nat.not_lt_of_ge hi_le_step_A h
          have h_not_update_G : ¬ (stateG.step < i.val ∧ stateG.step < j.val) := by
            intro ⟨h, _⟩; exact Nat.not_lt_of_ge hi_le_step h
          have h_not_col_G : ¬ (stateG.step < i.val ∧ j.val = stateG.step) := by
            intro ⟨h, _⟩; exact Nat.not_lt_of_ge hi_le_step h
          rw [Matrix.stepMatrix_eq_of_not_update stateA.matrix stateA.step _ _ iA jA
            h_not_update_A h_not_col_A]
          rw [Matrix.stepMatrix_eq_of_not_update stateG.matrix stateG.step _ _ i j
            h_not_update_G h_not_col_G]
          exact h_block_prev i j
      · -- Trailing-column invariant.
        intro i
        set iA : Fin (n + 1) := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ with hiA
        set L : Fin (n + 1) := Fin.last n with hL
        have hL_lt : stateA.step < L.val := by
          show stateA.step < n
          rw [h_step_prev]; exact hk_G_lt
        by_cases hi_lt : stateG.step < i.val
        · -- Active row: both sides apply the Bareiss update.
          have hi_lt_A : stateA.step < iA.val := by
            show stateA.step < i.val
            rw [h_step_prev]; exact hi_lt
          rw [Matrix.stepMatrix_update_eq stateA.matrix stateA.step _ _ iA L
            hi_lt_A hL_lt]
          dsimp only []
          -- Match the four entries on the LHS via the IH:
          -- - the trailing-column entry at row i: by trailing IH.
          -- - the entry (i, step↑): by block IH after reindexing.
          -- - the entry (step↑, last n): by trailing IH at row k.
          -- The pivot at (step↑, step↑) is `h_pivot_A_eq`.
          have h_iL_A : stateA.matrix[iA][L] = (bareissGramCanonicalCoeff b fuel i)[a] :=
            h_trail_prev i
          have h_step_lift_eq :
              (⟨stateA.step, Nat.lt_trans hi_lt_A iA.isLt⟩ : Fin (n + 1)) =
                (⟨(⟨stateG.step, hk_G_lt⟩ : Fin n).val,
                  Nat.lt_succ_of_lt (⟨stateG.step, hk_G_lt⟩ : Fin n).isLt⟩ :
                    Fin (n + 1)) := by
            apply Fin.ext
            show stateA.step = stateG.step
            exact h_step_prev
          have h_iK_A :
              stateA.matrix[iA][(⟨stateA.step, Nat.lt_trans hi_lt_A iA.isLt⟩ :
                  Fin (n + 1))] =
                stateG.matrix[i][(⟨stateG.step, hk_G_lt⟩ : Fin n)] := by
            calc stateA.matrix[iA][(⟨stateA.step, Nat.lt_trans hi_lt_A iA.isLt⟩ :
                    Fin (n + 1))]
                = stateA.matrix[(⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))][
                    (⟨(⟨stateG.step, hk_G_lt⟩ : Fin n).val,
                      Nat.lt_succ_of_lt (⟨stateG.step, hk_G_lt⟩ : Fin n).isLt⟩ :
                        Fin (n + 1))] := _root_.Hex.GramSchmidt.Int.matrix_entry_eq_of_eq _ rfl h_step_lift_eq
              _ = stateG.matrix[i][(⟨stateG.step, hk_G_lt⟩ : Fin n)] :=
                  h_block_prev i ⟨stateG.step, hk_G_lt⟩
          have h_kL_A :
              stateA.matrix[(⟨stateA.step, Nat.lt_trans hL_lt L.isLt⟩ : Fin (n + 1))][L] =
                (bareissGramCanonicalCoeff b fuel ⟨stateG.step, hk_G_lt⟩)[a] := by
            calc stateA.matrix[(⟨stateA.step, Nat.lt_trans hL_lt L.isLt⟩ :
                    Fin (n + 1))][L]
                = stateA.matrix[(⟨(⟨stateG.step, hk_G_lt⟩ : Fin n).val,
                    Nat.lt_succ_of_lt (⟨stateG.step, hk_G_lt⟩ : Fin n).isLt⟩ :
                      Fin (n + 1))][Fin.last n] :=
                  _root_.Hex.GramSchmidt.Int.matrix_entry_eq_of_eq _ h_step_lift_eq rfl
              _ = (bareissGramCanonicalCoeff b fuel
                    (⟨stateG.step, hk_G_lt⟩ : Fin n))[a] :=
                  h_trail_prev ⟨stateG.step, hk_G_lt⟩
          rw [h_iL_A, h_iK_A, h_kL_A, h_pivot_A_eq, h_prev_prev]
          -- The RHS is the canonical-coefficient recursion at active row.
          have hp_canon :
              (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
                (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
                (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0 := by
            show stateG.matrix[stateG.step][stateG.step] ≠ 0
            -- Lower the Fin index proof.
            intro hzero
            apply h_pivot_G_ne
            exact hzero
          have hnext_canon :
              (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n := by
            show stateG.step + 1 < n; exact hDone_G
          have hi_lt_canon :
              (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val := by
            show stateG.step + 1 ≤ i.val; exact hi_lt
          rw [bareissGramCanonicalCoeff_succ_regular b fuel i hnext_canon hp_canon hi_lt_canon]
          conv_rhs => rw [show ∀ f : Fin n → Int, (Vector.ofFn f)[a] = f a from
            fun f => by simp]
        · -- Processed row (i.val ≤ step): both sides preserve the value.
          have hi_le_step : i.val ≤ stateG.step := Nat.le_of_not_lt hi_lt
          have hi_le_step_A : iA.val ≤ stateA.step := by
            show i.val ≤ stateA.step
            rw [h_step_prev]; exact hi_le_step
          have h_not_update_A : ¬ (stateA.step < iA.val ∧ stateA.step < L.val) := by
            intro ⟨h, _⟩; exact Nat.not_lt_of_ge hi_le_step_A h
          have h_not_col_A : ¬ (stateA.step < iA.val ∧ L.val = stateA.step) := by
            intro ⟨h, _⟩; exact Nat.not_lt_of_ge hi_le_step_A h
          rw [Matrix.stepMatrix_eq_of_not_update stateA.matrix stateA.step _ _ iA L
            h_not_update_A h_not_col_A]
          -- Canon in processed-row case: stays at fuel-value.
          have hnext_canon :
              (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n := by
            show stateG.step + 1 < n; exact hDone_G
          have hp_canon :
              (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
                (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
                (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0 := by
            show stateG.matrix[stateG.step][stateG.step] ≠ 0
            intro hzero
            apply h_pivot_G_ne; exact hzero
          have h_not_active :
              ¬ (Matrix.noPivotLoop fuel
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val := by
            show ¬ stateG.step + 1 ≤ i.val; omega
          rw [bareissGramCanonicalCoeff_succ_processed b fuel i hnext_canon hp_canon
            h_not_active]
          exact h_trail_prev i

/-- Determinantal identification of the canonical row-coefficient vector
`bareissGramCanonicalCoeff b fuel i` at slot `a` as the trailing-column entry
of the no-pivot Bareiss pass on the augmented `(n + 1) × (n + 1)` matrix
`augmentedGram b a`.  The hypothesis `fuel ≤ i.val` ensures the comparison
covers both the active-row and processed-row branches of the canonical
recursion. -/
theorem bareissGramCanonicalCoeff_eq_augmentedGram_entry
    (b : Matrix Int n m) (fuel : Nat) (i : Fin n) (a : Fin n)
    (hfuel : fuel ≤ i.val)
    (h_no_sing :
      (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    (bareissGramCanonicalCoeff b fuel i)[a] =
      (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (augmentedGram b a))).matrix[
        (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))][Fin.last n] := by
  have hfuel_n : fuel + 1 ≤ n := by
    have : i.val < n := i.isLt
    omega
  obtain ⟨_, _, _, _, h_trail⟩ :=
    noPivotLoop_augmentedGram_invariant b a fuel hfuel_n h_no_sing
  exact (h_trail i).symm

/-- Direct bordered-minor form: the canonical row-coefficient vector at slot
`a` equals the determinant of the `(fuel + 1) × (fuel + 1)` bordered minor of
the augmented Gram matrix.  Composes
`bareissGramCanonicalCoeff_eq_augmentedGram_entry` with the Bareiss
no-pivot invariant `trailing_eq`. -/
theorem bareissGramCanonicalCoeff_eq_borderedMinor_aug
    (b : Matrix Int n m) (fuel : Nat) (i : Fin n) (a : Fin n)
    (hfuel : fuel ≤ i.val)
    (h_no_sing :
      (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    (bareissGramCanonicalCoeff b fuel i)[a] =
      Matrix.det (Matrix.borderedMinor (augmentedGram b a) fuel
        (by have : i.val < n := i.isLt; omega : fuel < n + 1)
        (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1)) (Fin.last n)) := by
  rw [bareissGramCanonicalCoeff_eq_augmentedGram_entry b fuel i a hfuel h_no_sing]
  -- Set up the Bareiss invariant on the augmented loop.
  have hfuel_n : fuel + 1 ≤ n := by
    have : i.val < n := i.isLt; omega
  obtain ⟨_, _, h_sing_aug, _, _⟩ :=
    noPivotLoop_augmentedGram_invariant b a fuel hfuel_n h_no_sing
  have h_step_aug_eq_fuel :
      (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (augmentedGram b a))).step = fuel := by
    have h := Matrix.noPivotLoop_step_eq_add_of_singularStep_none fuel
      (Matrix.noPivotInitialState (augmentedGram b a)) rfl (by
        show 0 + fuel + 1 ≤ n + 1; omega) h_sing_aug
    simpa [Matrix.noPivotInitialState] using h
  have h_inv : HexMatrixTheory.BareissNoPivotInvariant (augmentedGram b a)
      (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState (augmentedGram b a))) :=
    HexMatrixTheory.noPivotLoop_invariant_of_singularStep_eq_none
      (augmentedGram b a) fuel
      (Matrix.noPivotInitialState (augmentedGram b a))
      (HexMatrixTheory.bareissNoPivotInvariant_initial (augmentedGram b a)) h_sing_aug
  -- Apply trailing_eq_at_step with `s := fuel` and `hstep := h_step_aug_eq_fuel.symm`.
  have h_step_lt : fuel < n + 1 := by omega
  have h_step_le_i : fuel ≤ (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1)).val := hfuel
  have h_step_le_last : fuel ≤ (Fin.last n).val := by show fuel ≤ n; omega
  exact trailing_eq_at_step_local h_inv fuel h_step_lt h_step_aug_eq_fuel.symm
    (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1)) (Fin.last n)
    h_step_le_i h_step_le_last

/-- Under a non-singular no-pivot Bareiss prefix that has not yet reached the
terminal step, the loop on the initial state of `M` consumed exactly `fuel`
regular iterations: the resulting step equals `fuel`, and `fuel + 1 ≤ n'`. -/
theorem noPivotLoop_initial_step_eq_and_fuel_succ_le
    {n' : Nat} (M : Hex.Matrix Int n' n') (fuel : Nat)
    (h_no_sing :
      (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).singularStep = none)
    (hnext :
      (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).step + 1 < n') :
    (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).step = fuel ∧
      fuel + 1 ≤ n' := by
  induction fuel with
  | zero =>
    have h_init_step : (Matrix.noPivotInitialState M).step = 0 := rfl
    refine ⟨rfl, ?_⟩
    have h0 := hnext
    rw [Matrix.noPivotLoop_zero_fuel, h_init_step] at h0
    omega
  | succ fuel ih =>
    have h_no_sing_prev := _root_.Hex.GramSchmidt.Int.noPivotLoop_singularStep_none_of_succ M fuel h_no_sing
    set state' := Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M) with hstate'
    by_cases hDone : state'.step + 1 < n'
    · by_cases hp : state'.matrix[state'.step][state'.step] = 0
      · exfalso
        rw [Matrix.noPivotLoop_add fuel 1, ← hstate',
            Matrix.noPivotLoop_of_singular 0 state' hDone hp] at h_no_sing
        simp at h_no_sing
      · -- Regular branch: peel the last iteration.
        obtain ⟨h_step_prev, h_fuel_prev⟩ := ih h_no_sing_prev hDone
        refine ⟨?_, by omega⟩
        rw [Matrix.noPivotLoop_add fuel 1, ← hstate',
            Matrix.noPivotLoop_of_regular 0 state' hDone hp,
            Matrix.noPivotLoop_zero_fuel]
        show state'.step + 1 = fuel + 1
        rw [h_step_prev]
    · exfalso
      rw [Matrix.noPivotLoop_add fuel 1, ← hstate',
          Matrix.noPivotLoop_done 0 state' hDone] at hnext
      exact hDone hnext

/-- Companion to `trailing_eq_at_step_local`: rewrite
`BareissNoPivotInvariant.prevPivot_eq` with the step value supplied externally
so the dependent `principalSubmatrix` type matches the desired `s = state.step`
substitution cleanly. -/
theorem prevPivot_eq_at_step_local
    {n' : Nat} {M : Hex.Matrix Int n' n'} {state : Matrix.BareissState Int n'}
    (hinv : HexMatrixTheory.BareissNoPivotInvariant M state)
    (s : Nat) (hs : s ≤ n') (hstep : s = state.step) :
    state.prevPivot = Hex.Matrix.det (Hex.Matrix.principalSubmatrix M s hs) := by
  subst hstep
  exact hinv.prevPivot_eq

/-- Concrete bridge-side instance of `StepWitness` for any integer basis.

The witness quotient at slot `a` is the next iteration's canonical row
coefficient `(bareissGramCanonicalCoeff b (fuel + 1) i)[a]`.  Integrality of
this quotient comes from the Bareiss-Desnanot identity applied to the
augmented `(n + 1) × (n + 1)` matrix `augmentedGram b a`: the canonical
coefficients identify with trailing-column entries of the augmented no-pivot
Bareiss pass (`bareissGramCanonicalCoeff_eq_borderedMinor_aug`), and the
Bareiss step recurrence on the augmented matrix supplies the exact-division
multiplicative identity. -/
@[expose]
def StepWitness.ofGram (b : Matrix Int n m) :
    Hex.GramSchmidt.Int.StepWitness b := by
  intro fuel hinv h_canon h_prefix_none hnext hp i hi
  -- Prepare bound facts and the step equality before refining.
  set state := Matrix.noPivotLoop fuel
    (Matrix.noPivotInitialState (Matrix.gramMatrix b)) with hstate
  obtain ⟨h_step_eq_fuel, hfuel_n_le⟩ :=
    noPivotLoop_initial_step_eq_and_fuel_succ_le (Matrix.gramMatrix b)
      fuel h_prefix_none hnext
  have hfuel_lt_n : fuel < n := by omega
  have hfuel_lt_naug : fuel < n + 1 := by omega
  have hfuel_succ_lt_naug : fuel + 1 < n + 1 := by omega
  have hfuel_le_naug : fuel ≤ n + 1 := by omega
  -- The prefix at `fuel + 1` is also non-singular (one more regular step).
  have h_prefix_none_succ :
      (Matrix.noPivotLoop (fuel + 1)
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none := by
    rw [Matrix.noPivotLoop_add fuel 1, ← hstate,
        Matrix.noPivotLoop_of_regular 0 state hnext hp,
        Matrix.noPivotLoop_zero_fuel]
  have h_fuel_succ_le_i : fuel + 1 ≤ i.val := by rw [← h_step_eq_fuel]; exact hi
  refine ⟨fun a => (Hex.GramSchmidt.Int.bareissGramCanonicalCoeff b (fuel + 1) i)[a], ?_⟩
  -- The structure field has an outer `let k := ⟨state.step, _⟩` binder before
  -- the `∀ a`, so two intros are needed.
  intro k_let a
  -- Augmented invariants at fuel and fuel + 1, both at slot `a`.
  obtain ⟨h_step_A, h_prev_A, h_sing_A, h_block_A, h_trail_A⟩ :=
    noPivotLoop_augmentedGram_invariant b a fuel hfuel_n_le h_prefix_none
  set stateA := Matrix.noPivotLoop fuel
    (Matrix.noPivotInitialState (augmentedGram b a)) with hstateA
  -- The lifted Fin (n + 1) indices used throughout.
  set iA : Fin (n + 1) := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ with hiA_def
  set kA : Fin (n + 1) := ⟨k_let.val, Nat.lt_succ_of_lt k_let.isLt⟩ with hkA_def
  set L : Fin (n + 1) := Fin.last n with hL_def
  -- `k_let.val = state.step = fuel`, so `kA.val = fuel`.
  have h_kA_val : kA.val = fuel := h_step_eq_fuel
  have h_fuel_le_kA : fuel ≤ kA.val := Nat.le_of_eq h_kA_val.symm
  have h_fuel_lt_iA : fuel < iA.val := by show fuel < i.val; omega
  have h_fuel_lt_L : fuel < L.val := by show fuel < n; omega
  have h_fuel_le_iA : fuel ≤ iA.val := Nat.le_of_lt h_fuel_lt_iA
  have h_fuel_le_L : fuel ≤ L.val := Nat.le_of_lt h_fuel_lt_L
  -- Substitute the row-invariant's coefficients by canonical via h_canon.
  rw [h_canon i, h_canon k_let]
  -- Bridge state.matrix entries to stateA entries via the upper-block bridge.
  simp only [Hex.Matrix.getElem_pair_eq_nested]
  rw [show state.matrix[k_let][k_let] = stateA.matrix[kA][kA] from
      (h_block_A k_let k_let).symm]
  rw [show state.matrix[i][k_let] = stateA.matrix[iA][kA] from
      (h_block_A i k_let).symm]
  -- Bridge canonical coefficients to stateA trailing-column entries.
  rw [show (bareissGramCanonicalCoeff b fuel i)[a] = stateA.matrix[iA][L] from
      (h_trail_A i).symm]
  rw [show (bareissGramCanonicalCoeff b fuel k_let)[a] = stateA.matrix[kA][L] from
      (h_trail_A k_let).symm]
  -- Bridge state.prevPivot to stateA.prevPivot (h_prev_A goes the other way).
  rw [← h_prev_A]
  -- Bareiss invariant on the augmented loop at fuel.
  have h_inv : HexMatrixTheory.BareissNoPivotInvariant (augmentedGram b a) stateA :=
    HexMatrixTheory.noPivotLoop_invariant_of_singularStep_eq_none
      (augmentedGram b a) fuel _
      (HexMatrixTheory.bareissNoPivotInvariant_initial (augmentedGram b a))
      h_sing_A
  have h_stateA_step : stateA.step = fuel := h_step_A.trans h_step_eq_fuel
  -- Rewrite each stateA entry and the prevPivot as bordered-minor determinants.
  rw [trailing_eq_at_step_local h_inv fuel hfuel_lt_naug h_stateA_step.symm kA kA
        h_fuel_le_kA h_fuel_le_kA]
  rw [trailing_eq_at_step_local h_inv fuel hfuel_lt_naug h_stateA_step.symm iA L
        h_fuel_le_iA h_fuel_le_L]
  rw [trailing_eq_at_step_local h_inv fuel hfuel_lt_naug h_stateA_step.symm iA kA
        h_fuel_le_iA h_fuel_le_kA]
  rw [trailing_eq_at_step_local h_inv fuel hfuel_lt_naug h_stateA_step.symm kA L
        h_fuel_le_kA h_fuel_le_L]
  rw [prevPivot_eq_at_step_local h_inv fuel hfuel_le_naug h_stateA_step.symm]
  -- Beta-reduce the explicit `q a` on the RHS so the next rewrite matches.
  show ((augmentedGram b a).borderedMinor fuel hfuel_lt_naug kA kA).det *
        ((augmentedGram b a).borderedMinor fuel hfuel_lt_naug iA L).det -
      ((augmentedGram b a).borderedMinor fuel hfuel_lt_naug iA kA).det *
        ((augmentedGram b a).borderedMinor fuel hfuel_lt_naug kA L).det =
    (bareissGramCanonicalCoeff b (fuel + 1) i)[a] *
      ((augmentedGram b a).principalSubmatrix fuel hfuel_le_naug).det
  rw [bareissGramCanonicalCoeff_eq_borderedMinor_aug b (fuel + 1) i a
        h_fuel_succ_le_i h_prefix_none_succ]
  -- Desnanot-Jacobi on the augmented matrix at level `fuel`.
  have hdj :=
    HexMatrixTheory.desnanot_jacobi_borderedMinor (augmentedGram b a) fuel
      hfuel_lt_naug hfuel_succ_lt_naug iA L h_fuel_lt_iA h_fuel_lt_L
  -- The K positions in hdj are `⟨fuel, _⟩ : Fin (n + 1)`; via Fin.ext they
  -- equal `kA` (whose value is `state.step = fuel`).
  have hK : ∀ (h : fuel < n + 1), (⟨fuel, h⟩ : Fin (n + 1)) = kA := fun _ =>
    Fin.ext h_kA_val.symm
  simp_rw [hK] at hdj
  exact hdj.symm









end Int
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
namespace Int
/-! # Adjacent-swap pivot Gram-determinant product

Swapping adjacent rows `km1, k` (with `km1 + 1 = k`) of `b` changes only the
leading `k × k` Gram determinant within `0 ≤ t ≤ k + 1`. The new pivot Gram
determinant `gramDet (rowSwap b km1 k) k` satisfies the integer product
identity

    gramDet b' k · gramDet b k = gramDet b (k+1) · gramDet b km1 + B²

where `B = (scaledCoeffs b)[k][km1]`. This is the fraction-free form of the
standard rational adjacent-swap update used by integer LLL. -/



















/-- All-zero foldl: when every term in the foldl is zero, the result equals
the initial accumulator. -/
 theorem _root_.Hex.GramSchmidt.Int.foldl_add_zero_of_all_zero_rat {α : Type}
    (f : α → Rat) (xs : List α) (h : ∀ x ∈ xs, f x = 0) (acc : Rat) :
    xs.foldl (fun acc' x => acc' + f x) acc = acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = 0 := h x (by simp)
      rw [hx, Rat.add_zero]
      exact ih (fun y hy => h y (by simp [hy])) acc

/-- Foldl isolation: when every term except the `j`-th vanishes, the foldl
over `List.finRange i` collapses to `f ⟨j, hj⟩`. -/
 theorem _root_.Hex.GramSchmidt.Int.foldl_finRange_isolate_rat :
    ∀ (i : Nat) (j : Nat) (hj : j < i) (f : Fin i → Rat),
      (∀ q : Fin i, q.val ≠ j → f q = 0) →
      (List.finRange i).foldl (fun acc q => acc + f q) 0 = f ⟨j, hj⟩
  | 0, _, hj, _, _ => absurd hj (Nat.not_lt_zero _)
  | i + 1, j, hj, f, h_zero => by
      rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
      simp only [List.foldl_cons, List.foldl_nil]
      by_cases hj_eq : j = i
      · -- j = i: the `Fin.last i` term contributes `f ⟨j, hj⟩`.
        subst hj_eq
        have hzero_pre : ∀ q : Fin j, f (Fin.castSucc q) = 0 := by
          intro q
          apply h_zero
          have : (Fin.castSucc q).val = q.val := rfl
          rw [this]
          exact Nat.ne_of_lt q.isLt
        have hmem_zero : ∀ q ∈ List.finRange j, f (Fin.castSucc q) = 0 := by
          intro q _
          exact hzero_pre q
        have hfold_zero :
            (List.finRange j).foldl
                (fun (acc : Rat) (q : Fin j) => acc + f (Fin.castSucc q)) 0 = 0 :=
          _root_.Hex.GramSchmidt.Int.foldl_add_zero_of_all_zero_rat (fun q => f (Fin.castSucc q))
            (List.finRange j) hmem_zero 0
        rw [hfold_zero, Rat.zero_add]
        rfl
      · -- j < i: recurse on the smaller range.
        have hjlt : j < i := by omega
        have hlast_zero : f (Fin.last i) = 0 := by
          apply h_zero
          have : (Fin.last i).val = i := rfl
          rw [this]
          omega
        rw [hlast_zero, Rat.add_zero]
        have hzero_pre : ∀ q : Fin i, q.val ≠ j → f (Fin.castSucc q) = 0 := by
          intro q hq_ne
          apply h_zero
          have : (Fin.castSucc q).val = q.val := rfl
          rw [this]
          exact hq_ne
        have hih := foldl_finRange_isolate_rat i j hjlt
          (fun q => f (Fin.castSucc q)) hzero_pre
        rw [hih]
        rfl





















end Int
end GramSchmidt
end Hex

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end


