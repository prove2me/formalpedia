-- Prove2me | Definitions.Def_LARLLL_NativeLLLData
-- name    : LARLLL_NativeLLLData
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T02:42:52.488305+00:00
-- url     : https://prove2.me/theorems/9acdfde3-1f1b-425a-bfd6-d7025bbb03f9
-- title:
--   The original fuel-bounded integer LLL program and lattice data
-- statement:
--   The original integer lattice membership predicate, integer LLL state, size reduction, adjacent swaps, and explicit-fuel LLL loop, together with the reduction-property data types. No bound on full bit running time is asserted.
-- source:
--   Apache-2.0 leanprover/hex source and the already checked native LLL adapters. Exact original module locations and SHA-256 values are recorded in the validation receipt. Whole original declaration commands were retained using the official Lean declaration/sketch and structural syntax oracles, with original notices, checked computational definitions, and csimp proof logic preserved. All retained declaration types and safe non-theorem values were compared to the original environment using kernel-checked reflexivity after expanding safe generated implementation helpers. Source SHA-256: fc3d0e7e689e70d04342fc7c5960951cc9d55faede19184a0440a7d1f78e0fee.

import Definitions.Def_LARLLL_IntegerGramSchmidt

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/






set_option autoImplicit true



section

/-!
Row-operation update formulas for `hex-gram-schmidt`.

This module packages the elementary row operations used by LLL and states the
resulting update formulas for the Gram-Schmidt basis, coefficient, scaled
coefficient, and Gram-determinant surfaces. The executable row operations live
in `HexMatrix`; this file supplies the `HexGramSchmidt`-level API that later
libraries use to reason about size reduction and adjacent swaps.
-/
namespace Hex

namespace GramSchmidt

/-- The row immediately preceding `k`. -/
@[expose]
def prevRow (k : Fin n) (hk : 0 < k.val) : Fin n := by
  refine ⟨k.val - 1, ?_⟩
  omega

end GramSchmidt

namespace GramSchmidt.Int

/-- Size-reduce row `k` against an earlier row `j` by replacing
`b[k]` with `b[k] - r * b[j]`. -/
@[expose]
def sizeReduce (b : Matrix Int n m) (j k : Fin n) (r : Int) : Matrix Int n m :=
  Matrix.rowAdd b j k (-r)

/-- Swap adjacent rows `k - 1` and `k`. -/
@[expose]
def adjacentSwap (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val) : Matrix Int n m :=
  Matrix.rowSwap b (GramSchmidt.prevRow k hk) k

/-- The old `d[k]` denominator used by exact adjacent-swap updates. -/
@[expose]
def adjacentSwapDenom (b : Matrix Int n m) (k : Fin n) : Int :=
  ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int)

/-- The old `B = nu[k][k-1]` pivot coefficient used by adjacent swaps. -/
@[expose]
def adjacentSwapPivotCoeff (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val) : Int :=
  let km1 := GramSchmidt.prevRow k hk
  GramSchmidt.entry (scaledCoeffs b) k km1

/-- Numerator of the adjacent-swap `d[k]'` update. -/
@[expose]
def adjacentSwapGramDetNumerator (b : Matrix Int n m) (k : Fin n) (hk : 0 < k.val) :
    Int :=
  let km1 := GramSchmidt.prevRow k hk
  let B := adjacentSwapPivotCoeff b k hk
  ((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
      ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) + B ^ 2



/-- Numerator of the adjacent-swap `nu[i][k-1]'` update for rows above `k`. -/
@[expose]
def adjacentSwapScaledCoeffAbovePrevNumerator (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (i : Fin n) : Int :=
  let km1 := GramSchmidt.prevRow k hk
  let B := adjacentSwapPivotCoeff b k hk
  ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) *
      GramSchmidt.entry (scaledCoeffs b) i k +
    B * GramSchmidt.entry (scaledCoeffs b) i km1

/-- Numerator of the adjacent-swap `nu[i][k]'` update for rows above `k`. -/
@[expose]
def adjacentSwapScaledCoeffAboveCurrNumerator (b : Matrix Int n m)
    (k : Fin n) (hk : 0 < k.val) (i : Fin n) : Int :=
  let km1 := GramSchmidt.prevRow k hk
  let B := adjacentSwapPivotCoeff b k hk
  ((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
      GramSchmidt.entry (scaledCoeffs b) i km1 -
    B * GramSchmidt.entry (scaledCoeffs b) i k


























/-! The four `adjacentSwap` scaled-coefficient identities for rows above the
pivot (`scaledCoeffs_adjacentSwap_above_prev`, `_above_curr`, and the two
`_dvd` companions) live in `HexGramSchmidtTheory/Update.lean`. Their proof
path goes through `bareiss_scaledCoeffMatrix_rowSwap_above_prev` and
`bareiss_scaledCoeffMatrix_rowSwap_above_curr`, whose bordered-minor proofs
use the Mathlib determinant correspondence and therefore live in the Mathlib
bridge rather than the computational core. -/

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

/-! Integer row-lattice membership and transport through explicit row maps. -/

namespace Hex.Matrix

/-- `v` lies in the integer lattice generated by the rows of `b`. -/
@[expose]
def memLattice (b : Matrix Int n m) (v : Vector Int m) : Prop :=
  ∃ c : Vector Int n, vecMul c b = v

















end Hex.Matrix

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




namespace Hex.Matrix
end Hex.Matrix



set_option autoImplicit true



section

/-!
Integer row-lattice membership and independence for `hex-lll`,
with the row-operation lemmas showing that an adjacent swap or a
size-reduction row combination preserves the generated lattice.
-/

namespace Hex

namespace Matrix

/-- The rows of `b` are linearly independent, witnessed by positivity of each
executable leading Gram determinant. -/
@[expose]
def independent (b : Matrix Int n m) : Prop :=
  GramSchmidt.Int.independent b

/-- Independence is decidable (via `GramSchmidt.Int.independent`), so it can be
tested at runtime. -/
instance _root_.Hex.Matrix.instDecidableIndependent (b : Matrix Int n m) : Decidable (independent b) :=
  inferInstanceAs (Decidable (GramSchmidt.Int.independent b))

end Matrix

namespace Internal

open Hex.Matrix









end Internal

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
The pure integer-arithmetic LLL reducer. `LLLState` carries only the
integer basis, scaled Gram-Schmidt coefficients `ν`, and Gram
determinants `d`; `lllNative` runs the fuel-bounded `d`/`ν` loop, the
trusted exact reducer at the classical `η = 1/2`.
-/

namespace Hex

namespace Internal

/-- Integer-only state for later LLL reduction steps. The proof-facing fields
connect the stored Gram determinants and scaled coefficients to the executable
Gram-Schmidt integer data for `b`. -/
structure LLLState (n m : Nat) where
  /-- The current integer basis, as a matrix of row vectors. -/
  b : Matrix Int n m
  /-- The integer scaled Gram-Schmidt coefficients of `b`. -/
  ν : Matrix Int n n
  /-- The leading Gram determinants of `b` (`d[k]` for `k ≤ n`). -/
  d : Vector Nat (n + 1)

namespace LLLState

/-- Correctness predicate for the proof-facing interpretation of an executable
`LLLState`. Keeping this separate lets executable state updates remain purely
computational; Mathlib-side modules can prove preservation when they need the
Gram-Schmidt interpretation. -/
structure Valid (s : LLLState n m) : Prop where
  /-- Each below-diagonal `ν` entry equals the executable scaled Gram-Schmidt
  coefficient of `s.b`. -/
  ν_eq : ∀ i j, (hi : i < n) → (hj : j < n) → j < i →
      (s.ν.getRow ⟨i, hi⟩).get ⟨j, hj⟩ =
        ((GramSchmidt.Int.scaledCoeffs s.b).getRow ⟨i, hi⟩).get ⟨j, hj⟩
  /-- Each `d` entry equals the corresponding leading Gram determinant of
  `s.b`. -/
  d_eq : ∀ i, (hi : i < n + 1) →
      s.d.get ⟨i, hi⟩ = GramSchmidt.Int.gramDet s.b i (Nat.le_of_lt_succ hi)

/-- Integer nearest-quotient used by the LLL size-reduction test. -/
@[expose]
def nearestQuotient (νjk : Int) (dj1 : Nat) : Int :=
  Int.fdiv (2 * νjk + Int.ofNat dj1) (2 * Int.ofNat dj1)

/-- Targeted matrix entry update for LLL's integer coefficient state.

Uses `Vector.modify` rather than `M.set i ((M.get i).set j x)` so the
underlying `Array.modify` swap-with-placeholder runs the inner row update
in place when `M` is uniquely owned, avoiding the forced row copy that
`set i (… set j …)` triggers via a `lean_inc` on the borrowed row. -/
@[expose]
def setEntry (M : Matrix Int n n) (i j : Fin n) (x : Int) : Matrix Int n n :=
  M.modifyRow i (·.set j x)





/-- Single-column size reduction update for row `k` against row `j`. -/
@[expose]
def sizeReduceColumn (s : LLLState n m) (j k : Fin n) (hjk : j.val < k.val) :
    LLLState n m :=
  let νjk := (s.ν.getRow k).get j
  let dj1 := s.d.get ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  if hreduce : 2 * Int.natAbs νjk > dj1 then
    let r := nearestQuotient νjk dj1
    let b' := GramSchmidt.Int.sizeReduce s.b j k r
    let rowK :=
      Fin.foldl j.val
        (fun row l =>
          let lFin : Fin n := ⟨l.val, Nat.lt_trans l.isLt j.isLt⟩
          row.set lFin ((s.ν.getRow k).get lFin - r * (s.ν.getRow j).get lFin))
        (s.ν.getRow k)
    let rowK := rowK.set j ((s.ν.getRow k).get j - r * Int.ofNat dj1)
    let ν' : Matrix Int n n :=
      s.ν.setRow k rowK
    { b := b'
      ν := ν'
      d := s.d }
  else
    s

/-- Size-reduce row `k` against each earlier row using the stored integer
scaled coefficients. -/
@[expose]
def sizeReduce (s : LLLState n m) (k : Nat) : LLLState n m :=
  if hk : k < n then
    let kFin : Fin n := ⟨k, hk⟩
    Fin.foldr k
      (fun j state =>
        let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt hk⟩
        LLLState.sizeReduceColumn state jFin kFin j.isLt)
      s
  else
    s









/-- Swap adjacent rows `k - 1` and `k`, updating the stored scaled coefficients
and Gram determinants with the integer formulas from the LLL specification. -/
@[expose]
def swapStep (s : LLLState n m) (k : Nat) : LLLState n m :=
  if hk : k < n then
    if hk0 : 0 < k then
      let kFin : Fin n := ⟨k, hk⟩
      let km1 : Fin n := GramSchmidt.prevRow kFin hk0
      let B := (s.ν.getRow kFin).get km1
      let dkPrev := s.d.get ⟨km1.val, Nat.lt_succ_of_lt km1.isLt⟩
      let dk := s.d.get ⟨k, Nat.lt_succ_of_lt hk⟩
      let dkNext := s.d.get ⟨k + 1, Nat.succ_lt_succ hk⟩
      let dk' : Nat :=
        Int.toNat (((Int.ofNat dkNext * Int.ofNat dkPrev + B ^ 2) / Int.ofNat dk))
      let b' := GramSchmidt.Int.adjacentSwap s.b kFin hk0
      let d' : Vector Nat (n + 1) :=
        s.d.set k dk' (h := Nat.lt_succ_of_lt hk)
      let νRowsSwapped :=
        let setPrefixFrom (source : Vector Int n) (row : Vector Int n) : Vector Int n :=
          Fin.foldl km1.val
            (fun row j =>
              let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt km1.isLt⟩
              row.set jFin (source.get jFin))
            row
        s.ν.modifyRow km1 (setPrefixFrom (s.ν.getRow kFin))
          |>.modifyRow kFin (setPrefixFrom (s.ν.getRow km1))
      let νPivot := setEntry νRowsSwapped kFin km1 B
      -- Hoist (oldNu[i].kFin, oldNu[i].km1) reads out of the foldl lambda
      -- so the closure does not hold a reference to s.ν across iterations.
      -- With s.ν kept alive only for this precompute, the row-level rc on
      -- post-pivot rows drops to 1 by the time `ν.modifyRow i` runs, letting
      -- the two-`set` body inside the modify mutate in place instead of
      -- COW'ing the row on every iteration.
      let pairs : Vector (Int × Int) n :=
        Vector.ofFn fun i =>
          if _ : k < i.val then ((s.ν.getRow i).get kFin, (s.ν.getRow i).get km1)
          else (0, 0)
      let ν' : Matrix Int n n :=
        Fin.foldl n
          (fun ν i =>
            if _ : k < i.val then
              let (a, b) := pairs.get i
              let prev := (Int.ofNat dkPrev * a + B * b) / Int.ofNat dk
              let curr := (Int.ofNat dkNext * b - B * a) / Int.ofNat dk
              ν.modifyRow i fun row =>
                row.set km1 prev
                  |>.set kFin curr
            else
              ν)
          νPivot
      { b := b'
        ν := ν'
        d := d' }
    else
      s
  else
    s



















/-- The multiplicative potential used by the LLL termination argument:
`d₁ * ... * dₙ₋₁`. -/
@[expose]
def potential (s : LLLState n m) : Nat :=
  Fin.foldl (n - 1)
    (fun acc i =>
      acc * s.d.get
        ⟨i.val + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1))⟩)
    1



/-- Initial `LLLState` constructor: build the integer state directly from a
basis matrix. The `ν` field is the integral scaled Gram-Schmidt coefficient
matrix and the `d` field is the leading Gram-determinant vector.

Takes no independence hypothesis: the construction is purely executable, and the
resulting state is even `Valid` unconditionally (see
`HexLLLTheory.LLLState.ofBasis_valid`). `b.independent` enters only in the
theorems about the reducer's *output* (`lllNative_isLLLReduced` and the
short-vector bounds), never in building the state. Mathlib-free callers
(benchmarks, fixture emitters, BHKS projected-row computation) use it directly. -/
@[expose]
def ofBasis (b : Matrix Int n m) : LLLState n m :=
  let gs := GramSchmidt.Int.data b
  { b
    ν := gs.ν
    d := gs.d }

end LLLState

/-- Fuel-bounded outer LLL loop, selected by `lllAux`.

At row `k`, the loop size-reduces the current row, checks the integer
Lovasz condition, and either advances to `k + 1` or swaps adjacent rows and
continues from the previous position.

The `fuel = 0` branch returns the current basis as a total fallback.
The fuel-sufficiency theorem proves that `lllFuel` reaches the completed state
for valid independent inputs used by the public computation. -/
@[expose]
def lllLoop (s : LLLState n m) (k : Nat) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hk : 1 ≤ k) (hkn : k ≤ n) :
    Nat → Matrix Int n m
  | 0 =>
      s.b
  | fuel + 1 =>
      if hdone : k = n then
        s.b
      else
        have hlt : k < n := Nat.lt_of_le_of_ne hkn hdone
        have hkm1lt : k - 1 < n :=
          Nat.lt_of_le_of_lt (Nat.sub_le k 1) hlt
        let sReduced := s.sizeReduce k
        let kFin : Fin n := ⟨k, hlt⟩
        let km1Fin : Fin n := ⟨k - 1, hkm1lt⟩
        let dkPrev := sReduced.d.get
          ⟨k - 1, Nat.lt_trans hkm1lt (Nat.lt_succ_self n)⟩
        let dk := sReduced.d.get ⟨k, Nat.lt_succ_of_lt hlt⟩
        let dkNext := sReduced.d.get ⟨k + 1, Nat.succ_lt_succ hlt⟩
        let B := (sReduced.ν.getRow kFin).get km1Fin
        let lovaszLhs : Int :=
          Int.ofNat δ.den * (Int.ofNat dkNext * Int.ofNat dkPrev + B ^ 2)
        let lovaszRhs : Int :=
          δ.num * (Int.ofNat dk ^ 2)
        if lovaszLhs ≥ lovaszRhs then
          lllLoop sReduced (k + 1) δ hδ hδ' (Nat.succ_pos k) (Nat.succ_le_of_lt hlt) fuel
        else
          let sSwapped := sReduced.swapStep k
          let k' := max (k - 1) 1
          lllLoop sSwapped k' δ hδ hδ' (Nat.le_max_right (k - 1) 1)
            (by
              exact (Nat.max_le).2
                ⟨Nat.le_trans (Nat.sub_le k 1) hkn, Nat.le_trans hk hkn⟩)
            fuel







end Internal

open Hex.Internal



namespace Internal



end Internal

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
The `(δ, η)`-reducedness predicate `isLLLReduced` and the short-vector
bound `short_vector_bound_of_size_bound`: a reduced independent basis has
a first row no longer than `(1 / (δ - η²)) ^ (n - 1)` (squared) times any
nonzero lattice vector.
-/

namespace Hex

namespace Internal.LLLCore

/-- Recover the squared norm of a Gram-Schmidt basis vector. -/
@[expose]
def basisNormSq (basis : Matrix Rat n m) (i : Fin n) : Rat :=
  (basis.row i).normSq



end Internal.LLLCore

open Hex.Internal

/-- A basis is `(δ, η)`-LLL-reduced when it is size-reduced with bound `η`
(`|μ| ≤ η` for every below-diagonal entry of the Gram-Schmidt coefficient
matrix) and satisfies the Lovasz condition at every adjacent pair. The
size-reduction clause is stored in squared form `μ² ≤ η²`, which is equivalent
to `|μ| ≤ η` exactly when `η ≥ 0`; every consumer supplies `1/2 ≤ η`. -/
@[expose]
def isLLLReduced (b : Matrix Int n m) (δ η : Rat) : Prop :=
  let basis := GramSchmidt.Int.basis b
  let coeffs := GramSchmidt.Int.coeffs b
  (∀ i j, (hi : i < n) → (hji : j < i) →
      let iFin : Fin n := ⟨i, hi⟩
      let jFin : Fin n := ⟨j, Nat.lt_trans hji hi⟩
      let μ := coeffs[iFin][jFin]
      μ * μ ≤ η * η) ∧
    ∀ i, (hi : i + 1 < n) →
      let iFin : Fin n := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
      let ip1Fin : Fin n := ⟨i + 1, hi⟩
      let μ := coeffs[ip1Fin][iFin]
      δ * LLLCore.basisNormSq basis iFin ≤
        LLLCore.basisNormSq basis ip1Fin + μ * μ * LLLCore.basisNormSq basis iFin

namespace Internal.LLLCore





























end Internal.LLLCore



namespace Internal



end Internal

end Hex

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end


