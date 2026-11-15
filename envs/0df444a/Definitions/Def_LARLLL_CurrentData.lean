-- Prove2me | Definitions.Def_LARLLL_CurrentData
-- name    : LARLLL_CurrentData
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T02:48:48.687295+00:00
-- url     : https://prove2.me/theorems/3ffc9c07-8f11-44cc-95af-a32abba342c4
-- title:
--   The concrete logarithmic-fuel LLL algorithm and original-basis interface
-- statement:
--   The concrete LLL algorithm with logarithmic-potential fuel, its input conversion and original column-basis output, and the exact data used by the existing fuel, lattice-preservation, and basis-quality proofs. This bundle does not claim polynomial intermediate arithmetic height or a complete bit-PPT implementation.
-- source:
--   Apache-2.0 leanprover/hex source and the already checked native LLL adapters. Exact original module locations and SHA-256 values are recorded in the validation receipt. Whole original declaration commands were retained using the official Lean declaration/sketch and structural syntax oracles, with original notices, checked computational definitions, and csimp proof logic preserved. All retained declaration types and safe non-theorem values were compared to the original environment using kernel-checked reflexivity after expanding safe generated implementation helpers. Source SHA-256: 34ebc50cc2c27e11572d3115e3d66cf4f965f4070144421d4de6e8c31f975c5f.

import Definitions.Def_LARLLL_GramSchmidtRefinement

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/




namespace Hex.Internal
end Hex.Internal






set_option autoImplicit true



section
set_option maxHeartbeats 1600000

/-!
Invariants of the executable LLL reducers. The per-step
`Valid`/independence preservation, the potential strict-decrease and fuel
sufficiency, and the loop-invariant induction culminate in the reducedness,
lattice, and rational short-vector theorems for `Hex.lllNative` and
`Hex.lll`.
-/



namespace Hex

open Hex.Internal

namespace Matrix



end Matrix

namespace Internal.LLLState







/-- Inner foldl in `swapStep`'s `setPrefixFrom`: setting positions `0..km1-1` of a
row to `source[·]`. -/
 def _root_.Hex.Internal.LLLState.setPrefix (source row : Vector Int n) (km1 : Fin n) : Vector Int n :=
  Fin.foldl km1.val
    (fun row j =>
      let jFin : Fin n := ⟨j.val, Nat.lt_trans j.isLt km1.isLt⟩
      row.set jFin (source.get jFin))
    row

















/-! # Prefix LLL invariants under `swapStep`

For row indices strictly below `k - 1`, both the Gram-Schmidt basis row and
the rational coefficient entries are preserved by `swapStep s k`, because
the swap only touches rows `k - 1` and `k`. These prefix lemmas package
that observation as the building blocks for the `prefixLLLReduced`
preservation corollary below. -/





end Internal.LLLState

/-- The prefix `δ`-LLL-reduced predicate: the first `k` Gram-Schmidt rows
satisfy size reduction (for all `i < k`, `j < i`) and the adjacent Lovász
condition at `(i, i + 1)` (for all `i + 1 < k`). At `k = n` this coincides
with `isLLLReduced`; at `k ≤ 1` it is vacuously true. -/
@[expose]
def prefixLLLReduced (b : Matrix Int n m) (k : Nat) (δ : Rat) : Prop :=
  let basis := GramSchmidt.Int.basis b
  let coeffs := GramSchmidt.Int.coeffs b
  (∀ i j, (hik : i < k) → (hin : i < n) → (hji : j < i) →
      let iFin : Fin n := ⟨i, hin⟩
      let jFin : Fin n := ⟨j, Nat.lt_trans hji hin⟩
      let μ := coeffs[iFin][jFin]
      4 * μ * μ ≤ 1) ∧
    ∀ i, (hik : i + 1 < k) → (hin : i + 1 < n) →
      let iFin : Fin n := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hin⟩
      let ip1Fin : Fin n := ⟨i + 1, hin⟩
      let μ := coeffs[ip1Fin][iFin]
      δ * LLLCore.basisNormSq basis iFin ≤
        LLLCore.basisNormSq basis ip1Fin + μ * μ * LLLCore.basisNormSq basis iFin









namespace Internal.LLLState



/-! # Size-reduce Valid preservation

The single-column update `sizeReduceColumn` edits `b`, `ν` at row `k`,
and leaves `d` alone.  Validity is preserved because the integer
`(b, ν)` update mirrors the Mathlib-side `scaledCoeffs` updates
(`scaledCoeffs_sizeReduce_pivot`/`_lower`/`_above_pivot`/`_other_row`)
and the Gram-determinants are unchanged (`gramDet_sizeReduce`). -/













/-! # Size-reduce size-reducedness

After `LLLState.sizeReduce s k`, the row `k` of the integer scaled coefficients
satisfies `2 * |ν[k][j]| ≤ d[j+1]` for every `j < k` (the integer formulation
of the rational size-reducedness bound `|μ[k][j]| ≤ 1/2`).  Pair with
`scaledCoeffs_eq` to get the rational bound `4 * μ[k][j]² ≤ 1` on the
post-reduction Gram-Schmidt coefficients.  Closes the size-reduction half of
the LLL loop invariant. -/























/-! # Potential strict-decrease under failing Lovász

These lemmas package the multiplicative termination potential
`d_1 · … · d_{n-1}` behaviour under the two inner-loop updates:

* `sizeReduce_potential`: size reduction is potential-neutral (it only
  edits `ν`, never `d`).
* `swapStep_d_pivot`: the post-swap Gram-determinant slot reads
  `Int.toNat ⌊(d_{k+1}·d_{k-1} + B²)/d_k⌋` directly off `swapStep`'s
  definition (pairs with `swapStep_d_eq` to identify this slot with
  `gramDet (adjacentSwap b k) k`).
* `swapStep_potential_lt`: when the integer Lovász test fails at row
  `k` (the swap branch of `lllLoop`), the potential strictly decreases.
-/















/-! # Fuel sufficiency for `lllLoop`

The outer LLL loop `lllLoop` is total by structural recursion on a `fuel`
argument, with `fuel = 0` returning the current basis. This section
proves the fallback unreachable for valid input: the bound
`lllFuel s = (s.potential + 1) * (n + 1)` is sufficient for the loop
started at `k = 1` on `s = ofBasis b`.

The argument tracks the lexicographic measure
`s.potential * (n + 1) + (n - k)`:

* size reduction is potential-neutral (`sizeReduce_potential`) and is
  immediately followed by either an advance (decreases `n - k` by 1)
  or a swap;
* swaps strictly decrease the potential (`swapStep_potential_lt`),
  swallowing the `n - k` reset.

So each loop iteration strictly decreases the measure by ≥ 1, and the
measure starts strictly below `lllFuel s`, so the loop hits the
`k = n` base case before fuel exhausts.
-/



/-- The inner body of `lllLoop`'s `fuel = g + 1` branch (under `k < n`),
extracted for use in fuel-sufficiency reasoning. -/
def lllLoopBody (s : LLLState n m) (k : Nat) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hlt : k < n) (fuel : Nat) : Matrix Int n m :=
  let sReduced := s.sizeReduce k
  let kFin : Fin n := ⟨k, hlt⟩
  let km1Fin : Fin n := ⟨k - 1, Nat.lt_of_le_of_lt (Nat.sub_le k 1) hlt⟩
  let dkPrev := sReduced.d.get
    ⟨k - 1, Nat.lt_trans
      (Nat.lt_of_le_of_lt (Nat.sub_le k 1) hlt) (Nat.lt_succ_self n)⟩
  let dk := sReduced.d.get ⟨k, Nat.lt_succ_of_lt hlt⟩
  let dkNext := sReduced.d.get ⟨k + 1, Nat.succ_lt_succ hlt⟩
  let B := (sReduced.ν.getRow kFin).get km1Fin
  let lovaszLhs : Int :=
    Int.ofNat δ.den * (Int.ofNat dkNext * Int.ofNat dkPrev + B ^ 2)
  let lovaszRhs : Int := δ.num * (Int.ofNat dk ^ 2)
  if lovaszLhs ≥ lovaszRhs then
    lllLoop sReduced (k + 1) δ hδ hδ' (Nat.succ_pos k)
      (Nat.succ_le_of_lt hlt) fuel
  else
    let sSwapped := sReduced.swapStep k
    let k' := max (k - 1) 1
    lllLoop sSwapped k' δ hδ hδ' (Nat.le_max_right (k - 1) 1)
      ((Nat.max_le).2 ⟨Nat.le_trans (Nat.sub_le k 1) hkn, Nat.le_trans hk hkn⟩)
      fuel









/-! # Size-reduce coefficient-row preservation

Size reduction at row `k` rewrites only that row's coefficients; rows at
indices `i ≠ k` are preserved by every iteration of the inner foldl.  This
packages the preservation as a single statement so the loop-invariant proof
below can quote it without re-running the inductive `coeffs_sizeReduce_other_row`
chain. -/









/-! # Loop invariant induction

The `prefixLLLReduced` predicate is preserved by every iteration of `lllLoop`
under the standard validity / independence hypotheses, and at the `k = n`
base case it coincides with `isLLLReduced`. This packages those two facts
into a single fuel-bounded induction. -/





end Internal.LLLState

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
Released under Apache 2.0 license as described in Solutions/RegevBridgeNativeLLLVendor/LICENSE.
Authors: Kim Morrison
Modifications: strengthen the checked swap inequality to the 3/4 contraction.
-/




set_option autoImplicit true



set_option maxHeartbeats 1600000


namespace Hex
open Hex.Internal
namespace Internal.LLLState


















/-- A natural-valued measure with O(log potential) magnitude. -/
def logPotential (s : LLLState n m) : Nat := (s.potential ^ 3).log2 + 1





end Internal.LLLState
end Hex

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in Solutions/RegevBridgeNativeLLLVendor/LICENSE.
Authors: Kim Morrison
Modifications: logarithmic potential replaces numerical-potential fuel.
-/


set_option autoImplicit true



set_option maxHeartbeats 1600000
namespace Hex
open Hex.Internal
namespace Internal.LLLState



/-- The number of loop iterations is logarithmic in the initial potential. -/
def logarithmicFuel (s : LLLState n m) : Nat := (s.logPotential + 1) * (n + 1)



end Internal.LLLState
end Hex

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/









set_option autoImplicit true



section
set_option maxHeartbeats 1600000

/-!
The integer row lattice as a
`Submodule ℤ`, its identification with `Hex.Matrix.memLattice`, the
`EuclideanSpace` embeddings with their norm transport, and the conditional
Euclidean short-vector bound for an already-reduced basis.
-/

namespace HexLLLTheory

















/-- View an executable integer row as a vector in Mathlib's standard Euclidean
space on `Fin m`. -/
@[expose]
def intRowToEuclidean (row : Vector Int m) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun j : Fin m => (row[j] : ℝ))











end HexLLLTheory

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section




set_option autoImplicit true



set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.NativeLLL
open Hex.Internal
open scoped BigOperators
variable {n m : Nat}

/-- Exact integer LLL with a logarithmic, rather than numerical, potential budget. -/
def current (b : Hex.Matrix Int n m) : Hex.Matrix Int n m :=
  if hn : 1 ≤ n then
    lllLoop (LLLState.ofBasis b) 1 (3 / 4) (by norm_num) (by norm_num)
      (Nat.le_refl 1) hn (LLLState.ofBasis b).logarithmicFuel
  else b







/-- Original column-basis convention, transported without changing any entries. -/
def input (B : Matrix (Fin n) (Fin n) ℤ) : Hex.Matrix Int n n :=
  Hex.Matrix.ofFn fun i j => B j i

def basis (B : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  (HexMatrixTheory.matrixEquiv (current (input B))).transpose







end InfoLossLAR.WorstCase.NativeLLL

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/






set_option autoImplicit true



section
set_option maxHeartbeats 1600000

/-!
Mathlib-side correspondence lemmas for `hex-gram-schmidt`.

This module converts dense `Hex.Matrix` rows into the finite-dimensional real
vector space used by Mathlib's `gramSchmidt`, then states the rowwise
correspondence between the executable `Hex.GramSchmidt` basis and Mathlib's
orthogonalization process.
-/

namespace Hex
namespace GramSchmidtTheory

/-- View a rational dense row as a vector in Mathlib's standard Euclidean
space on `Fin m`. -/
@[expose]
def rowToEuclidean (row : Vector Rat m) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun j : Fin m => (row[j] : ℝ))











/-- Cast an integer dense matrix into the rational matrix space of `HexGramSchmidt`. -/
@[expose]
def castIntMatrix (b : Matrix Int n m) : Matrix Rat n m :=
  Hex.Matrix.ofRows (b.rows.map (fun row => row.map (fun x : Int => (x : Rat))))

/-- The row family fed to Mathlib's `gramSchmidt` for a rational matrix. -/
@[expose]
def ratRowFamily (b : Matrix Rat n m) : Fin n → EuclideanSpace ℝ (Fin m) :=
  fun i => rowToEuclidean (b.row i)

/-- The row family fed to Mathlib's `gramSchmidt` for an integer matrix. -/
@[expose]
def intRowFamily (b : Matrix Int n m) : Fin n → EuclideanSpace ℝ (Fin m) :=
  ratRowFamily (castIntMatrix b)

















end GramSchmidtTheory
end Hex

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section



set_option autoImplicit true



set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.NativeLLL
open Hex.Internal
open scoped BigOperators
variable {n m : Nat}

/-- Full unnormalized Gram-Schmidt vector of the actual native basis. -/
noncomputable def gsRow (b : Hex.Matrix Int n m) (i : Fin n) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun j => ((Hex.GramSchmidt.Int.basis b).row i)[j]



def lastIndex (hn : 0 < n) : Fin n := ⟨n-1,Nat.sub_lt hn (by decide)⟩

noncomputable def lastGS (B : Matrix (Fin n) (Fin n) ℤ) (hn : 0 < n) : EuclideanSpace ℝ (Fin n) :=
  gsRow (current (input B)) (lastIndex hn)












end InfoLossLAR.WorstCase.NativeLLL

end

section

namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace OAI.MetricKMedian.Binary
end OAI.MetricKMedian.Binary


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open AFT.RationalNumerics
open scoped BigOperators

def integerTicks (value : ℤ) : List Unit := List.replicate 3 ()++value.natAbs.bits.map (fun _ => ())


def integerVectorTicks (vector : List ℤ) : List Unit :=
  vector.flatMap (fun value => integerTicks value++integerTicks value++[()])


def integerMatrixTicks (matrix : List (List ℤ)) : List Unit :=
  matrix.flatMap (fun vector => integerVectorTicks vector++integerVectorTicks vector++[()])

































noncomputable section




def inputColumns {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) : List (List ℤ) :=
  List.ofFn (fun column => List.ofFn (fun row => basis row column))














end
end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end

section

namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace InfoLossLAR.WorstCase.RationalGramSchmidt
end InfoLossLAR.WorstCase.RationalGramSchmidt
namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native
end InfoLossLAR.WorstCase.RationalGramSchmidt.Native
namespace OAI.MetricKMedian.Binary
end OAI.MetricKMedian.Binary


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
namespace InfoLossLAR.WorstCase.RationalInverse.Native
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open AFT.RationalNumerics
open RationalGramSchmidt
open RationalGramSchmidt.Native
open scoped BigOperators
noncomputable section


















def inputRows {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : List (List ℤ) :=
  List.ofFn (fun row => List.ofFn (fun col => B row col))













end
end InfoLossLAR.WorstCase.RationalInverse.Native

end


