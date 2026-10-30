-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44
-- name    : QAlgorithms_Papers_Independent_Extend50_P44
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T23:06:11.593227+00:00
-- url     : https://prove2.me/theorems/0c6512fd-3bbb-408b-a0e4-1dde46c63418
-- title:
--   Definitions for Block-encoding structured matrices for data input in quantum computing
-- statement:
--   The objects the formalized statements of *Block-encoding structured matrices for data input in quantum computing* (arXiv:2302.10949) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `tableMax`: PDF pp.5,7: the maximum magnitude of a supplied table (zero for an empty table).
--   - `supportedPower`: PDF p.8: supported powers, with zero padding excluded even at exponent zero.
--   - `prepAlpha`: PDF p.10, (32): PREP normalization, using the actual supported data count D.
--   - `matrixMax`: PDF p.8, (18): maximum entry magnitude, with a defined empty-matrix value.
--   - `withFlags`: PDF pp.5-7: an oracle acts trivially on the flag register. The accepted square permutation matrix is evaluated at the relabelled input, which also covers distinct source and target register types.
--   - `dataRotation`: PDF p.5, (7)-(8): RX(2 arccos q), with its negative imaginary off-diagonal.
--   - `Scheme`: PDF pp.5-7: full reversible oracle data, uniform preparation completions, actual supported sparsity states, and injective enumeration of structural entries. Dimensions are physical powers of two; equality of total bit counts is explicit. No block-encoding identity or circuit-cost bound is assumed here.
--   - `Scheme.matrix`: PDF pp.5-7: the matrix specified by the label pattern and supplied data. The injectivity in Scheme rules out counting a structural entry more than once.
--   - `Scheme.baseAlpha`: PDF pp.6-7: the base normalization uses supported sparsities, not padded S.
--   - `diffusion`: PDF pp.6-7: lift a sparsity diffusion, preserving flags and matrix indices.
--   - `Scheme.baseMiddle`: PDF p.7, (14)-(16): the middle multiplexed rotation and range-controlled NOT. When hermitian=true, the Z of (36) acts first on the input data flag.
--   - `Scheme.baseCircuit`: PDF p.7, (16), and p.11, (36): the actual five-stage base circuit, reassociated so that all flags precede the matrix register.
--   - `Scheme.simpleCircuit`: PDF p.6, (11): the introductory circuit has no deletion flag.
--   - `Scheme.splitCircuit`: PDF p.8, (19): two separate data flags, with the same middle range test.
--   - `loadingCost`: PDF pp.7,10: a loading schedule lists the table slots read at each loading stage. The base word contains one table rotation; the split and PREP words contain two. This metric does not count arithmetic gates or synthesis precision.
--   - `baseLoadingSchedule`: PDF pp.5,7: the base circuit's single table oracle.
--   - `doubleLoadingSchedule`: PDF pp.8,10: two separately loaded data tables.
--   - `TransposeOracle`: PDF p.11, (35): transpose is an involution on every label and preserves the data index and the range predicate, including on invalid labels.
--   - `zeroEncoding`: PDF pp.2,5: for the zero matrix use a flag X and alpha=1, rather than normalizing a zero data table. This definition is independent of all divisions.
--   - `PrepLayout`: PDF p.10, (31): compatible physical tensor factors. The active D labels need not fill their binary register. Supports factor as D times the supported residual sparsity. Data labels are preserved by both full arithmetic oracles; this is the source's commutativity prerequisite, including all padding.
--   - `PrepLayout.alpha`: PDF pp.10-11, (32): supported physical data register with its actual D.
--   - `PreparationPair`: PDF p.10, (29)-(30): PREP column and UNPREP row, with normalized states and full unitary completions. This does not assume block-encoding correctness.
--   - `tensorPreparation`: PDF p.10, (31): a preparation acting on the data factor and residual factor.
--   - `PrepLayout.circuit`: PDF p.10, (31): PREP, the column/range/row oracles, then UNPREP. Only the range-deletion qubit is left besides the physical sparsity register.
--   - `signOracle`: PDF p.12, (38): the full Hermitian sign oracle. Zero/unused labels have sign +1, so that the completion is unitary and Hermitian on every label.
--   - `ArithmeticGate`: PDF pp.5,13-21: elementary reversible arithmetic gates X, CNOT, CCNOT. Controls and target are distinct. Swaps can be three CNOT gates.
--   - `ArithmeticGate.run`: Basis action of an elementary reversible arithmetic gate.
--   - `runArithmetic`: Arithmetic gates are performed in list order.
--   - `toffoliCount`: PDF pp.13-21: CCNOT count in the actual elementary arithmetic list.
--   - `bitAt`: Canonical most-significant-first bit, returning zero beyond the register.
--   - `pairBits`: Canonical binary encoding of two source registers, in their displayed order.
--   - `flaggedPairBits`: A leading Boolean flag followed by the two source registers.
--   - `doubleFlaggedPairBits`: Source-order encoding of the existing data and deletion flags followed by the label registers. They may be borrowed by arithmetic but must be restored on every basis input; they are not further clean work ancillas.
--   - `cleanBits`: Append clean work wires after a fixed physical binary encoding.
--   - `RealizesMap`: A cost-bearing reversible circuit implements a map on every basis input, returning every work wire to zero. Encodings are fixed, rather than chosen to make the map artificially cheap.
--   - `Scheme.ArithmeticCost`: PDF pp.7,14-21: implementations of the two label oracles and the range NOT. The bound is on their summed CCNOT count. Work is clean and not a flag.
--   - `Scheme.ArithmeticSize`: PDF p.21: all-gates count for the Laplacian arithmetic. Existing flags may be borrowed but are restored on all basis inputs, including junk inputs.
--   - `checkerboard`: PDF p.13, (40)-(44): the checkerboard entries, allowing signed data.
--   - `CheckerLabels`: PDF p.13, (41)-(42): the paper's checkerboard labels.
--   - `deletedCheckerboard`: PDF pp.13-14, (49): replace only the two specified corner entries by zero.
--   - `deleteCheckerCorners`: PDF p.14, (49): the same arithmetic permutations with two invalid labels.
--   - `bandedToeplitzSeed`: PDF p.14, (50)-(52): the diagonal seed for the accepted Toeplitz matrix. Seed address u represents signed offset u-(N-1); out-of-band diagonals are zero.
--   - `bandedToeplitz`: PDF p.14, (50): specialize the accepted full Toeplitz matrix to the paper's banded signed-offset data; no periodic wrap-around is introduced.
--   - `ToeplitzLabels`: PDF pp.14-15: the actual Toeplitz arithmetic and its overflow deletion.
--   - `triTable`: PDF pp.15-16, (57),(63): diagonal/off-diagonal data with the last table slot fixed to zero, rather than loaded as an independent real parameter.
--   - `tridiagonal`: PDF p.15, (57): symmetric tridiagonal matrix, including N=1 and N=2.
--   - `TridiagonalLabels`: PDF p.16, (58)-(62): the supported three labels are 00,01,11, not H4.
--   - `extendedTree`: PDF pp.17-18, (67): tree adjacency with the source's extra root edge 0--1, root/leaf diagonal a0, internal diagonal a1, and every edge a2.
--   - `treeTable`: PDF p.17: fourth physical data slot is a structural zero.
--   - `TreeLabels`: PDF pp.17-18, (69)-(74): range and row formulas. The two invalid edge labels m=0,N have reversible completions instead of undefined arithmetic.
--   - `laplacian`: PDF pp.19-20, (78): nonperiodic finite-difference Laplacian. The integer coordinate differences avoid truncated natural subtraction.
--   - `laplacianTable`: PDF p.19, (78): the three actual values and a fourth zero sentinel.
--   - `LaplacianLabels`: PDF pp.19-20, (80)-(84): five supported states and off-grid deletion.
--   - `PrepLayout.noDeleteCircuit`: PDF p.13, (45): when no range deletion is needed, remove that untouched flag from the PREP circuit, rather than counting an extra physical flag.
--   - `cliffordTSet`: PDF pp.25-26: the elementary Clifford+T gate set used for T counts. Arbitrary rotations are targets of approximation, not free gates in this set.
--   - `loaderTWord`: PDF pp.25-26: extract the T-cost instruction trace from a concrete Clifford+T circuit for the accepted single-qubit word counter. Each T or inverse-T instruction contributes one t; other gates contribute h and hence zero T count. This trace records cost only; Circuit.unitary retains the full gate semantics.
--   - `phaseGradient`: PDF p.26: a normalized reusable phase-gradient resource. Its preparation is separate from each invocation of the lookup/rotate/uncompute procedure.
--   - `loaderEmbedding`: PDF pp.25-26, (91): embed data flag and table index with the reusable gradient state and clean work. This specifies full output accuracy, including return of the resource and work, not only the selected data amplitude.
--   - `idealLoader`: PDF p.25, (89): the ideal multiplexed RX data loader on every data-flag input.
--   - `paddedTable`: PDF p.25: a non-power-of-two supplied data table is padded with known zeros in its minimal physical binary register. No new unknown item is loaded.
--   - `reverseCode`: PDF p.26, (94): the reverse map supplies an occurrence label, or the fixed zero sentinel for structural zeros. It is not inferred from forward maps.
--   - `valueAtLabel`: PDF p.26: finite b-bit data lookup, with no additional loaded zero value.
--   - `basisMatrix`: A basis-action matrix used for the reversible XOR compute/load steps.
--   - `entryCircuit`: PDF p.26, (94): compute the occurrence label, XOR the corresponding finite entry value, then uncompute the occurrence label. Buffer input is general.
--   - `rowColumnLabelBits`: PDF p.26: binary encoding for the reverse-map implementation; rows, columns, and occurrence workspace use the fixed displayed register order.
--   - `entryArithmeticCost`: PDF p.26: the arithmetic part of the three-stage word consists exactly of the given reverse-map circuit and its inverse, with no repetition of data.
-- source:
--   Block-encoding structured matrices for data input in quantum computing, arXiv:2302.10949v2, https://arxiv.org/abs/2302.10949v2

import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P11
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P23
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21

/-!
Statements from Sunderhauf, Campbell and Camps, arXiv:2302.10949v2.
All page numbers below are PDF page numbers. Rotations are ideal; arithmetic
oracles are reversible on the whole physical register, including padding.
Data loading counts table items, rather than elementary gates.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)
open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)
open QAlgorithms.Papers.Independent.Next46.P21 (tCount)

/-- PDF pp.5,7: the maximum magnitude of a supplied table (zero for an empty table). -/
def tableMax {D : ℕ} (a : Fin D → ℝ) : ℝ :=
  (List.ofFn fun d => |a d|).foldr max 0

/-- PDF p.8: supported powers, with zero padding excluded even at exponent zero. -/
def supportedPower (x p : ℝ) : ℝ :=
  if x = 0 then 0 else |x| ^ p

/-- PDF p.10, (32): PREP normalization, using the actual supported data count D. -/
def prepAlpha {D : ℕ} (a : Fin D → ℝ) (Sc Sr : ℕ) (p : ℝ) : ℝ :=
  Real.sqrt ((Sc : ℝ) * Sr) / D *
    Real.sqrt ((∑ d, supportedPower (a d) (2 * p)) *
      ∑ d, supportedPower (a d) (2 - 2 * p))

/-- PDF p.8, (18): maximum entry magnitude, with a defined empty-matrix value. -/
def matrixMax {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  (List.ofFn fun i => (List.ofFn fun j => |A i j|).foldr max 0).foldr max 0

/-- PDF pp.5-7: an oracle acts trivially on the flag register.
The accepted square permutation matrix is evaluated at the relabelled input,
which also covers distinct source and target register types. -/
def withFlags {F X Y : Type*} [DecidableEq F] [DecidableEq Y]
    (e : X ≃ Y) : Matrix (F × Y) (F × X) ℂ :=
  fun y x => if y.1 = x.1 then permutationMatrix (Equiv.refl Y) y.2 (e x.2) else 0

/-- Sanity check: the accepted permutation helper retains the relabelled basis entry. -/
example {X Y : Type*} [DecidableEq Y] (e : X ≃ Y) (x : X) :
    withFlags (F := Bool) e (false, e x) (false, x) = 1 := by
  simp [withFlags, QAlgorithms.Papers.Independent.Information100.P34.permutationMatrix]

/-- PDF p.5, (7)-(8): RX(2 arccos q), with its negative imaginary off-diagonal. -/
def dataRotation (q : ℝ) : Matrix Bool Bool ℂ :=
  fun b c => if b = c then (q : ℂ) else -Complex.I * (Real.sqrt (1 - q ^ 2) : ℂ)

/-- PDF pp.5-7: full reversible oracle data, uniform preparation completions,
actual supported sparsity states, and injective enumeration of structural entries.
Dimensions are physical powers of two; equality of total bit counts is explicit.
No block-encoding identity or circuit-cost bound is assumed here. -/
structure Scheme (n s d m : ℕ) where
  bit_balance : d + m = s + n
  column : (Fin (2 ^ d) × Fin (2 ^ m)) ≃ (Fin (2 ^ s) × Fin (2 ^ n))
  row : (Fin (2 ^ d) × Fin (2 ^ m)) ≃ (Fin (2 ^ s) × Fin (2 ^ n))
  valid : (Fin (2 ^ d) × Fin (2 ^ m)) → Bool
  columnSlots : Finset (Fin (2 ^ s))
  rowSlots : Finset (Fin (2 ^ s))
  column_nonempty : columnSlots.Nonempty
  row_nonempty : rowSlots.Nonempty
  column_range : ∀ l, valid l = true → (column l).1 ∈ columnSlots
  row_range : ∀ l, valid l = true → (row l).1 ∈ rowSlots
  positions_injective : ∀ l k, valid l = true → valid k = true →
    (column l).2 = (column k).2 → (row l).2 = (row k).2 → l = k
  Hc : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℂ
  Hr : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℂ
  Hc_unitary : Hc ∈ Matrix.unitaryGroup _ ℂ
  Hr_unitary : Hr ∈ Matrix.unitaryGroup _ ℂ
  Hc_zero : ∀ t, Hc t 0 = if t ∈ columnSlots then
    ((Real.sqrt (columnSlots.card : ℝ))⁻¹ : ℂ) else 0
  Hr_zero : ∀ t, Hr t 0 = if t ∈ rowSlots then
    ((Real.sqrt (rowSlots.card : ℝ))⁻¹ : ℂ) else 0

variable {n s d m : ℕ}

/-- PDF pp.5-7: the matrix specified by the label pattern and supplied data.
The injectivity in Scheme rules out counting a structural entry more than once. -/
def Scheme.matrix (B : Scheme n s d m) (a : Fin (2 ^ d) → ℝ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun i j => ∑ l : Fin (2 ^ d) × Fin (2 ^ m),
    if B.valid l = true ∧ (B.row l).2 = i ∧ (B.column l).2 = j then (a l.1 : ℂ) else 0

/-- PDF pp.6-7: the base normalization uses supported sparsities, not padded S. -/
def Scheme.baseAlpha (B : Scheme n s d m) (a : Fin (2 ^ d) → ℝ) : ℝ :=
  Real.sqrt ((B.columnSlots.card : ℝ) * B.rowSlots.card) * tableMax a

/-- PDF pp.6-7: lift a sparsity diffusion, preserving flags and matrix indices. -/
def diffusion {F : Type*} [DecidableEq F]
    (H : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℂ) :
    Matrix (F × (Fin (2 ^ s) × Fin (2 ^ n)))
      (F × (Fin (2 ^ s) × Fin (2 ^ n))) ℂ :=
  fun x y => if x.1 = y.1 ∧ x.2.2 = y.2.2 then H x.2.1 y.2.1 else 0

/-- PDF p.7, (14)-(16): the middle multiplexed rotation and range-controlled NOT.
When hermitian=true, the Z of (36) acts first on the input data flag. -/
def Scheme.baseMiddle (B : Scheme n s d m) (a : Fin (2 ^ d) → ℝ)
    (hermitian : Bool) :
    Matrix ((Bool × Bool) × (Fin (2 ^ d) × Fin (2 ^ m)))
      ((Bool × Bool) × (Fin (2 ^ d) × Fin (2 ^ m))) ℂ :=
  fun x y => if x.2 = y.2 ∧
      x.1.2 = (if B.valid y.2 then y.1.2 else !y.1.2) then
    dataRotation (a y.2.1 / tableMax a) x.1.1 y.1.1 *
      (if hermitian && y.1.1 then -1 else 1) else 0

/-- PDF p.7, (16), and p.11, (36): the actual five-stage base circuit,
reassociated so that all flags precede the matrix register. -/
def Scheme.baseCircuit (B : Scheme n s d m) (a : Fin (2 ^ d) → ℝ)
    (hermitian : Bool := false) :
    Matrix (((Bool × Bool) × Fin (2 ^ s)) × Fin (2 ^ n))
      (((Bool × Bool) × Fin (2 ^ s)) × Fin (2 ^ n)) ℂ :=
  let V := (diffusion (n := n) (F := Bool × Bool) B.Hr)ᴴ * withFlags (F := Bool × Bool) B.row *
    B.baseMiddle a hermitian * (withFlags (F := Bool × Bool) B.column)ᴴ * diffusion (n := n) (F := Bool × Bool) B.Hc
  fun x y => V (x.1.1, (x.1.2, x.2)) (y.1.1, (y.1.2, y.2))

/-- PDF p.6, (11): the introductory circuit has no deletion flag. -/
def Scheme.simpleCircuit (B : Scheme n s d m) (a : Fin (2 ^ d) → ℝ)
    (hermitian : Bool := false) :
    Matrix ((Bool × Fin (2 ^ s)) × Fin (2 ^ n))
      ((Bool × Fin (2 ^ s)) × Fin (2 ^ n)) ℂ :=
  let R : Matrix (Bool × (Fin (2 ^ d) × Fin (2 ^ m)))
      (Bool × (Fin (2 ^ d) × Fin (2 ^ m))) ℂ := fun x y =>
    if x.2 = y.2 then dataRotation (a y.2.1 / tableMax a) x.1 y.1 *
      (if hermitian && y.1 then -1 else 1) else 0
  let V := (diffusion (n := n) (F := Bool) B.Hr)ᴴ * withFlags (F := Bool) B.row * R *
    (withFlags (F := Bool) B.column)ᴴ * diffusion (n := n) (F := Bool) B.Hc
  fun x y => V (x.1.1, (x.1.2, x.2)) (y.1.1, (y.1.2, y.2))

/-- PDF p.8, (19): two separate data flags, with the same middle range test. -/
def Scheme.splitCircuit (B : Scheme n s d m) (a : Fin (2 ^ d) → ℝ) (p : ℝ) :
    Matrix (((Bool × Bool × Bool) × Fin (2 ^ s)) × Fin (2 ^ n))
      (((Bool × Bool × Bool) × Fin (2 ^ s)) × Fin (2 ^ n)) ℂ :=
  let R : Matrix ((Bool × Bool × Bool) × (Fin (2 ^ d) × Fin (2 ^ m)))
      ((Bool × Bool × Bool) × (Fin (2 ^ d) × Fin (2 ^ m))) ℂ := fun x y =>
    if x.2 = y.2 ∧ x.1.2.2 = (if B.valid y.2 then y.1.2.2 else !y.1.2.2) then
      dataRotation (Real.sign (a y.2.1) * supportedPower (a y.2.1) p /
        (tableMax a) ^ p) x.1.1 y.1.1 *
      dataRotation (supportedPower (a y.2.1) (1 - p) /
        (tableMax a) ^ (1 - p)) x.1.2.1 y.1.2.1 else 0
  let V := (diffusion (n := n) (F := Bool × Bool × Bool) B.Hr)ᴴ * withFlags (F := Bool × Bool × Bool) B.row * R *
    (withFlags (F := Bool × Bool × Bool) B.column)ᴴ * diffusion (n := n) (F := Bool × Bool × Bool) B.Hc
  fun x y => V (x.1.1, (x.1.2, x.2)) (y.1.1, (y.1.2, y.2))

/-- PDF pp.7,10: a loading schedule lists the table slots read at each loading stage.
The base word contains one table rotation; the split and PREP words contain two.
This metric does not count arithmetic gates or synthesis precision. -/
def loadingCost (schedule : List ℕ) : ℕ := schedule.sum

/-- PDF pp.5,7: the base circuit's single table oracle. -/
def baseLoadingSchedule (D : ℕ) : List ℕ := [D]

/-- PDF pp.8,10: two separately loaded data tables. -/
def doubleLoadingSchedule (D : ℕ) : List ℕ := [D, D]

/-- PDF p.11, (35): transpose is an involution on every label and preserves
the data index and the range predicate, including on invalid labels. -/
structure TransposeOracle (B : Scheme n s d m) where
  transpose : Equiv.Perm (Fin (2 ^ d) × Fin (2 ^ m))
  involutive : ∀ l, transpose (transpose l) = l
  data_preserved : ∀ l, (transpose l).1 = l.1
  valid_preserved : ∀ l, B.valid (transpose l) = B.valid l
  row_eq : ∀ l, B.row l = B.column (transpose l)
  diffusion_eq : B.Hr = B.Hc

/-- PDF pp.2,5: for the zero matrix use a flag X and alpha=1, rather than
normalizing a zero data table. This definition is independent of all divisions. -/
def zeroEncoding (N : ℕ) : Matrix (Bool × Fin N) (Bool × Fin N) ℂ :=
  fun x y => if x.1 = !y.1 ∧ x.2 = y.2 then 1 else 0

/-- The separate zero encoding has exactly zero selected block, even for N=0. -/
example (N : ℕ) (i j : Fin N) : zeroEncoding N (false, i) (false, j) = 0 := by
  simp [zeroEncoding]

/-- Small supported endpoint: a structural zero contributes no zeroth power. -/
example : supportedPower 0 0 = 0 := by simp [supportedPower]

/-- Small sign check for the ideal data rotation. -/
example : dataRotation (-1) false false = (-1 : ℂ) := by simp [dataRotation]

/-- Single table loading and two loading stages count their supplied items. -/
example : loadingCost (baseLoadingSchedule 3) = 3 ∧
    loadingCost (doubleLoadingSchedule 3) = 6 := by decide

/-- PDF p.10, (31): compatible physical tensor factors. The active D labels
need not fill their binary register. Supports factor as D times the supported
residual sparsity. Data labels are preserved by both full arithmetic oracles;
this is the source's commutativity prerequisite, including all padding. -/
structure PrepLayout (B : Scheme n s d m) where
  active : Finset (Fin (2 ^ d))
  active_nonempty : active.Nonempty
  kc : ℕ
  kr : ℕ
  factorColumn : Fin (2 ^ s) ≃ (Fin (2 ^ d) × Fin (2 ^ kc))
  factorRow : Fin (2 ^ s) ≃ (Fin (2 ^ d) × Fin (2 ^ kr))
  factorColumn_zero : factorColumn 0 = (0, 0)
  factorRow_zero : factorRow 0 = (0, 0)
  residualColumn : Finset (Fin (2 ^ kc))
  residualRow : Finset (Fin (2 ^ kr))
  residualColumn_nonempty : residualColumn.Nonempty
  residualRow_nonempty : residualRow.Nonempty
  column_support : ∀ t, t ∈ B.columnSlots ↔
    (factorColumn t).1 ∈ active ∧ (factorColumn t).2 ∈ residualColumn
  row_support : ∀ t, t ∈ B.rowSlots ↔
    (factorRow t).1 ∈ active ∧ (factorRow t).2 ∈ residualRow
  column_data : ∀ l, (factorColumn (B.column l).1).1 = l.1
  row_data : ∀ l, (factorRow (B.row l).1).1 = l.1
  Hcolumn : Matrix (Fin (2 ^ kc)) (Fin (2 ^ kc)) ℂ
  Hrow : Matrix (Fin (2 ^ kr)) (Fin (2 ^ kr)) ℂ
  Hcolumn_unitary : Hcolumn ∈ Matrix.unitaryGroup _ ℂ
  Hrow_unitary : Hrow ∈ Matrix.unitaryGroup _ ℂ
  Hcolumn_zero : ∀ t, Hcolumn t 0 = if t ∈ residualColumn then
    ((Real.sqrt (residualColumn.card : ℝ))⁻¹ : ℂ) else 0
  Hrow_zero : ∀ t, Hrow t 0 = if t ∈ residualRow then
    ((Real.sqrt (residualRow.card : ℝ))⁻¹ : ℂ) else 0

/-- PDF pp.10-11, (32): supported physical data register with its actual D. -/
def PrepLayout.alpha {B : Scheme n s d m} (L : PrepLayout B)
    (a : Fin (2 ^ d) → ℝ) (p : ℝ) : ℝ :=
  Real.sqrt ((B.columnSlots.card : ℝ) * B.rowSlots.card) / L.active.card *
    Real.sqrt ((∑ j ∈ L.active, supportedPower (a j) (2 * p)) *
      ∑ j ∈ L.active, supportedPower (a j) (2 - 2 * p))

/-- PDF p.10, (29)-(30): PREP column and UNPREP row, with normalized states
and full unitary completions. This does not assume block-encoding correctness. -/
structure PreparationPair {B : Scheme n s d m} (L : PrepLayout B)
    (a : Fin (2 ^ d) → ℝ) (p : ℝ) where
  prep : Matrix (Fin (2 ^ d)) (Fin (2 ^ d)) ℂ
  unprep : Matrix (Fin (2 ^ d)) (Fin (2 ^ d)) ℂ
  prep_unitary : prep ∈ Matrix.unitaryGroup _ ℂ
  unprep_unitary : unprep ∈ Matrix.unitaryGroup _ ℂ
  prep_zero : ∀ j, prep j 0 = if j ∈ L.active then
    ((Real.sign (a j) * supportedPower (a j) p /
      Real.sqrt (∑ k ∈ L.active, supportedPower (a k) (2 * p)) : ℝ) : ℂ) else 0
  unprep_zero : ∀ j, unprep 0 j = if j ∈ L.active then
    ((supportedPower (a j) (1 - p) /
      Real.sqrt (∑ k ∈ L.active, supportedPower (a k) (2 - 2 * p)) : ℝ) : ℂ) else 0

/-- PDF p.10, (31): a preparation acting on the data factor and residual factor. -/
def tensorPreparation {k : ℕ}
    (factor : Fin (2 ^ s) ≃ (Fin (2 ^ d) × Fin (2 ^ k)))
    (P : Matrix (Fin (2 ^ d)) (Fin (2 ^ d)) ℂ)
    (H : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℂ :=
  fun x y => P (factor x).1 (factor y).1 * H (factor x).2 (factor y).2

/-- PDF p.10, (31): PREP, the column/range/row oracles, then UNPREP.
Only the range-deletion qubit is left besides the physical sparsity register. -/
def PrepLayout.circuit {B : Scheme n s d m} (L : PrepLayout B)
    {a : Fin (2 ^ d) → ℝ} {p : ℝ} (P : PreparationPair L a p) :
    Matrix ((Bool × Fin (2 ^ s)) × Fin (2 ^ n))
      ((Bool × Fin (2 ^ s)) × Fin (2 ^ n)) ℂ :=
  let G : Matrix (Bool × (Fin (2 ^ d) × Fin (2 ^ m)))
      (Bool × (Fin (2 ^ d) × Fin (2 ^ m))) ℂ := fun x y =>
    if x.2 = y.2 ∧ x.1 = (if B.valid y.2 then y.1 else !y.1) then 1 else 0
  let V := diffusion (n := n) (F := Bool) (tensorPreparation L.factorRow P.unprep L.Hrowᴴ) *
    withFlags (F := Bool) B.row * G * (withFlags (F := Bool) B.column)ᴴ *
    diffusion (n := n) (F := Bool) (tensorPreparation L.factorColumn P.prep L.Hcolumn)
  fun x y => V (x.1.1, (x.1.2, x.2)) (y.1.1, (y.1.2, y.2))

/-- PDF p.12, (38): the full Hermitian sign oracle. Zero/unused labels
have sign +1, so that the completion is unitary and Hermitian on every label. -/
def signOracle (a : Fin (2 ^ d) → ℝ) : Matrix (Fin (2 ^ d)) (Fin (2 ^ d)) ℂ :=
  fun i j => if i = j then (if a i < 0 then -1 else 1) else 0

/-- One supported data item has normalization |a| independent of p. -/
example (a : Fin 1 → ℝ) (Sc Sr : ℕ) (p : ℝ) :
    prepAlpha a Sc Sr p = Real.sqrt ((Sc : ℝ) * Sr) *
      Real.sqrt (supportedPower (a 0) (2 * p) * supportedPower (a 0) (2 - 2 * p)) := by
  simp [prepAlpha]

/-- PDF pp.5,13-21: elementary reversible arithmetic gates X, CNOT, CCNOT.
Controls and target are distinct. Swaps can be three CNOT gates. -/
structure ArithmeticGate (w : ℕ) where
  target : Fin w
  controls : Finset (Fin w)
  target_not_control : target ∉ controls
  at_most_two : controls.card ≤ 2

/-- Basis action of an elementary reversible arithmetic gate. -/
def ArithmeticGate.run {w : ℕ} (g : ArithmeticGate w) (x : QAlgorithms.Qubits w) :
    QAlgorithms.Qubits w :=
  fun i => if i = g.target then Bool.xor (x i) (decide (∀ j ∈ g.controls, x j = true)) else x i

/-- Arithmetic gates are performed in list order. -/
def runArithmetic {w : ℕ} (c : List (ArithmeticGate w)) (x : QAlgorithms.Qubits w) :
    QAlgorithms.Qubits w := c.foldl (fun y g => g.run y) x

/-- PDF pp.13-21: CCNOT count in the actual elementary arithmetic list. -/
def toffoliCount {w : ℕ} (c : List (ArithmeticGate w)) : ℕ :=
  (c.map fun g => if g.controls.card = 2 then 1 else 0).sum

/-- Canonical most-significant-first bit, returning zero beyond the register. -/
def bitAt (w value k : ℕ) : Bool :=
  if h : k < w then QAlgorithms.natToBits w value ⟨k, h⟩ else false

/-- Canonical binary encoding of two source registers, in their displayed order. -/
def pairBits {u v : ℕ} (x : Fin (2 ^ u) × Fin (2 ^ v)) (k : ℕ) : Bool :=
  if k < u then bitAt u x.1 k else bitAt v x.2 (k - u)

/-- A leading Boolean flag followed by the two source registers. -/
def flaggedPairBits {u v : ℕ} (x : Bool × (Fin (2 ^ u) × Fin (2 ^ v))) (k : ℕ) : Bool :=
  if k = 0 then x.1 else pairBits x.2 (k - 1)

/-- Source-order encoding of the existing data and deletion flags followed
by the label registers. They may be borrowed by arithmetic but must be restored
on every basis input; they are not further clean work ancillas. -/
def doubleFlaggedPairBits {u v : ℕ}
    (x : (Bool × Bool) × (Fin (2 ^ u) × Fin (2 ^ v))) (k : ℕ) : Bool :=
  if k = 0 then x.1.1 else if k = 1 then x.1.2 else pairBits x.2 (k - 2)

/-- Append clean work wires after a fixed physical binary encoding. -/
def cleanBits {X : Type*} (encode : X → ℕ → Bool) (w work : ℕ) (x : X) :
    QAlgorithms.Qubits (w + work) :=
  fun i => if i.val < w then encode x i.val else false

/-- A cost-bearing reversible circuit implements a map on every basis input,
returning every work wire to zero. Encodings are fixed, rather than chosen to
make the map artificially cheap. -/
def RealizesMap {X Y : Type*} (input : X → ℕ → Bool) (output : Y → ℕ → Bool)
    (f : X → Y) (w work : ℕ) (c : List (ArithmeticGate (w + work))) : Prop :=
  ∀ x, runArithmetic c (cleanBits input w work x) = cleanBits output w work (f x)

/-- PDF pp.7,14-21: implementations of the two label oracles and the range
NOT. The bound is on their summed CCNOT count. Work is clean and not a flag. -/
def Scheme.ArithmeticCost (B : Scheme n s d m) (bound : ℝ) (work : ℕ) : Prop :=
  ∃ c r g : List (ArithmeticGate ((2 + (d + m)) + work)),
    RealizesMap doubleFlaggedPairBits doubleFlaggedPairBits
      (fun x : (Bool × Bool) × (Fin (2 ^ d) × Fin (2 ^ m)) => (x.1, B.column x.2))
      (2 + (d + m)) work c ∧
    RealizesMap doubleFlaggedPairBits doubleFlaggedPairBits
      (fun x : (Bool × Bool) × (Fin (2 ^ d) × Fin (2 ^ m)) => (x.1, B.row x.2))
      (2 + (d + m)) work r ∧
    RealizesMap doubleFlaggedPairBits doubleFlaggedPairBits
      (fun x : (Bool × Bool) × (Fin (2 ^ d) × Fin (2 ^ m)) =>
        ((x.1.1, if B.valid x.2 then x.1.2 else !x.1.2), x.2))
      (2 + (d + m)) work g ∧
    ((toffoliCount c + toffoliCount r + toffoliCount g : ℕ) : ℝ) ≤ bound

/-- PDF p.21: all-gates count for the Laplacian arithmetic. Existing flags
may be borrowed but are restored on all basis inputs, including junk inputs. -/
def Scheme.ArithmeticSize (B : Scheme n s d m) (bound : ℝ) (work : ℕ) : Prop :=
  ∃ c r g : List (ArithmeticGate ((2 + (d + m)) + work)),
    RealizesMap doubleFlaggedPairBits doubleFlaggedPairBits
      (fun x : (Bool × Bool) × (Fin (2 ^ d) × Fin (2 ^ m)) => (x.1, B.column x.2))
      (2 + (d + m)) work c ∧
    RealizesMap doubleFlaggedPairBits doubleFlaggedPairBits
      (fun x : (Bool × Bool) × (Fin (2 ^ d) × Fin (2 ^ m)) => (x.1, B.row x.2))
      (2 + (d + m)) work r ∧
    RealizesMap doubleFlaggedPairBits doubleFlaggedPairBits
      (fun x : (Bool × Bool) × (Fin (2 ^ d) × Fin (2 ^ m)) =>
        ((x.1.1, if B.valid x.2 then x.1.2 else !x.1.2), x.2))
      (2 + (d + m)) work g ∧
    ((c.length + r.length + g.length : ℕ) : ℝ) ≤ bound

/-- PDF p.13, (40)-(44): the checkerboard entries, allowing signed data. -/
def checkerboard (n : ℕ) (a : Fin 2 → ℝ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun i j => (a ⟨(i.val + j.val) % 2, Nat.mod_lt _ (by decide)⟩ : ℂ)

/-- PDF p.13, (41)-(42): the paper's checkerboard labels. -/
def CheckerLabels (B : Scheme n n 1 (2 * n - 1)) : Prop :=
  (∀ l, B.valid l = true) ∧ B.columnSlots = Finset.univ ∧ B.rowSlots = Finset.univ ∧
  ∀ l, (B.row l).2.val = l.2.val / (2 ^ n / 2) ∧
    (B.column l).2.val = 2 * (l.2.val % (2 ^ n / 2)) +
      (l.1.val + l.2.val / (2 ^ n / 2)) % 2

/-- PDF pp.13-14, (49): replace only the two specified corner entries by zero. -/
def deletedCheckerboard (n : ℕ) (a : Fin 2 → ℝ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun i j => if (i.val = 0 ∧ j.val = 0) ∨
      (i.val + 1 = 2 ^ n ∧ j.val + 1 = 2 ^ n) then 0 else checkerboard n a i j

/-- PDF p.14, (49): the same arithmetic permutations with two invalid labels. -/
def deleteCheckerCorners (B : Scheme n n 1 (2 * n - 1)) : Scheme n n 1 (2 * n - 1) :=
  { B with
    valid := fun l => B.valid l && !(decide (l.1.val = 0 ∧
      (l.2.val = 0 ∨ l.2.val + 1 = 2 ^ (2 * n - 1))))
    column_range := by
      intro l h
      simp only [Bool.and_eq_true_eq_eq_true_and_eq_true] at h
      exact B.column_range l h.1
    row_range := by
      intro l h
      simp only [Bool.and_eq_true_eq_eq_true_and_eq_true] at h
      exact B.row_range l h.1
    positions_injective := by
      intro l k hl hk hc hr
      simp only [Bool.and_eq_true_eq_eq_true_and_eq_true] at hl hk
      exact B.positions_injective l k hl.1 hk.1 hc hr }

/-- PDF p.14, (50)-(52): the diagonal seed for the accepted Toeplitz matrix.
Seed address u represents signed offset u-(N-1); out-of-band diagonals are zero. -/
def bandedToeplitzSeed (n d : ℕ) (k : Fin (2 ^ d)) (a : Fin (2 ^ d) → ℝ) :
    Fin (2 ^ n + 2 ^ n - 1) → ℂ :=
  fun u => ∑ t : Fin (2 ^ d),
    if (u.val : ℤ) - ((2 ^ n - 1 : ℕ) : ℤ) = (t.val : ℤ) - k.val
    then (a t : ℂ) else 0

/-- PDF p.14, (50): specialize the accepted full Toeplitz matrix to the
paper's banded signed-offset data; no periodic wrap-around is introduced. -/
def bandedToeplitz (n d : ℕ) (k : Fin (2 ^ d)) (a : Fin (2 ^ d) → ℝ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  QAlgorithms.Papers.Independent.Advance50.P23.toeplitz (2 ^ n) (2 ^ n)
    (bandedToeplitzSeed n d k a)

/-- Sanity check: the one-entry banded Toeplitz adapter selects its sole datum. -/
example (a : Fin 1 → ℝ) : bandedToeplitz 0 0 0 a 0 0 = (a 0 : ℂ) := by
  simp [bandedToeplitz, QAlgorithms.Papers.Independent.Advance50.P23.toeplitz,
    bandedToeplitzSeed]

/-- PDF pp.14-15: the actual Toeplitz arithmetic and its overflow deletion. -/
def ToeplitzLabels (B : Scheme n d d n) (k : Fin (2 ^ d)) : Prop :=
  B.columnSlots = Finset.univ ∧ B.rowSlots = Finset.univ ∧
  ∀ l, B.column l = (l.1, l.2) ∧ (B.row l).1 = l.1 ∧
    ((B.row l).2.val : ℤ) = ((l.1.val : ℤ) - k.val + l.2.val) % (2 ^ n : ℕ) ∧
    (B.valid l = true ↔ 0 ≤ (l.1.val : ℤ) - k.val + l.2.val ∧
      (l.1.val : ℤ) - k.val + l.2.val < (2 ^ n : ℕ))

/-- PDF pp.15-16, (57),(63): diagonal/off-diagonal data with the last table
slot fixed to zero, rather than loaded as an independent real parameter. -/
def triTable (n : ℕ) (a : Fin (2 * 2 ^ n - 1) → ℝ) : Fin (2 ^ (n + 1)) → ℝ :=
  fun j => if h : j.val < 2 * 2 ^ n - 1 then a ⟨j.val, h⟩ else 0

/-- PDF p.15, (57): symmetric tridiagonal matrix, including N=1 and N=2. -/
def tridiagonal (n : ℕ) (a : Fin (2 * 2 ^ n - 1) → ℝ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun i j => if i = j then (triTable n a ⟨2 * i.val, by simp only [pow_succ]; omega⟩ : ℂ)
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then
      (triTable n a ⟨2 * min i.val j.val + 1, by
        have hi := i.isLt
        have hm := Nat.min_le_left i.val j.val
        simp only [pow_succ]
        omega⟩ : ℂ) else 0

/-- PDF p.16, (58)-(62): the supported three labels are 00,01,11, not H4. -/
def TridiagonalLabels (B : Scheme n 2 (n + 1) 1) : Prop :=
  B.columnSlots = (Finset.univ.filter fun j => j.val ≠ 2) ∧
  B.rowSlots = (Finset.univ.filter fun j => j.val ≠ 2) ∧
  ∀ l, (B.valid l = true ↔ ¬((l.1.val % 2 = 0 ∧ l.2.val = 1) ∨
      l.1.val + 1 = 2 ^ (n + 1))) ∧
    (B.valid l = true → (B.row l).2.val = (l.1.val / 2 + l.2.val) % 2 ^ n ∧
      (B.column l).2.val = (l.1.val / 2 + (if l.2.val = 0 then l.1.val % 2 else 0)) % 2 ^ n)

/-- PDF pp.17-18, (67): tree adjacency with the source's extra root edge
0--1, root/leaf diagonal a0, internal diagonal a1, and every edge a2. -/
def extendedTree (n : ℕ) (a : Fin 3 → ℝ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun i j => if i = j then (a (if i.val = 0 ∨ 2 ^ n / 2 ≤ i.val then 0 else 1) : ℂ)
    else if (i.val > 0 ∧ i.val / 2 = j.val) ∨ (j.val > 0 ∧ j.val / 2 = i.val)
      then (a 2 : ℂ) else 0

/-- PDF p.17: fourth physical data slot is a structural zero. -/
def treeTable (a : Fin 3 → ℝ) : Fin 4 → ℝ :=
  fun j => if h : j.val < 3 then a ⟨j.val, h⟩ else 0

/-- PDF pp.17-18, (69)-(74): range and row formulas. The two invalid edge
labels m=0,N have reversible completions instead of undefined arithmetic. -/
def TreeLabels (B : Scheme n 3 2 (n + 1)) : Prop :=
  B.columnSlots = (Finset.univ.filter fun j => j.val < 4) ∧
  B.rowSlots = (Finset.univ.filter fun j => j.val < 4) ∧
  ∀ l, (B.valid l = true ↔
    (l.1.val = 0 ∧ (l.2.val = 0 ∨ (2 ^ n / 2 ≤ l.2.val ∧ l.2.val < 2 ^ n))) ∨
    (l.1.val = 1 ∧ 0 < l.2.val ∧ l.2.val < 2 ^ n / 2) ∨
    (l.1.val = 2 ∧ l.2.val ≠ 0 ∧ l.2.val ≠ 2 ^ n)) ∧
    (B.valid l = true → (B.row l).2.val =
      if l.1.val < 2 then l.2.val else
        if l.2.val < 2 ^ n then l.2.val / 2 else l.2.val - 2 ^ n)

/-- PDF pp.19-20, (78): nonperiodic finite-difference Laplacian.
The integer coordinate differences avoid truncated natural subtraction. -/
def laplacian (nx ny : ℕ) (dx dy : ℝ) :
    Matrix (Fin (2 ^ (nx + ny))) (Fin (2 ^ (nx + ny))) ℂ :=
  fun i j =>
    if i = j then (-2 * (1 / dx ^ 2 + 1 / dy ^ 2) : ℝ)
    else if (i.val / 2 ^ nx = j.val / 2 ^ nx) ∧
        |((i.val % 2 ^ nx : ℕ) : ℤ) - (j.val % 2 ^ nx : ℕ)| = 1 then (1 / dx ^ 2 : ℝ)
    else if (i.val % 2 ^ nx = j.val % 2 ^ nx) ∧
        |((i.val / 2 ^ nx : ℕ) : ℤ) - (j.val / 2 ^ nx : ℕ)| = 1 then (1 / dy ^ 2 : ℝ)
    else 0

/-- PDF p.19, (78): the three actual values and a fourth zero sentinel. -/
def laplacianTable (dx dy : ℝ) : Fin 4 → ℝ :=
  fun j => if j.val = 0 then -2 * (1 / dx ^ 2 + 1 / dy ^ 2)
    else if j.val = 1 then 1 / dx ^ 2 else if j.val = 2 then 1 / dy ^ 2 else 0

/-- PDF pp.19-20, (80)-(84): five supported states and off-grid deletion. -/
def LaplacianLabels (nx ny : ℕ) (B : Scheme (nx + ny) 3 2 (nx + ny + 1)) : Prop :=
  B.columnSlots = (Finset.univ.filter fun j => j.val = 0 ∨ j.val = 2 ∨
    j.val = 3 ∨ j.val = 4 ∨ j.val = 5) ∧
  B.rowSlots = B.columnSlots ∧
  ∀ l, (B.valid l = true ↔
    (l.1.val = 0 ∧ l.2.val < 2 ^ (nx + ny)) ∨
    (l.1.val = 1 ∧ l.2.val % 2 ^ nx ≠ 0) ∨
    (l.1.val = 2 ∧ l.2.val % 2 ^ (nx + ny) ≥ 2 ^ nx)) ∧
    (B.column l).1.val = 2 * l.1.val + l.2.val / 2 ^ (nx + ny) ∧
    (B.valid l = true → ((B.column l).2.val : ℤ) =
      ((l.2.val % 2 ^ (nx + ny) : ℕ) : ℤ) -
        (if l.2.val < 2 ^ (nx + ny) ∧ l.1.val = 1 then 1
         else if l.2.val < 2 ^ (nx + ny) ∧ l.1.val = 2 then (2 ^ nx : ℕ) else 0))

/-- PDF p.13, (45): when no range deletion is needed, remove that untouched
flag from the PREP circuit, rather than counting an extra physical flag. -/
def PrepLayout.noDeleteCircuit {B : Scheme n s d m} (L : PrepLayout B)
    {a : Fin (2 ^ d) → ℝ} {p : ℝ} (P : PreparationPair L a p) :
    Matrix (Fin (2 ^ s) × Fin (2 ^ n)) (Fin (2 ^ s) × Fin (2 ^ n)) ℂ :=
  fun x y => L.circuit P ((false, x.1), x.2) ((false, y.1), y.2)

/-- Reversible arithmetic with zero gates ignores no input and preserves all bits. -/
example (w : ℕ) (x : QAlgorithms.Qubits w) : runArithmetic [] x = x := rfl

/-- PDF p.16: the last tridiagonal table slot is a fixed zero sentinel. -/
example : triTable 1 (fun _ => (1 : ℝ)) 3 = 0 := by simp [triTable]

/-- N=2 checkerboard sign/parity and corner-deletion checks. -/
example (a : Fin 2 → ℝ) : checkerboard 1 a 0 1 = (a 1 : ℂ) ∧
    deletedCheckerboard 1 a 0 0 = 0 := by simp [checkerboard, deletedCheckerboard]

/-- PDF pp.25-26: the elementary Clifford+T gate set used for T counts.
Arbitrary rotations are targets of approximation, not free gates in this set. -/
def cliffordTSet : Set QAlgorithms.Gate :=
  {g | g = QAlgorithms.Gate.ofMatrix1 QAlgorithms.hadamard ∨
    g = QAlgorithms.Gate.ofMatrix1 QAlgorithms.gateT ∨
    g = QAlgorithms.Gate.ofMatrix1 QAlgorithms.gateTᴴ ∨
    g = QAlgorithms.Gate.ofMatrix1 QAlgorithms.pauliX ∨
    g = QAlgorithms.Gate.ofMatrix2 QAlgorithms.cnot}

local instance : DecidableEq QAlgorithms.Gate := Classical.decEq _

/-- PDF pp.25-26: extract the T-cost instruction trace from a concrete
Clifford+T circuit for the accepted single-qubit word counter. Each T or inverse-T
instruction contributes one t; other gates contribute h and hence zero T count.
This trace records cost only; Circuit.unitary retains the full gate semantics. -/
def loaderTWord {w : ℕ} (c : QAlgorithms.Circuit cliffordTSet w) :
    List QAlgorithms.Papers.Independent.Next46.P21.Letter :=
  c.map fun g => if g.gate = QAlgorithms.Gate.ofMatrix1 QAlgorithms.gateT ∨
    g.gate = QAlgorithms.Gate.ofMatrix1 QAlgorithms.gateTᴴ then .t else .h

/-- PDF p.26: a normalized reusable phase-gradient resource. Its preparation
is separate from each invocation of the lookup/rotate/uncompute procedure. -/
def phaseGradient (b : ℕ) (z : QAlgorithms.Qubits b) : ℂ :=
  (Real.sqrt (2 ^ b : ℕ))⁻¹ * Complex.exp
    (-2 * (Real.pi : ℂ) * Complex.I * (QAlgorithms.bitsToNat z : ℂ) / (2 ^ b : ℕ))

/-- PDF pp.25-26, (91): embed data flag and table index with the reusable
gradient state and clean work. This specifies full output accuracy, including
return of the resource and work, not only the selected data amplitude. -/
def loaderEmbedding (db b work : ℕ) :
    Matrix (QAlgorithms.Qubits (1 + db + b + work)) (Bool × Fin (2 ^ db)) ℂ :=
  fun y x => if y ⟨0, by omega⟩ = x.1 ∧
      (∀ i : Fin db, y ⟨1 + i.val, by omega⟩ = QAlgorithms.natToBits db x.2 i) ∧
      (∀ i : Fin work, y ⟨1 + db + b + i.val, by omega⟩ = false) then
    phaseGradient b (fun i => y ⟨1 + db + i.val, by omega⟩) else 0

/-- PDF p.25, (89): the ideal multiplexed RX data loader on every data-flag input. -/
def idealLoader {db : ℕ} (a : Fin (2 ^ db) → ℝ) :
    Matrix (Bool × Fin (2 ^ db)) (Bool × Fin (2 ^ db)) ℂ :=
  fun x y => if x.2 = y.2 then dataRotation (a y.2 / tableMax a) x.1 y.1 else 0

/-- PDF p.25: a non-power-of-two supplied data table is padded with known zeros
in its minimal physical binary register. No new unknown item is loaded. -/
def paddedTable {D : ℕ} (a : Fin D → ℝ) : Fin (2 ^ (Nat.clog 2 D)) → ℝ :=
  fun j => if h : j.val < D then a ⟨j.val, h⟩ else 0

/-- PDF p.26, (94): the reverse map supplies an occurrence label, or the
fixed zero sentinel for structural zeros. It is not inferred from forward maps. -/
def reverseCode {d m : ℕ} {X : Type*}
    (r : X → Option (Fin (2 ^ d) × Fin (2 ^ m))) (x : X) :
    QAlgorithms.Qubits (1 + d + m) :=
  fun i => match r x with
    | none => false
    | some l => flaggedPairBits (true, l) i.val

/-- PDF p.26: finite b-bit data lookup, with no additional loaded zero value. -/
def valueAtLabel {d m b : ℕ} (code : Fin (2 ^ d) → QAlgorithms.Qubits b)
    (z : QAlgorithms.Qubits (1 + d + m)) : QAlgorithms.Qubits b :=
  if z ⟨0, by omega⟩ then code (QAlgorithms.bitsEquivFin d
    (fun i => z ⟨1 + i.val, by omega⟩)) else 0

/-- A basis-action matrix used for the reversible XOR compute/load steps. -/
def basisMatrix {X : Type*} [DecidableEq X] (f : X → X) : Matrix X X ℂ :=
  fun x y => if x = f y then 1 else 0

/-- PDF p.26, (94): compute the occurrence label, XOR the corresponding
finite entry value, then uncompute the occurrence label. Buffer input is general. -/
def entryCircuit {n d m b : ℕ}
    (r : (Fin (2 ^ n) × Fin (2 ^ n)) → Option (Fin (2 ^ d) × Fin (2 ^ m)))
    (code : Fin (2 ^ d) → QAlgorithms.Qubits b) :
    Matrix ((QAlgorithms.Qubits b × (Fin (2 ^ n) × Fin (2 ^ n))) ×
      QAlgorithms.Qubits (1 + d + m))
      ((QAlgorithms.Qubits b × (Fin (2 ^ n) × Fin (2 ^ n))) ×
        QAlgorithms.Qubits (1 + d + m)) ℂ :=
  let C := basisMatrix fun x => (x.1, x.2 + reverseCode r x.1.2)
  let V := basisMatrix fun x => ((x.1.1 + valueAtLabel code x.2, x.1.2), x.2)
  C * V * C

/-- PDF p.26: binary encoding for the reverse-map implementation; rows,
columns, and occurrence workspace use the fixed displayed register order. -/
def rowColumnLabelBits {n t : ℕ}
    (x : (Fin (2 ^ n) × Fin (2 ^ n)) × QAlgorithms.Qubits t) (i : ℕ) : Bool :=
  if i < n + n then pairBits x.1 i else bitAt t (QAlgorithms.bitsToNat x.2) (i - (n + n))

/-- PDF p.26: the arithmetic part of the three-stage word consists exactly
of the given reverse-map circuit and its inverse, with no repetition of data. -/
def entryArithmeticCost {w : ℕ} (c : List (ArithmeticGate w)) : ℕ :=
  toffoliCount (c ++ c.reverse)

/-- A zero sentinel yields the zero b-bit word, including b=0. -/
example (b d m : ℕ) (code : Fin (2 ^ d) → QAlgorithms.Qubits b) :
    valueAtLabel (m := m) code 0 = 0 := by simp [valueAtLabel]

/-- The empty Clifford+T circuit has zero T count. -/
example (w : ℕ) : tCount (loaderTWord ([] : QAlgorithms.Circuit cliffordTSet w)) = 0 := rfl

end QAlgorithms.Papers.Independent.Extend50.P44


