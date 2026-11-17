-- Prove2me | Definitions.Def_CoRSuccGap_Supplement_TypedMatrixCircuit
-- name    : CoRSuccGap_Supplement_TypedMatrixCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:39:14.241105+00:00
-- url     : https://prove2.me/theorems/997b51c5-0177-428f-9ab8-76e9c2a9a855
-- title:
--   Typed matrix circuits and charged aggregation counts $\#_{mv},\#_{mm}$
-- statement:
--   A **typed matrix circuit** has arrays of shape $n\times n$, $n\times1$, $1\times n$ or $1\times1$ and fixed acyclic wiring. Its gates are square input matrices; contractions with arbitrary fixed kernels $\kappa:S\times S\to S$; arbitrary uniform entrywise functions; transpose; broadcasting; diagonal extraction and formation; uniform vector and scalar constants; and diagonal masks. Kernels and entrywise functions cannot inspect vertex names, output positions or the contracted index.
--
--   A contraction over the common data index aggregates with semiring addition. Contraction over a singleton index simply applies its kernel. The count $\#_{mv}$ charges distinct matrix--vector and vector--matrix data-index contractions; $\#_{mm}$ charges distinct square matrix--matrix contractions. Vector inner products, singleton-index contractions and every other permitted operation are uncharged.
--
--   A circuit computes $G_k$ when its square output equals the semiring-valued query on every finite nonempty common index set and every input interpretation. Sharing is allowed and each distinct gate is counted once.
-- source:
--   Uezato--Nakamura, arXiv:2609.26778 (held version, sha256 5ad6337d...), Section 7.2 pp.39--40 (PDF 41--42)

import Mathlib
import Definitions.Def_CoRSuccGap_Gk
import Definitions.Def_CoRSuccGap_Supplement_AnnotatedRelationalAlgebra

set_option autoImplicit false

namespace CoRSuccGap
namespace Supplement

universe u

/-!
# Typed matrix circuits and charged data-index contractions

Uezato--Nakamura, *An Exponential Succinctness Gap between Three-Variable Logic and the
Calculus of Relations*, arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), Section 7.2,
pp.39--40 (PDF 41--42).

There are exactly four shapes: matrix, column, row, and scalar.  Gates are input matrices,
contractions with arbitrary fixed kernels, arbitrary uniform entrywise functions, transpose,
broadcasting, diagonal extraction and formation, uniform vector/scalar constants, and diagonal
masks.  Gate operands always point to earlier gates, so the representation is a DAG with sharing.
Only matrix--vector, vector--matrix, and matrix--matrix contractions over the data index are charged.
-/

/-- One index dimension, either the singleton dimension `1` or the data dimension `n`. -/
inductive MatrixDim where
  | one
  | data
deriving DecidableEq

/-- The four permitted array shapes are pairs of dimensions in `{1,n}`. -/
structure MatrixShape where
  row : MatrixDim
  col : MatrixDim
deriving DecidableEq

namespace MatrixShape

def matrix : MatrixShape := ⟨.data, .data⟩
def column : MatrixShape := ⟨.data, .one⟩
def rowVector : MatrixShape := ⟨.one, .data⟩
def scalar : MatrixShape := ⟨.one, .one⟩

end MatrixShape

/-- The index type represented by a dimension symbol. -/
def MatrixDim.Index (V : Type u) : MatrixDim → Type u
  | .one => PUnit
  | .data => V

instance MatrixDim.indexFintype (V : Type*) [Fintype V] (d : MatrixDim) :
    Fintype (d.Index V) :=
  match d with
  | .one => inferInstanceAs (Fintype PUnit)
  | .data => inferInstanceAs (Fintype V)

/-- An `S`-valued array of a permitted shape. -/
abbrev TypedArray (S V : Type*) (sh : MatrixShape) := sh.row.Index V → sh.col.Index V → S

/-- An array packaged with its shape. -/
abbrev PackedArray (S V : Type*) := Σ sh : MatrixShape, TypedArray S V sh

/-- A dimension may be broadcast to itself, or a singleton dimension may be broadcast to data. -/
inductive CanBroadcastDim : MatrixDim → MatrixDim → Type
  | refl (d : MatrixDim) : CanBroadcastDim d d
  | oneData : CanBroadcastDim .one .data

/-- Forget a broadcast output index down to its source index. -/
def CanBroadcastDim.project {V : Type*} {a b : MatrixDim} :
    CanBroadcastDim a b → b.Index V → a.Index V
  | .refl _, x => x
  | .oneData, _ => PUnit.unit

/-- Cast a packed array to an expected shape; this keeps evaluation total, while
`TypedMatrixCircuit.WellTyped` below excludes every mismatched operand port from the circuit
class used in the theorems. -/
noncomputable def PackedArray.asShape {S V : Type*} [Zero S]
    (sh : MatrixShape) (A : PackedArray S V) : TypedArray S V sh := by
  classical
  exact if h : A.1 = sh then cast (congrArg (TypedArray S V) h) A.2 else fun _ _ => 0

/-- Contraction over the common middle dimension.  When that dimension is `1`, the finite sum has
one term and therefore merely applies the kernel; when it is `n`, it aggregates over the data. -/
noncomputable def contractArray {S V : Type*} [AddCommMonoid S] [Fintype V]
    (sx sy : MatrixShape) (h : sx.col = sy.row) (kernel : S → S → S)
    (X : TypedArray S V sx) (Y : TypedArray S V sy) :
    TypedArray S V ⟨sx.row, sy.col⟩ :=
  fun i j => ∑ z : sx.col.Index V, kernel (X i z)
    (Y (cast (congrArg (fun d => d.Index V) h) z) j)

/-- Shapes on which a uniform constant gate is supplied for free. -/
inductive UniformConstantShape where
  | scalar
  | column
  | row

def UniformConstantShape.shape : UniformConstantShape → MatrixShape
  | .scalar => .scalar
  | .column => .column
  | .row => .rowVector

/-- Every permitted gate label.  Functions, kernels, and scalar constants are stored in the label,
so they are fixed before an input is seen and cannot access vertex names or positions. -/
inductive MatrixGate (S σ : Type*) (ι : Type*) where
  | input (R : σ)
  | contract (sx sy : MatrixShape) (h : sx.col = sy.row) (x y : ι) (kernel : S → S → S)
  | entrywise (sh : MatrixShape) (r : ℕ) (args : Fin r → ι) (f : (Fin r → S) → S)
  | transpose (sh : MatrixShape) (x : ι)
  | broadcast (src dst : MatrixShape) (hr : CanBroadcastDim src.row dst.row)
      (hc : CanBroadcastDim src.col dst.col) (x : ι)
  | diagExtractColumn (x : ι)
  | diagExtractRow (x : ι)
  | diagFormColumn (x : ι)
  | diagFormRow (x : ι)
  | uniformConstant (sh : UniformConstantShape) (c : S)
  | diagonalMask (onDiagonal offDiagonal : S)

namespace MatrixGate

variable {S σ ι : Type*}

/-- The output shape declared by a gate label. -/
def outputShape : MatrixGate S σ ι → MatrixShape
  | .input _ => .matrix
  | .contract sx sy _ _ _ _ => ⟨sx.row, sy.col⟩
  | .entrywise sh _ _ _ => sh
  | .transpose sh _ => ⟨sh.col, sh.row⟩
  | .broadcast _ dst _ _ _ => dst
  | .diagExtractColumn _ => .column
  | .diagExtractRow _ => .rowVector
  | .diagFormColumn _ => .matrix
  | .diagFormRow _ => .matrix
  | .uniformConstant sh _ => sh.shape
  | .diagonalMask _ _ => .matrix

/-- Whether the gate is a charged matrix--vector or vector--matrix data-index contraction. -/
def isMV : MatrixGate S σ ι → Bool
  | .contract sx sy _ _ _ _ =>
      (sx == MatrixShape.matrix && sy == MatrixShape.column) ||
      (sx == MatrixShape.rowVector && sy == MatrixShape.matrix)
  | _ => false

/-- Whether the gate is a charged square matrix--matrix data-index contraction. -/
def isMM : MatrixGate S σ ι → Bool
  | .contract sx sy _ _ _ _ => sx == MatrixShape.matrix && sy == MatrixShape.matrix
  | _ => false

/-- The static shape check for every operand port of one gate. -/
def WellTyped (shape : ι → MatrixShape) : MatrixGate S σ ι → Prop
  | .input _ => True
  | .contract sx sy _ x y _ => shape x = sx ∧ shape y = sy
  | .entrywise sh _ args _ => ∀ a, shape (args a) = sh
  | .transpose sh x => shape x = sh
  | .broadcast src _ _ _ x => shape x = src
  | .diagExtractColumn x => shape x = .matrix
  | .diagExtractRow x => shape x = .matrix
  | .diagFormColumn x => shape x = .column
  | .diagFormRow x => shape x = .rowVector
  | .uniformConstant _ _ => True
  | .diagonalMask _ _ => True

/-- Evaluate one label from already evaluated operand gates. -/
noncomputable def evalWith {V : Type*} [Fintype V] [DecidableEq V] [CommSemiring S]
    (M : σ → V → V → S) (val : ι → PackedArray S V) :
    MatrixGate S σ ι → PackedArray S V
  | .input R => ⟨.matrix, M R⟩
  | .contract sx sy h x y kernel =>
      ⟨⟨sx.row, sy.col⟩, contractArray sx sy h kernel
        ((val x).asShape sx) ((val y).asShape sy)⟩
  | .entrywise sh _ args f =>
      ⟨sh, fun i j => f (fun a => ((val (args a)).asShape sh) i j)⟩
  | .transpose sh x =>
      ⟨⟨sh.col, sh.row⟩, fun i j => ((val x).asShape sh) j i⟩
  | .broadcast src dst hr hc x =>
      ⟨dst, fun i j => ((val x).asShape src) (hr.project i) (hc.project j)⟩
  | .diagExtractColumn x =>
      ⟨MatrixShape.column, fun i _ => ((val x).asShape MatrixShape.matrix) i i⟩
  | .diagExtractRow x =>
      ⟨MatrixShape.rowVector, fun _ j => ((val x).asShape MatrixShape.matrix) j j⟩
  | .diagFormColumn x =>
      ⟨MatrixShape.matrix, fun (i : V) (j : V) =>
        if i = j then ((val x).asShape MatrixShape.column) i PUnit.unit else 0⟩
  | .diagFormRow x =>
      ⟨MatrixShape.matrix, fun (i : V) (j : V) =>
        if i = j then ((val x).asShape MatrixShape.rowVector) PUnit.unit i else 0⟩
  | .uniformConstant sh c =>
      ⟨sh.shape, fun _ _ => c⟩
  | .diagonalMask d o =>
      ⟨MatrixShape.matrix, fun (i : V) (j : V) => if i = j then d else o⟩

end MatrixGate

/-- A fixed-wiring typed matrix circuit.  Gate `i` may reference only `Fin i`, hence sharing is
allowed and cycles are impossible. -/
structure TypedMatrixCircuit (S : Type*) (k : ℕ) where
  size : ℕ
  gate : (i : Fin size) → MatrixGate S (GSym k) (Fin i)
  output : Fin size

namespace TypedMatrixCircuit

variable {S : Type*} {k : ℕ}

/-- The declared output shape of a gate. -/
def gateShape (C : TypedMatrixCircuit S k) (i : Fin C.size) : MatrixShape :=
  (C.gate i).outputShape

/-- Every gate receives operands of exactly the shapes written on its ports. -/
def WellTyped (C : TypedMatrixCircuit S k) : Prop :=
  ∀ i : Fin C.size,
    (C.gate i).WellTyped (fun j => C.gateShape ⟨j.val, lt_trans j.isLt i.isLt⟩)

/-- Evaluate every distinct gate once in topological order. -/
noncomputable def gateVal [CommSemiring S] (C : TypedMatrixCircuit S k)
    {V : Type*} [Fintype V] [DecidableEq V] (M : GSym k → V → V → S) :
    Fin C.size → PackedArray S V
  | ⟨i, hi⟩ => (C.gate ⟨i, hi⟩).evalWith M
      (fun j => C.gateVal M ⟨j.val, lt_trans j.isLt hi⟩)
termination_by i => i.val
decreasing_by exact j.isLt

/-- The packed value of the designated output gate. -/
noncomputable def eval [CommSemiring S] (C : TypedMatrixCircuit S k)
    {V : Type*} [Fintype V] [DecidableEq V] (M : GSym k → V → V → S) :
    PackedArray S V := C.gateVal M C.output

/-- Number of distinct charged matrix--vector and vector--matrix contractions. -/
def numMV (C : TypedMatrixCircuit S k) : ℕ :=
  (Finset.univ.filter (fun i : Fin C.size => (C.gate i).isMV)).card

/-- Number of distinct charged square matrix--matrix contractions. -/
def numMM (C : TypedMatrixCircuit S k) : ℕ :=
  (Finset.univ.filter (fun i : Fin C.size => (C.gate i).isMM)).card

/-- The circuit computes the semiring query `G_k` on every finite nonempty common index set and
every interpretation of its square input matrices. -/
def ComputesGk [CommSemiring S] (C : TypedMatrixCircuit S k) : Prop :=
  C.WellTyped ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
      (M : GSym k → V → V → S),
        (C.eval M).fst = MatrixShape.matrix ∧
        (show V → V → S from (C.eval M).asShape MatrixShape.matrix) = semiringGk k M

end TypedMatrixCircuit

end Supplement
end CoRSuccGap


