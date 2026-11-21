-- Prove2me | Definitions.Def_InfoLossLAR_RegevSearch_PhysicalFourierReadout
-- name    : InfoLossLAR_RegevSearch_PhysicalFourierReadout
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T05:34:11.2095+00:00
-- url     : https://prove2.me/theorems/513f605a-539c-4686-b8e2-779b46460b5e
-- title:
--   Native register encodings for Fourier readout and coherent decoder cleanup
-- statement:
--   Fix a lattice basis and a dyadic modulus $2^b$. These definitions put the normalized Gaussian amplitudes on the finite coordinate register, lay out its $b$-bit axes and two ancillary qubits, and define the signed integer readout. They also specify the encoding of a framed decoder request, its answer word and an independent reference register. The joint register conventions let the Fourier sampling and coherent erasure theorems quantify over arbitrary normalized input states and all finite output events.
-- source:
--   Register definitions used by InfoLossLAR.WorstCase.RegevSearch.coherent_shared_pool_fourier_sampler, https://prove2.me/theorems/23174e03-6b1d-4113-b6b9-4dab17fa850a

import Definitions.Def_InfoLossLAR_BDD_Coordinates
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_05
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_06_Optimized
import Definitions.Def_InfoLossLAR_IntegerBasis_Core
import Definitions.Def_InfoLossLAR_NativeSparsePrefix_02
import Definitions.Def_InfoLossLAR_RegevSearch_FourierGrid
import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Definitions.Def_InfoLossLAR_RuntimeBundle_01
import Definitions.Def_InfoLossLAR_WorstCase_QPT
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_ShorAlgorithms_QFT_Circuit
import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

section

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open AFT
open GaussianSource
open RegevLWE.GaussConv
open GaussianRandomizedRounding

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

/-- Canonical input-basis representative of each public residue vector. -/
def lift {Index : Type*} [Fintype Index] (q : ℕ) [NeZero q]
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (color : Index → ZMod q) : lattice :=
  basis.equivFun.symm (fun index => ((color index).val : ℤ))

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

end

section

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv
open GaussianProjection
open GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

/-- Each integral dual coordinate is exactly the pairing with the
corresponding original input column. -/
private theorem dualCoordinates_inner (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (value : Fin dimension → ℤ) (index : Fin dimension) :
    inner ℝ (dualCoordinates basis hdet value) (integerBasis basis hdet index : Space (dimension:=dimension))=(value index : ℝ) := by
  have hreal : (integerBasis basis hdet index : Space (dimension:=dimension))=realBasis basis hdet index :=
    Module.Basis.restrictScalars_apply ℤ (realBasis basis hdet) index
  have hdual (column row : Fin dimension) :
      inner ℝ (dualRealBasis basis hdet column) (realBasis basis hdet row)=if row=column then 1 else 0 :=
    LinearMap.BilinForm.apply_dualBasis_left inner_nondegenerate (realBasis basis hdet) column row
  rw [dualCoordinates_apply,hreal,sum_inner]
  simp only [←Int.cast_smul_eq_zsmul ℝ,real_inner_smul_left]
  simp_rw [hdual]
  simp

end

end InfoLossLAR.WorstCase.IntegerBasis

end

section

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv
open GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

/-- Integral coordinates identify the genuine dual input lattice with the
free integer module, using exactly the original input-basis pairings. -/
def dualIntegerEquiv (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    (Fin dimension → ℤ) ≃ₗ[ℤ] dual (inputLattice basis hdet) where
  toFun value := ⟨dualCoordinates basis hdet value,dualCoordinates_mem basis hdet value⟩
  invFun point := fun index => pairing (inputLattice basis hdet) point (integerBasis basis hdet index)
  left_inv value := by
    funext index
    apply Int.cast_injective (α:=ℝ)
    rw [pairing_spec]
    exact dualCoordinates_inner basis hdet value index
  right_inv point := by
    apply Subtype.ext
    exact dualCoordinates_pairing basis hdet point
  map_add' first second := Subtype.ext (map_add (dualCoordinates basis hdet) first second)
  map_smul' scalar value := Subtype.ext (map_smul (dualCoordinates basis hdet) scalar value)

/-- A genuine integral basis of the dual lattice. It is a mathematical
coordinate object; a separate native algorithm computes its rational entries. -/
def dualIntegerBasis (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    Module.Basis (Fin dimension) ℤ (dual (inputLattice basis hdet)) :=
  (Pi.basisFun ℤ (Fin dimension)).map (dualIntegerEquiv basis hdet)

end

end InfoLossLAR.WorstCase.IntegerBasis

end

section

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open MeasureTheory
open FourierTransform
open RegevLWE.GaussConv

open scoped FourierTransform SchwartzMap

noncomputable section

variable {dimension : ℕ}

abbrev Space := EuclideanSpace ℝ (Fin dimension)

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end

section

namespace InfoLossLAR.WorstCase.FiniteLatticeFourier

open GaussianProjection.CosetGeometry
open RegevLWE.GaussConv

open scoped BigOperators FourierTransform

noncomputable section

variable {dimension : ℕ}

abbrev CoordinateSpace := EuclideanSpace ℝ (Fin dimension)

/-- The actual fine-lattice point represented by one quotient color in
L/modulus, using the original integral basis and no arbitrary section. -/
def gridPoint (modulus : ℕ) [NeZero modulus]
    (lattice : Submodule ℤ (CoordinateSpace (dimension:=dimension)))
    (basis : Module.Basis (Fin dimension) ℤ lattice) (color : Fin dimension → ZMod modulus) :
    CoordinateSpace (dimension:=dimension) :=
  (modulus : ℝ)⁻¹ • (GaussianProjection.CosetGeometry.lift modulus lattice basis color : CoordinateSpace (dimension:=dimension))

end

end InfoLossLAR.WorstCase.FiniteLatticeFourier

end

section

namespace InfoLossLAR.WorstCase.CoherentProjection

open scoped BigOperators

noncomputable def normalized {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E) : E :=
  ‖v‖⁻¹ • v

end InfoLossLAR.WorstCase.CoherentProjection

end

section

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv
open GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

variable {dimension modulus : ℕ} [NeZero modulus]

/-- Actual complete periodized Gaussian amplitudes on the finite quotient,
before their physical global norm is removed. -/
def periodizedState (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (basis : Module.Basis (Fin dimension) ℤ lattice) (width : ℝ) :
    EuclideanSpace ℂ (Fin dimension → ZMod modulus) :=
  WithLp.toLp 2 (fun color => (rhoCoset width lattice
    (FiniteLatticeFourier.gridPoint modulus lattice basis color) : ℂ))

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end

section

namespace InfoLossLAR.WorstCase.CoherentDecoder

open scoped BigOperators

noncomputable section

/-- Unnormalized Born mass, so the error statement also covers intermediate
states before normalization has separately been established. -/
def bornEvent {α : Type*} [Fintype α] (event : α → Prop)
    (state : EuclideanSpace ℂ α) : ℝ :=
  open Classical in ∑ value,if event value then ‖state value‖^2 else 0

end

end InfoLossLAR.WorstCase.CoherentDecoder

end

section

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms
open QAlgorithms.Complexity

inductive Letter (n : ℕ) where
  | h (i : Fin n)
  | t (i : Fin n)
  | cnot (i j : Fin n) (hij : i≠j)
  deriving DecidableEq

def Letter.toInstr {n : ℕ} : Letter n → Instr n
  | .h i => .h i
  | .t i => .t i
  | .cnot i j hij => .cnot i j hij

def instructions {n : ℕ} (word : List (Letter n)) : List (Instr n) :=
  word.map Letter.toInstr

end InfoLossLAR.WorstCase.FiniteGateTransport

end

section

namespace InfoLossLAR.WorstCase.FiniteGateTransport

def alphabet : List (Letter 3) :=
  [.h 0,.h 1,.h 2,.t 0,.t 1,.t 2,
   .cnot 0 1 (by decide),.cnot 0 2 (by decide),
   .cnot 1 0 (by decide),.cnot 1 2 (by decide),
   .cnot 2 0 (by decide),.cnot 2 1 (by decide)]

end InfoLossLAR.WorstCase.FiniteGateTransport

end

section

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

/-- Executable rational coordinates for `a + b sqrt(2)`. -/
abbrev RealPair := ℚ × ℚ

/-- Executable rational coordinates for `(a + b sqrt(2)) + i(c + d sqrt(2))`. -/
abbrev Scalar := RealPair × RealPair

def addReal (x y : RealPair) : RealPair := (x.1+y.1,x.2+y.2)

def negReal (x : RealPair) : RealPair := (-x.1,-x.2)

def subReal (x y : RealPair) : RealPair := addReal x (negReal y)

def mulReal (x y : RealPair) : RealPair :=
  (x.1*y.1+2*x.2*y.2,x.1*y.2+x.2*y.1)

def zero : Scalar := ((0,0),(0,0))

def one : Scalar := ((1,0),(0,0))

def add (x y : Scalar) : Scalar := (addReal x.1 y.1,addReal x.2 y.2)

def neg (x : Scalar) : Scalar := (negReal x.1,negReal x.2)

def sub (x y : Scalar) : Scalar := add x (neg y)

def mul (x y : Scalar) : Scalar :=
  (subReal (mulReal x.1 y.1) (mulReal x.2 y.2),
   addReal (mulReal x.1 y.2) (mulReal x.2 y.1))

def normSq (x : Scalar) : RealPair := addReal (mulReal x.1 x.1) (mulReal x.2 x.2)

/-- A rational comparison decides the sign exactly. No real-number oracle is read. -/
def nonnegReal (x : RealPair) : Bool :=
  if 0≤x.2 then
    if 0≤x.1 then true else decide (x.1^2≤2*x.2^2)
  else
    if x.1<0 then false else decide (2*x.2^2≤x.1^2)

/-- Exact comparison of an algebraic real coordinate with a supplied rational bound. -/
def leRational (x : RealPair) (bound : ℚ) : Bool :=
  nonnegReal (subReal (bound,0) x)

end InfoLossLAR.WorstCase.FiniteGateNative

end

section

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms
open QAlgorithms.Complexity

def finBits {n : ℕ} (bits : Bits n) : Fin n → Fin 2 := fun i => if bits i then 1 else 0

end InfoLossLAR.WorstCase.FiniteGateTransport

end

section

namespace InfoLossLAR.WorstCase.NativePhaseTaylor

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2NativeFiniteSeries

open FiniteGateNative
open FiniteGateTransport

open scoped BigOperators

abbrev Input := ℚ × List Unit

def termValue (x : Input × ℕ) : ℚ := cappedTaylor ((x.1.1/4,x.1.2),x.2)

def realTerm (x : Input × ℕ) : ℚ :=
  if x.2%4=0 then termValue x else if x.2%4=2 then -termValue x else 0

def imagTerm (x : Input × ℕ) : ℚ :=
  if x.2%4=1 then termValue x else if x.2%4=3 then -termValue x else 0

def realSum (x : Input) : ℚ := ((List.range x.2.length).map (fun i => realTerm (x,i))).sum

def imagSum (x : Input) : ℚ := ((List.range x.2.length).map (fun i => imagTerm (x,i))).sum

def base (x : Input) : Scalar := ((realSum x,0),(imagSum x,0))

def current (x : Input) : Scalar :=
  let squared := FiniteGateNative.mul (base x) (base x)
  FiniteGateNative.mul squared squared

/-- Unary buffers bound pi precision, QFT gap, and Taylor degree. The Boolean
selects a negative phase. No unchecked binary exponent or real input occurs. -/
abbrev QFTRequest := (List Unit × List Unit × List Unit) × Bool

def angle (x : QFTRequest) : ℚ :=
  AFT.RationalNumerics.piApprox x.1.1.length / powerValue (2,x.1.2.1++[()])

def signedAngle (x : QFTRequest) : ℚ := if x.2 then -angle x else angle x

def qftCurrent (x : QFTRequest) : Scalar := current (signedAngle x,x.1.2.2)

end InfoLossLAR.WorstCase.NativePhaseTaylor

end

section

namespace InfoLossLAR.WorstCase.NativeQFTPlan

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

open QMCNumericRuntime

/-- Unary wire count, pi precision and Taylor precision. No real angle is
accepted as executable program input. -/
abbrev Input := List Unit × List Unit × List Unit

/-- Tags 0,1,2 mean H, phase and CNOT. The next fields are two natural wire
addresses and the native finite phase request. -/
abbrev Instruction := ℕ × ℕ × ℕ × NativePhaseTaylor.QFTRequest

def emptyRequest : NativePhaseTaylor.QFTRequest := (([],[],[]),false)

def hCode (wire : ℕ) : Instruction := (0,wire,0,emptyRequest)

def cnotCode (first second : ℕ) : Instruction := (2,first,second,emptyRequest)

def phaseCode (wire : ℕ) (request : NativePhaseTaylor.QFTRequest) : Instruction := (1,wire,0,request)

def request (input : Input) (gap : ℕ) (negative : Bool) : NativePhaseTaylor.QFTRequest :=
  ((input.2.1,input.1.take gap,input.2.2),negative)

/-- The five exact requests for a controlled phase. The later semantic proof
uses only i<j from the actual QFT schedule. -/
def interaction (x : Input × (ℕ × ℕ)) : List Instruction :=
  [phaseCode x.2.1 (request x.1 (x.2.2-x.2.1) false),
    phaseCode x.2.2 (request x.1 (x.2.2-x.2.1) false),
    cnotCode x.2.1 x.2.2,
    phaseCode x.2.2 (request x.1 (x.2.2-x.2.1) true),
    cnotCode x.2.1 x.2.2]

def indices (input : Input) : List ℕ := (List.range input.1.length).reverse

def rowPlan (x : Input × ℕ) : List Instruction :=
  ((indices x.1).filter (fun j => decide (x.2<j))).flatMap (fun j => interaction (x.1,(x.2,j)))++[hCode x.2]

def current (input : Input) : List Instruction :=
  (indices input).flatMap (fun i => rowPlan (input,i))

end InfoLossLAR.WorstCase.NativeQFTPlan

end

section

namespace InfoLossLAR.WorstCase.FiniteGateNative

def hScale : Scalar := ((0,1/2),(0,0))

def tPhase : Scalar := ((0,1/2),(0,1/2))

def hCoefficient (row column : Bool) : Scalar := if row && column then neg hScale else hScale

def tCoefficient (row column : Bool) : Scalar := if row=column then (if row then tPhase else one) else zero

end InfoLossLAR.WorstCase.FiniteGateNative

end

section

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

abbrev Bits := QAlgorithms.Complexity.Bits 3

abbrev NativeMatrix := Matrix Bits Bits Scalar

def basis : List Bits :=
  [![false,false,false],![false,false,true],![false,true,false],![false,true,true],
   ![true,false,false],![true,false,true],![true,true,false],![true,true,true]]

def sumAt (indices : List Bits) (f : Bits→Scalar) : Scalar :=
  indices.foldr (fun i acc => add (f i) acc) zero

def matrixMul (first second : NativeMatrix) : NativeMatrix :=
  fun r c => sumAt basis (fun k => mul (first r k) (second k c))

end InfoLossLAR.WorstCase.FiniteGateNative

end

section

namespace InfoLossLAR.WorstCase.FiniteGateNativeEnumeration

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PolynomialBudget

abbrev State := ℕ × List ℕ

def step (x : State × Unit) : State :=
  if x.1.1=0 then x.1 else (x.1.1/13,(x.1.1%13-1)::x.1.2)

def decode (x : List Unit × ℕ) : List ℕ :=
  (x.1.foldl (fun s u => step (s,u)) (x.2,[])).2.reverse

/-- Decode every bounded integer, with an explicit unary iteration budget. -/
def candidates (slots : List Unit) : List (List ℕ) :=
  (List.range slots.length).map (fun index => decode (slots,index))

def searchSlots (a : ℕ) (budget : List Unit) : List Unit :=
  List.replicate (13^(a+1)*(budget.length+1)^(4*a)) ()

def search (a : ℕ) (budget : List Unit) : List (List ℕ) := candidates (searchSlots a budget)

open FiniteGateTransport

def letterOfCode (code : ℕ) : Letter 3 := alphabet[code]?.getD (.h 0)

def interpreted (codes : List ℕ) : List (Letter 3) := codes.map letterOfCode

end InfoLossLAR.WorstCase.FiniteGateNativeEnumeration

end

section

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport

def singleGate (coefficient : Bool→Bool→Scalar) (i : Fin 3) : NativeMatrix :=
  fun row column =>
    if column=Function.update row i (column i) then coefficient (row i) (column i) else zero

def cnotGate (i j : Fin 3) : NativeMatrix :=
  fun row column =>
    if column=Function.update row j (xor (row j) (row i)) then one else zero

def letterNative : Letter 3→NativeMatrix
  | .h i => singleGate hCoefficient i
  | .t i => singleGate tCoefficient i
  | .cnot i j _ => cnotGate i j

def gateTable : List NativeMatrix := alphabet.map letterNative

def nativeGate (code : ℕ) : NativeMatrix := gateTable[code]?.getD (letterNative (.h 0))

end InfoLossLAR.WorstCase.FiniteGateNative

end

section

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport

def identityMatrix : NativeMatrix := fun row column => if row=column then one else zero

def maxSteps (a : ℕ) (budget : List Unit) : ℕ :=
  (13^(a+1)*(budget.length+1)^(4*a)).bits.length

abbrev EvalState := (List Unit×ℕ)×NativeMatrix

def evalStep (a : ℕ) (input : EvalState×ℕ) : EvalState :=
  if input.1.1.2 < maxSteps a input.1.1.1 then
    ((input.1.1.1,input.1.1.2+1),matrixMul (nativeGate input.2) input.1.2)
  else input.1

end InfoLossLAR.WorstCase.FiniteGateNative

end

section

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

def evalFold (a : ℕ) (codes : List ℕ) (state : EvalState) : EvalState :=
  codes.foldl (fun s code => evalStep a (s,code)) state

end InfoLossLAR.WorstCase.FiniteGateNative

end

section

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

open Polynomial

def boundedMatrix (a : ℕ) (input : List Unit×List ℕ) : NativeMatrix :=
  (evalFold a input.2 ((input.1,0),identityMatrix)).2

end InfoLossLAR.WorstCase.FiniteGateNative

end

section

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

abbrev InputBits := QAlgorithms.Qubits 1

def inputs : List InputBits := [fun _ => false,fun _ => true]

def initializedColumn (x : InputBits) : Bits := Fin.append x (fun _ : Fin 2 => false)

def sumReal {ι : Type} (indices : List ι) (f : ι→RealPair) : RealPair :=
  indices.foldr (fun i acc => addReal (f i) acc) (0,0)

/-- All eight output rows and both initialized input columns are tested. -/
def rectangleError (first second : NativeMatrix) : RealPair :=
  sumReal basis (fun row => sumReal inputs (fun column =>
    normSq (sub (first row (initializedColumn column)) (second row (initializedColumn column)))))

def accepts (first second : NativeMatrix) (tolerance : ℚ) : Bool :=
  leRational (rectangleError first second) (tolerance^2)

end InfoLossLAR.WorstCase.FiniteGateNative

end

section

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport

abbrev CompileRequest := (List Unit×NativeMatrix)×ℚ

def compilerTest (a : ℕ) (input : CompileRequest×List ℕ) : Bool :=
  accepts (boundedMatrix a (input.1.1.1,input.2)) input.1.1.2 input.1.2

def compileWord (a : ℕ) (request : CompileRequest) : List ℕ :=
  let candidates := FiniteGateNativeEnumeration.search a request.1.1
  candidates[candidates.findIdx (fun codes => compilerTest a (request,codes))]?.getD []

end InfoLossLAR.WorstCase.FiniteGateNative

end

section

namespace InfoLossLAR.WorstCase.FiniteGateNative

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport

def compilerTolerance (budget : List Unit) : ℚ := 4/((budget.length : ℚ)+1)

def nativeCompile (a : ℕ) (input : List Unit×NativeMatrix) : List ℕ :=
  compileWord a (input,compilerTolerance input.1)

end InfoLossLAR.WorstCase.FiniteGateNative

end

section

namespace InfoLossLAR.WorstCase.NativePhaseGates

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport
open FiniteGateNative

abbrev Input := List Unit×NativePhaseTaylor.QFTRequest

def coefficient (z : Scalar) (row col : Bool) : Scalar :=
  if row=col then (if row then z else one) else zero

def target (x : NativePhaseTaylor.QFTRequest) : NativeMatrix :=
  singleGate (coefficient (NativePhaseTaylor.qftCurrent x)) 0

def current (a : ℕ) (x : Input) : List ℕ := nativeCompile a (x.1,target x.2)

/-- Linear unary buffers suffice because the requested error is inverse polynomial,
not exponentially small in the machine's input length. -/
def termBudget (budget : List Unit) : List Unit :=
  (budget++[()]).flatMap (fun _ => List.replicate 160 ())

abbrev AutomaticInput := List Unit×(List Unit×Bool)

def request (x : AutomaticInput) : NativePhaseTaylor.QFTRequest :=
  ((x.1++[()],x.2.1,termBudget x.1),x.2.2)

def automatic (a : ℕ) (x : AutomaticInput) : List ℕ := current a (x.1,request x)

end InfoLossLAR.WorstCase.NativePhaseGates

end

section

namespace InfoLossLAR.WorstCase.NativeQFTPlanCompile

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

open NativeQFTPlan
open FiniteGateTransport
open FiniteGateNative

/-- Unary wire count and unary inverse-error budget. -/
abbrev Input := List Unit × List Unit

/-- H/CNOT keep their tag and wire addresses; phase blocks carry an actual
native finite word on the three local wires. There is no real-valued field. -/
abbrev Block := ℕ × ℕ × ℕ × List ℕ

def automaticInput (x : List Unit × NativeQFTPlan.Instruction) : NativePhaseGates.AutomaticInput :=
  (x.1,((x.2.2.2.2).1.2.1,(x.2.2.2.2).2))

def compileCode (a : ℕ) (x : List Unit × NativeQFTPlan.Instruction) : Block :=
  (x.2.1,x.2.2.1,x.2.2.2.1,
    if x.2.1=1 then NativePhaseGates.automatic a (automaticInput x) else [])

/-- The automatic phase compiler generates its own precision buffers, so the
request-plan generator need only receive empty pi/Taylor placeholders. -/
def plan (x : Input) : List NativeQFTPlan.Instruction := NativeQFTPlan.current (x.1,[],[])

def current (a : ℕ) (x : Input) : List Block := (plan x).map (fun code => compileCode a (x.2,code))

end InfoLossLAR.WorstCase.NativeQFTPlanCompile

end

section

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms
open QAlgorithms.Complexity

open scoped BigOperators

/-- Relocating an instruction preserves its ordered control and target wires. -/
def Letter.relocate {k n : ℕ} (w : Fin k ↪ Fin n) : Letter k → Letter n
  | .h i => .h (w i)
  | .t i => .t (w i)
  | .cnot i j hij => .cnot (w i) (w j) (w.injective.ne hij)

end InfoLossLAR.WorstCase.FiniteGateTransport

end

section

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms
open QAlgorithms.Complexity

open scoped BigOperators

def freshPhaseWires {n : ℕ} (i : Fin n) : Fin 3 ↪ Fin (n+2) where
  toFun j := if j=0 then i.castAdd 2 else if j=1 then ⟨n,by omega⟩ else ⟨n+1,by omega⟩
  inj' := by
    intro j k h
    fin_cases j <;> fin_cases k <;> simp only [Fin.zero_eta,Fin.isValue,ite_true] at h ⊢ <;>
      first | rfl | (have hv:=congrArg Fin.val h;dsimp at hv;omega)

end InfoLossLAR.WorstCase.FiniteGateTransport

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.NativeQFTPlanCompile

open QAlgorithms
open QAlgorithms.Complexity
open FiniteGateTransport

open scoped BigOperators

/-- Finite-address interpretation of mixed blocks. No scalar or angle is read.
Malformed public addresses denote an empty physical word. -/
def physicalBlock (n : ℕ) (block : Block) : List (Letter (n+2)) :=
  if block.1=0 then
    if hi : block.2.1<n then [.h ((⟨block.2.1,hi⟩ : Fin n).castAdd 2)] else []
  else if block.1=1 then
    if hi : block.2.1<n then
      (FiniteGateNativeEnumeration.interpreted block.2.2.2).map
        (Letter.relocate (freshPhaseWires (⟨block.2.1,hi⟩ : Fin n)))
    else []
  else if block.1=2 then
    if hi : block.2.1<n then
      if hj : block.2.2.1<n then
        if hne : block.2.1≠block.2.2.1 then
          [.cnot ((⟨block.2.1,hi⟩ : Fin n).castAdd 2)
            ((⟨block.2.2.1,hj⟩ : Fin n).castAdd 2)
            (by intro h;exact hne (congrArg Fin.val h))]
        else []
      else []
    else []
  else []

end InfoLossLAR.WorstCase.NativeQFTPlanCompile

end

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.NativeQFTPlanCompile

open QAlgorithms
open QAlgorithms.Complexity
open FiniteGateTransport
open CoherentDecoder

open scoped BigOperators

/-- The physical word uses the same final two wires for every phase block. -/
def physicalWord (a : ℕ) (x : Input) : List (Letter (x.1.length+2)) :=
  (current a x).flatMap (physicalBlock x.1.length)

end InfoLossLAR.WorstCase.NativeQFTPlanCompile

end

end

section

open scoped Classical BigOperators

namespace GridReadout.Axis

open InfoLossLAR.WorstCase
open QAlgorithms
open QAlgorithms.Complexity
open FiniteGateTransport
open NativeQFTPlanCompile
open CoherentDecoder

noncomputable section

variable {b : ℕ}

def binaryFin (b : ℕ) : Bits b ≃ (Fin b → Fin 2) where
  toFun := finBits
  invFun z := fun i => decide (z i = 1)
  left_inv z := by funext i; cases h:z i <;> simp [finBits,h]
  right_inv z := by funext i; change (if decide (z i = 1) then 1 else 0) = z i; generalize z i = t; fin_cases t <;> rfl

def binary (b : ℕ) : Bits b ≃ ZMod (2^b) :=
  (binaryFin b).trans (finFunctionFinEquiv.trans (ZMod.finEquiv (2^b)).toEquiv)

end

end GridReadout.Axis

end

section

open scoped BigOperators Classical

namespace GridReadout.Axis

open InfoLossLAR.WorstCase
open QAlgorithms
open QAlgorithms.Complexity
open FiniteGateTransport
open NativeQFTPlanCompile
open CoherentDecoder

open FiniteLatticeFourier

noncomputable section

variable {b n : ℕ}

abbrev Rows (b n : ℕ) := Fin n → Bits b

def rowInput (b n : ℕ) : Rows b n ≃ (Fin n → ZMod (2^b)) := Equiv.piCongrRight fun _ => binary b

end

end GridReadout.Axis

end

section

open scoped BigOperators Classical

namespace GridReadout.Axis

open InfoLossLAR.WorstCase
open QAlgorithms
open QAlgorithms.Complexity
open FiniteGateTransport
open NativeQFTPlanCompile
open CoherentDecoder

noncomputable section

variable {n b : ℕ}

private theorem disjoint_wires {m k : ℕ} (i : Fin m) (j : Fin k) : i.castAdd k ≠ j.natAdd m := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

def dataWire (j : Fin n) (k : Fin b) : Fin (n*b+2) := (finProdFinEquiv (j,k)).castAdd 2

def auxWire (n b : ℕ) (k : Fin 2) : Fin (n*b+2) := k.natAdd (n*b)

def wires (b : ℕ) (i : Fin n) : Fin (b+2) ↪ Fin (n*b+2) where
  toFun := Fin.append (dataWire i) (auxWire n b)
  inj' := by
    intro p q h
    induction p using Fin.addCases with
    | left j =>
      induction q using Fin.addCases with
      | left k =>
        simp only [Fin.append_left,dataWire,Fin.castAdd_inj,Equiv.apply_eq_iff_eq,Prod.mk.injEq,true_and] at h
        rw [h]
      | right k =>
        simp only [Fin.append_left,Fin.append_right,dataWire,auxWire] at h
        exact False.elim (disjoint_wires _ _ h)
    | right j =>
      induction q using Fin.addCases with
      | left k =>
        simp only [Fin.append_left,Fin.append_right,dataWire,auxWire] at h
        exact False.elim (disjoint_wires _ _ h.symm)
      | right k =>
        simp only [Fin.append_right,auxWire,Fin.natAdd_inj] at h
        rw [h]

def rows (y : Bits (n*b+2)) : Rows b n := fun i k => y (dataWire i k)

def anc (n b : ℕ) (y : Bits (n*b+2)) : Bits 2 := fun k => y (auxWire n b k)

def liftRows (u : Rows b n → ℂ) : QState (n*b+2) :=
  fun y => if anc n b y=0 then u (rows y) else 0

end

end GridReadout.Axis

end

section

open scoped BigOperators Classical

namespace GridReadout.Axis

open InfoLossLAR.WorstCase
open QAlgorithms
open QAlgorithms.Complexity
open FiniteGateTransport
open NativeQFTPlanCompile
open CoherentDecoder

noncomputable section

def word {n : ℕ} (a : ℕ) (x : Input) (i : Fin n) := (physicalWord a x).map (Letter.relocate (wires x.1.length i))

def circuit {n : ℕ} (a : ℕ) (x : Input) (is : List (Fin n)) : Layered (n*x.1.length+2) :=
  is.map (fun i => instructions (word a x i))

end

end GridReadout.Axis

end

section

open scoped BigOperators Classical

namespace GridReadout.Axis

open InfoLossLAR.WorstCase
open QAlgorithms
open QAlgorithms.Complexity
open FiniteGateTransport
open NativeQFTPlanCompile
open CoherentDecoder

open CoherentProjection
open GaussianPoissonSeries
open FiniteLatticeFourier
open IntegerBasis
open RegevLWE.GaussConv

noncomputable section

variable {n b : ℕ}

def reindex {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) (v : EuclideanSpace ℂ Y) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun x => v (e x))

abbrev inputState (r : EuclideanSpace ℂ (Fin n → ZMod (2^b))) := normalized (reindex (rowInput b n) r)

def dualInput (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (r : ℝ) : EuclideanSpace ℂ (Fin n → ZMod (2^b)) :=
  periodizedState (modulus:=2^b) (dual (inputLattice B hB)) (dualIntegerBasis B hB) (1/(Real.sqrt 2*r))

end

end GridReadout.Axis

end

section

namespace GridReadout.Axis

open InfoLossLAR.WorstCase
open NativeQFTPlanCompile
open FiniteGateTransport

noncomputable section

def precision (n b k : ℕ) : ℕ := 200*n*b*(b+1)*(k+1)

end

end GridReadout.Axis

end

section

namespace InfoLossLAR.WorstCase

open QAlgorithms.Complexity

/-- A valid layered inverse circuit, using one gate per layer and no new wires. -/
def inverseCircuit {n : ℕ} (circuit : Layered n) : Layered n :=
  (inverseGates circuit.flatten).map (fun g => [g])

end InfoLossLAR.WorstCase

end

section

namespace InfoLossLAR.WorstCase.CoherentComputeUncompute

open FiniteGateTransport

open scoped BigOperators

variable {D W I : Type*} [Fintype D] [Fintype W] [DecidableEq W]

noncomputable def basis (w : W) : W → ℂ := fun r => if r=w then 1 else 0

end InfoLossLAR.WorstCase.CoherentComputeUncompute

end

section

namespace InfoLossLAR.WorstCase.CoherentComputeUncompute

open scoped BigOperators

variable {I W : Type*} [Fintype I] [Fintype W] [DecidableEq W]

/-- An analysis map storing all coherent indices in distinct physical basis
states. This specifies amplitudes and is not asserted to be a circuit. -/
noncomputable def basisEmbedding (e : I ↪ W) : (I → ℂ) →ₗ[ℂ] (W → ℂ) where
  toFun ψ := ∑ i,ψ i • basis (e i)
  map_add' ψ φ := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c ψ := by simp [mul_smul,Finset.smul_sum]

end InfoLossLAR.WorstCase.CoherentComputeUncompute

end

section

namespace InfoLossLAR.WorstCase.ControlledNativeGates

open QAlgorithms
open QAlgorithms.Complexity
open FiniteGateTransport


open scoped BigOperators

noncomputable def stateNorm {n : ℕ} (ψ : QState n) : ℝ :=
  ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Bits n))‖

end InfoLossLAR.WorstCase.ControlledNativeGates

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentXorCopy

open QAlgorithms
open QAlgorithms.Complexity
open CoherentComputeUncompute


open scoped BigOperators

variable {W k : ℕ}

def gate (controls : Fin k → Fin W) (i : Fin k) : ReversibleGate (W+k) :=
  .controlled ((controls i).castAdd k) (Fin.natAdd W i) (by
    intro h;have hv:=congrArg Fin.val h;dsimp at hv;have hi:=(controls i).isLt;omega)

/-- Actual finite CNOTs copy all requested output bits into an arbitrary
separate register by XOR. Repeated controls are permitted; targets are distinct. -/
def circuit (controls : Fin k → Fin W) : Layered (W+k) :=
  compileReversible ((List.finRange k).map (gate controls))

end InfoLossLAR.WorstCase.CoherentXorCopy

end

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.QuantumXorOracle

open QAlgorithms
open QAlgorithms.Complexity
open CoherentComputeUncompute
open ControlledNativeGates

variable {W k : ℕ}

/-- The real forward quantum procedure, real output CNOTs, and real
inverse gate sequence. This is valid even when U computes probabilistically. -/
def circuit (U : Layered W) (controls : Fin k→Fin W) : Layered (W+k) :=
  leftCircuit U++CoherentXorCopy.circuit controls++leftCircuit (inverseCircuit U)

end InfoLossLAR.WorstCase.QuantumXorOracle

end

end

section

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder

open QAlgorithms
open QAlgorithms.Complexity
open QuantumXorOracle
open ControlledNativeGates

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

noncomputable section

def prefixBits (k : ℕ) (w : Str) : Bits k := fun i => w[i.val]?.getD false

def controls (F : MFamily) (l k : ℕ) (h : k ≤ F.outLen l) : Fin k → Fin (l+(F.anc l+1)) :=
  fun j => F.outW l (Fin.castLE h j)

end

end InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder

end

section

namespace InfoLossLAR.WorstCase.FiniteGateTransport

open QAlgorithms.Complexity

open scoped BigOperators

/-- Relocate all five actual gate constructors along public physical wires. -/
def relocateInstr {k n : ℕ} (w : Fin k ↪ Fin n) : Instr k → Instr n
  | .h i => .h (w i)
  | .s i => .s (w i)
  | .t i => .t (w i)
  | .x i => .x (w i)
  | .cnot i j h => .cnot (w i) (w j) (w.injective.ne h)

def relocateCircuit {k n : ℕ} (w : Fin k ↪ Fin n) (circuit : Layered k) : Layered n :=
  circuit.map (List.map (relocateInstr w))

end InfoLossLAR.WorstCase.FiniteGateTransport

end

section

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder

open CoherentComputeUncompute
open QAlgorithms
open QAlgorithms.Complexity
open QuantumXorOracle
open ControlledNativeGates

noncomputable section

variable {n l k a r : ℕ} {I : Type} [Fintype I]

def oracleWord (x : Bits l) (d : Bits k) (tag : Bits r) : Bits (l+(a+1)+k+r) :=
  Fin.append (Fin.append (Fin.append x (fun _ : Fin (a+1) => false)) d) tag

def oracleEmbedding (x : I → Bits l) (d : I → Bits k) (tag : I ↪ Bits r) : I ↪ Bits (l+(a+1)+k+r) where
  toFun i := oracleWord (x i) (d i) (tag i)
  inj' := by
    intro i j h
    apply tag.injective
    funext u
    exact (Fin.append_right _ _ u).symm.trans ((congrFun h (u.natAdd _)).trans (Fin.append_right _ _ u))

end

end InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder

end

section

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms
open QAlgorithms.Complexity
open FiniteGateTransport
open ControlledNativeGates
open CoherentComputeUncompute

noncomputable section

/-- Wire permutation from the oracle view (query, work, signed answer,
prefix and suffix) to the serialized view (prefix, signed answer, query,
suffix, work). The prefix includes actual Fourier bits, the suffix includes
the retained residual, and all offsets are ordinary public integer sums. -/
def oraclePerm (H K L J A : ℕ) : Fin (L+A+K+(H+J)) ≃ Fin (H+K+L+J+A) where
  toFun i := ⟨if i.val<L then H+K+i.val else if i.val<L+A then H+K+L+J+(i.val-L)
    else if i.val<L+A+K then H+(i.val-(L+A)) else if i.val<L+A+K+H then i.val-(L+A+K)
    else H+K+L+(i.val-(L+A+K+H)),by split_ifs <;> omega⟩
  invFun j := ⟨if j.val<H then L+A+K+j.val else if j.val<H+K then L+A+(j.val-H)
    else if j.val<H+K+L then j.val-(H+K) else if j.val<H+K+L+J then L+A+K+H+(j.val-(H+K+L))
    else L+(j.val-(H+K+L+J)),by split_ifs <;> omega⟩
  left_inv := by intro i;apply Fin.ext;dsimp only;split_ifs <;> omega
  right_inv := by intro i;apply Fin.ext;dsimp only;split_ifs <;> omega

def wirePull {p N : ℕ} (e : Fin p ≃ Fin N) : Bits N ≃ Bits p where
  toFun x := x ∘ e
  invFun y := y ∘ e.symm
  left_inv x := by funext i;simp
  right_inv x := by funext i;simp

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end

section

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms
open QAlgorithms.Complexity
open FiniteGateTransport
open ControlledNativeGates
open CoherentComputeUncompute
open QuantumXorOracle

open PaddedDecoder


noncomputable section

variable {H K L J A : ℕ}

def frontRear {I : Type} (h : I → Bits H) (j : I → Bits J)
    (hi : Function.Injective (fun i => (h i,j i))) : I ↪ Bits (H+J) where
  toFun i := Fin.append (h i) (j i)
  inj' := by
    intro i k e
    apply hi
    apply Prod.ext
    · funext a
      simpa only [Fin.append_left] using congrFun e (a.castAdd J)
    · funext a
      simpa only [Fin.append_right] using congrFun e (a.natAdd H)

def emittedBasis {I : Type} (h : I → Bits H) (j : I → Bits J) (hi : Function.Injective (fun i => (h i,j i)))
    (x : I → Bits L) (d : I → Bits K) : I ↪ Bits (H+K+L+J+(A+1)) :=
  (oracleEmbedding (a:=A) x d (frontRear h j hi)).trans (wirePull (oraclePerm H K L J (A+1))).symm.toEmbedding

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end


