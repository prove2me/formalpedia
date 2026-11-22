-- Prove2me | Definitions.Def_InfoLossLAR_CoherentGaussianTickets
-- name    : InfoLossLAR_CoherentGaussianTickets
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T06:08:54.184736+00:00
-- url     : https://prove2.me/theorems/5f0ebc68-1749-4967-9138-3e68934d8558
-- title:
--   Finite registers for coherent Gaussian ticket rejection
-- statement:
--   The register convention specifies a dyadic proposal ticket, the finite interpretation circuit for each trial, and the recovered output after coherently selecting the first success among repeated trials. It records the computational basis input, the normalized target, the spectator indexing and the quantitative single-trial error. The gate-word size certificate is an explicit parameter so the same physical specification applies with any proof of its polynomial bound.
-- source:
--   Register contract for Gaussian preparation used in https://prove2.me/theorems/912efb88-48a6-4e10-b841-1070dd0ad365

import Definitions.Def_InfoLossLAR_BDD_Coordinates
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_05
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_06_Optimized
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_07
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_08
import Definitions.Def_InfoLossLAR_LoadedBatchBundle_01
import Definitions.Def_InfoLossLAR_ReciprocallyScaledGaussianSource
import Definitions.Def_InfoLossLAR_RegevSearch_FourierGrid
import Definitions.Def_InfoLossLAR_RegevSearch_PhysicalFourierReadout
import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Definitions.Def_InfoLossLAR_RuntimeBundle_01
import Definitions.Def_InfoLossLAR_RuntimeBundle_02
import Definitions.Def_InfoLossLAR_RuntimeBundle_03
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ShorAlgorithms_QFT_Circuit
import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

section

namespace AFT.GaussianSource

open scoped BigOperators Classical

noncomputable def shiftedWeight (width center : ℝ) (z : ℤ) : ℝ :=
  Real.exp (-(Real.pi / width ^ 2) * ((z : ℝ) - center) ^ 2)

end AFT.GaussianSource

end

section

namespace InfoLossLAR.WorstCase.ControlledNativeCode

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

/-- Tag 5 is an exact ideal eighth phase in the input plan only. The Boolean
is its sign. The output has only the five finite native gate tags. -/
abbrev AtomCode := GateCode×Bool

def decodeGate (n : ℕ) (code : GateCode) : Option (Instr n) :=
  if hi : code.2.1< n then
    match code.1 with
    | 0 => some (.h ⟨code.2.1,hi⟩)
    | 1 => some (.s ⟨code.2.1,hi⟩)
    | 2 => some (.t ⟨code.2.1,hi⟩)
    | 3 => some (.x ⟨code.2.1,hi⟩)
    | 4 => if hj : code.2.2< n then
        if hij : code.2.1≠code.2.2 then some (.cnot ⟨code.2.1,hi⟩ ⟨code.2.2,hj⟩ (by
          intro h;exact hij (congrArg Fin.val h))) else none
      else none
    | _ => none
  else none

def localTable : List GateCode := alphabet.map (fun letter => encodeInstr letter.toInstr)

def localCode (code : ℕ) : GateCode := localTable[code]?.getD (0,0,0)

abbrev Layout := ℕ×ℕ×ℕ

def address (layout : Layout) (wire : ℕ) : ℕ :=
  if wire=0 then layout.1 else if wire=1 then layout.2.1 else layout.2.2

def relocateCode (layout : Layout) (gate : GateCode) : GateCode :=
  (gate.1,address layout gate.2.1,if gate.1=4 then address layout gate.2.2 else 0)

abbrev PhaseInput := (List Unit×Layout)×Bool

def phaseCodes (a : ℕ) (x : PhaseInput) : List GateCode :=
  (NativePhaseGates.automatic a (x.1.1,([(),()],x.2))).map
    (fun code => relocateCode x.1.2 (localCode code))

/-- The input contains an ordinary finite ideal atom sequence and addresses
of two reserved ancillas. No real angle or amplitude is read. -/
abbrev Input := (List Unit×(ℕ×ℕ))×List AtomCode

def atomCodes (a : ℕ) (x : (List Unit×(ℕ×ℕ))×AtomCode) : List GateCode :=
  if x.2.1.1=5 then phaseCodes a ((x.1.1,(x.2.1.2.1,x.1.2.1,x.1.2.2)),x.2.2)
  else [x.2.1]

def compile (a : ℕ) (x : Input) : List GateCode := x.2.flatMap (fun atom => atomCodes a (x.1,atom))

end InfoLossLAR.WorstCase.ControlledNativeCode

end

section

namespace InfoLossLAR.WorstCase.CoherentProjection

open scoped BigOperators

noncomputable def tensorState {O J : Type*} [Fintype O] [Fintype J]
    (target : EuclideanSpace ℂ O) (junk : EuclideanSpace ℂ J) : EuclideanSpace ℂ (O×J) :=
  WithLp.toLp 2 (fun p => target p.1*junk p.2)

end InfoLossLAR.WorstCase.CoherentProjection

end

section

namespace InfoLossLAR.WorstCase.ControlledPlanNative

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

/-- Exact finite inverse expansion: S inverse is S^3 and T inverse is T^7. -/
def inverseCode (gate : GateCode) : List GateCode :=
  if gate.1=1 then (List.replicate 3 ()).map (fun _ => gate)
  else if gate.1=2 then (List.replicate 7 ()).map (fun _ => gate)
  else [gate]

def turnCodes (target : ℕ) : List GateCode :=
  [(0,target,0),(1,target,0),(1,target,0),(1,target,0),(0,target,0),(2,target,0),(0,target,0),(1,target,0)]

def inverseTurnCodes (target : ℕ) : List GateCode := (turnCodes target).reverse.flatMap inverseCode

def hPlan (control target : ℕ) : List AtomCode :=
  (inverseTurnCodes target++[(4,control,target)]++turnCodes target).map (fun gate => (gate,false))

def tPlan (control target : ℕ) : List AtomCode :=
  [((5,control,0),false),((5,target,0),false),((4,control,target),false),
   ((5,target,0),true),((4,control,target),false)]

def cnotPlan (p q r : ℕ) : List AtomCode :=
  [(0,r,0),
   (2,p,0),(2,q,0),(2,r,0),
   (4,p,q),
   (2,q,0),(2,q,0),(2,q,0),(2,q,0),(2,q,0),(2,q,0),(2,q,0),
   (4,p,q),(4,q,r),
   (2,r,0),(2,r,0),(2,r,0),(2,r,0),(2,r,0),(2,r,0),(2,r,0),
   (4,q,r),(4,p,r),
   (2,r,0),(2,r,0),(2,r,0),(2,r,0),(2,r,0),(2,r,0),(2,r,0),
   (4,p,r),(4,p,r),(4,q,r),(2,r,0),(4,q,r),(4,p,r),(0,r,0)].map (fun gate => (gate,false))

def gatePlan (control : ℕ) (gate : GateCode) : List AtomCode :=
  if gate.1=0 then hPlan control gate.2.1
  else if gate.1=2 then tPlan control gate.2.1
  else if gate.1=4 then cnotPlan control gate.2.1 gate.2.2
  else []

/-- Public control address, three public data addresses, and one fixed-alphabet
letter code. This is an ordinary total finite-data generator. -/
abbrev Input := ℕ×(Layout×ℕ)

def current (x : Input) : List AtomCode := gatePlan x.1 (relocateCode x.2.1 (localCode x.2.2))

end InfoLossLAR.WorstCase.ControlledPlanNative

end

section

namespace InfoLossLAR.WorstCase.NativeWordControls

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport FiniteGateNativeEnumeration

abbrev Input := List ℕ×List Unit

/-- Out-of-alphabet values use precisely the same H0 fallback as letterOfCode. -/
def normalizedCode (code : ℕ) : ℕ := if code<12 then code else 0

def selected (x : Input×(ℕ×ℕ)) : Bool :=
  decide (x.2.1<x.1.1.length) &&
    decide (normalizedCode (x.1.1[x.2.1]?.getD 0)=x.2.2)

@[fun_prop] private theorem normalizedCode_poly : Poly normalizedCode := by unfold normalizedCode;fun_prop

@[fun_prop] private theorem selected_poly : Poly selected := by unfold selected;fun_prop

end InfoLossLAR.WorstCase.NativeWordControls

end

section

namespace InfoLossLAR.WorstCase.TM2Boolean

open Turing QAlgorithms.Complexity

open Integration9_9.TM2OutputLength

variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

variable {width : ℕ}

private theorem wordExtension_before (word : List Bool) (i : ℕ) (h : i < word.length) :
    wordExtension word i = word[i] := by simp only [wordExtension, List.getElem?_eq_getElem h, Option.getD_some]

end InfoLossLAR.WorstCase.TM2Boolean

end

section

namespace InfoLossLAR.WorstCase.NativeWordControls

open QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PolynomialBudget

/-- Raw one-hot output bits, in slot-major and alphabet-minor order. -/
def rawControls (x : Input) : List Bool :=
  (List.range (12*x.2.length)).map (fun index => selected (x,(index/12,index%12)))

@[fun_prop] private theorem rawControls_poly : Poly rawControls := by
  unfold rawControls
  apply Poly.list_map
  · fun_prop
  · have h : Poly (fun x : Input => (x.2++x.2++x.2++x.2++x.2++x.2++
        x.2++x.2++x.2++x.2++x.2++x.2)) := by fun_prop
    have hi := Poly.comp Poly.list_indices h
    convert hi using 1
    funext x
    congr 1
    simp only [List.length_append]
    omega

def rawCurrent (words : Str → List ℕ) (p : Polynomial ℕ) (word : Str) : Str :=
  rawControls (words word,List.replicate (p.eval word.length) ())

@[fun_prop] private theorem rawCurrent_poly (words : Str → List ℕ) (hw : Poly words)
    (p : Polynomial ℕ) : Poly (rawCurrent words p) := by
  unfold rawCurrent
  apply Poly.comp rawControls_poly
  apply Poly.pair hw
  have hp := polynomialSlots_poly p
  simpa only [List.length_map] using
    Poly.comp hp (by fun_prop : Poly (fun word : Str => word.map (fun _ => ())))

/-- An actual raw-string TM2 program, suitable for the reversible compiler. -/
noncomputable def rawCurrentProgram (words : Str → List ℕ) (hw : Poly words)
    (p : Polynomial ℕ) : PolyProgram id id (rawCurrent words p) := by
  let P := (BooleanLists.packProgram.comp (rawCurrent_poly words hw p).program).comp BooleanLists.unpackProgram
  exact P.congr _ (fun _ => rfl)

end InfoLossLAR.WorstCase.NativeWordControls

end

section

namespace InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open Integration9_9.TM2OutputLength

/-- The real machine's complete output fits in the compiled finite slot register. -/
private theorem actualOutput_length_lt_capacity {f : Str → Str} (P : PolyProgram id id f) (word : Str) :
    (f word).length<capacity P word.length := by
  have h := output_length_le P.machine.tm word (f word) (P.time.eval word.length) (P.outputs word)
  change (f word).length≤word.length+programPushBound P.machine.code*P.time.eval word.length at h
  unfold capacity
  omega

end InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

namespace Integration9_9.LARCoinLayout

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.TM2Boolean.PolyProgramCircuit

open QAlgorithms.Complexity Polynomial

open OAI.MetricKMedian.Binary

open LARRankOneMachine

end Integration9_9.LARCoinLayout

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordLayout

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open TM2Boolean TM2Boolean.PolyProgramCircuit CodeGenerator

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PolynomialBudget

variable {f : Str → Str} (P : PolyProgram id id f) (p : Polynomial ℕ)

local instance : DecidableEq P.machine.Label := Classical.decEq _

local instance : DecidableEq P.machine.State := Classical.decEq _

/-- Exact width of the entire generated reversible machine, including its
old input, all work/output wires, and the reserved guard wire. -/
def machineWidth (word : Str) : ℕ :=
  word.length+(generate P.machine.code P.machine.input P.machine.main P.machine.initial (request P word)).2.2.2.length+1

def width (n : ℕ) : ℕ := n+((compiled P n).ops.length+1)

def slots (word : Str) : List Unit := List.replicate (p.eval word.length) ()

def address (word : Str) (slot code : ℕ) : ℕ := generatedProgramOutputAddress P word (12*slot+code)

/-- This public generator reads the unary input length only. Native output
bits remain in the reversible machine and serve as physical controls. -/
def atomGrid (word : Str) : List ControlledNativeCode.AtomCode :=
  (List.range (slots p word).length).flatMap (fun slot => (List.range 12).flatMap
    (fun code => ControlledPlanNative.current (address P word slot code,
      ((machineWidth P word,machineWidth P word+1,machineWidth P word+2),code))))

/-- Compile all public control operations using exactly the same last two
ancillas for every eighth phase in the full operation grid. -/
def current (a : ℕ) (x : Str×List Unit) : List ControlledNativeCode.GateCode :=
  ControlledNativeCode.compile a
    ((x.2,(machineWidth P x.1+3,machineWidth P x.1+4)),atomGrid P p x.1)

end InfoLossLAR.WorstCase.NativeWordLayout

end

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordCoherent

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open NativeWordLayout ControlledNativeGates

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

variable (words : Str → List ℕ) (hw : Poly words) (p : Polynomial ℕ)

abbrev P : PolyProgram id id (NativeWordControls.rawCurrent words p) := NativeWordControls.rawCurrentProgram words hw p

end InfoLossLAR.WorstCase.NativeWordCoherent

end

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordCoherent

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open NativeWordLayout ControlledNativeGates

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

variable (words : Str → List ℕ) (hw : Poly words) (p : Polynomial ℕ)

def initialWork (n : ℕ) (word : Str) : Bits (width (P words hw p) n) :=
  fun i => wordExtension word i.val

variable {I : Type*} [Fintype I]

end InfoLossLAR.WorstCase.NativeWordCoherent

end

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordCoherent

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open scoped BigOperators

/-- Append arbitrary data/reference wires; original instruction addresses
remain fixed and every CNOT control/target remains distinct. -/
def extendInstr (k : ℕ) {W : ℕ} : Instr W → Instr (W+k)
  | .h i => .h (i.castAdd k)
  | .s i => .s (i.castAdd k)
  | .t i => .t (i.castAdd k)
  | .x i => .x (i.castAdd k)
  | .cnot i j h => .cnot (i.castAdd k) (j.castAdd k) (by intro he;exact h (Fin.castAdd_inj.mp he))

def extendCircuit (k : ℕ) {W : ℕ} (gates : Layered W) : Layered (W+k) :=
  gates.map (List.map (extendInstr k))

end InfoLossLAR.WorstCase.NativeWordCoherent

end

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordCoherent

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open NativeWordLayout ControlledNativeGates

open TM2Boolean TM2Boolean.PolyProgramCircuit

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

variable (words : Str → List ℕ) (hw : Poly words) (p : Polynomial ℕ)

variable {I : Type*} [Fintype I]

/-- Give the verified circuit its exact public register-width interface. -/
def baseCircuit (n : ℕ) : Layered (width (P words hw p) n) := circuit (P words hw p) n

def nativeMiddle (n a : ℕ) (budget : List Unit) : List (Instr (width (P words hw p) n+5)) :=
  (NativeWordLayout.current (P words hw p) p a (unary n,budget)).filterMap
    (ControlledNativeCode.decodeGate (width (P words hw p) n+3+2))

def wholeCircuit (n a : ℕ) (budget : List Unit) : Layered (width (P words hw p) n+5) :=
  extendCircuit 5 (baseCircuit words hw p n)++
    (nativeMiddle words hw p n a budget).map (fun gate => [gate])++
    extendCircuit 5 (inverseCircuit (baseCircuit words hw p n))

end InfoLossLAR.WorstCase.NativeWordCoherent

end

end

section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 TM2NativeFiniteDraw

open scoped BigOperators

def numeratorTicks (squaredWidth : ℚ) : List Unit := (Nat.bits squaredWidth.num.natAbs).map (fun _ => ())

def rawScaleTicks (squaredWidth : ℚ) : List Unit :=
  (numeratorTicks squaredWidth).drop (Nat.size squaredWidth.den)++[(),()]

def scaleTicks (squaredWidth : ℚ) : List Unit :=
  (rawScaleTicks squaredWidth).take ((rawScaleTicks squaredWidth).length/2)

def scale (squaredWidth : ℚ) : ℕ := dyadicPower (scaleTicks squaredWidth)

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end

section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 TM2NativeGaussian

open scoped BigOperators

abbrev PointRequest := (ℚ × ℚ) × (List Unit × List Unit)

def variance (input : PointRequest) : ℚ := if 1 ≤ input.1.1 then input.1.1 else 1

def radius (input : PointRequest) : ℕ := input.2.1.length*scale (variance input)

def intervalCount (input : PointRequest) : ℕ := 2*radius input+1

def anchorInteger (center : ℚ) : ℤ := (GaussianRandomizedRounding.Native.anchor center).num

/-- One random binary interval ticket becomes its translated integer point. -/
def point (input : PointRequest × ℕ) : ℤ := anchorInteger input.1.1.2+(input.2 : ℤ)-(radius input.1 : ℤ)

def pointRatio (input : PointRequest × ℕ) : ℚ := ((point input : ℚ)-input.1.1.2)^2/variance input.1

/-- The exponent loop guard is polynomial in the unary radius multiplier,
and independent of the numerical magnitude of the binary Gaussian width. -/
def pointGuardTicks (input : PointRequest) : List Unit :=
  ((input.2.1++[()]).flatMap (fun _ => input.2.1++[()])).flatMap (fun _ => List.replicate 8 ())

def pointValue (input : PointRequest × ℕ) : ℚ :=
  gaussianCapped ((pointRatio input,input.1.2.2),pointGuardTicks input.1)

noncomputable section

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end

section

namespace InfoLossLAR.WorstCase.NativeSquareRoot

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

abbrev Input := ℚ×List Unit

def capacity (x : Input) : ℕ := x.2.length+1

def test (x : Input×ℕ) : Bool :=
  decide (x.1.1<(((x.2+1 : ℕ) : ℚ)/(capacity x.1 : ℚ))*
    (((x.2+1 : ℕ) : ℚ)/(capacity x.1 : ℚ)))

def index (x : Input) : ℕ :=
  (List.range (capacity x)).findIdx (fun i => test (x,i))

def current (x : Input) : ℚ := (index x : ℚ)/(capacity x : ℚ)

end InfoLossLAR.WorstCase.NativeSquareRoot

end

section

namespace InfoLossLAR.WorstCase.AcceptanceRotation

open QAlgorithms FiniteGateTransport

open scoped BigOperators

abbrev Input := NativeSquareRoot.Input

def cValue (x : Input) : ℚ := NativeSquareRoot.current (1-x.1,x.2)

def sValue (x : Input) : ℚ := NativeSquareRoot.current x

def coefficient (x : Input) (row col : Bool) : FiniteGateNative.Scalar :=
  let v := if row then (if col then cValue x else sValue x)
    else (if col then -sValue x else cValue x)
  ((v,0),(0,0))

def nativeTarget (x : Input) : FiniteGateNative.NativeMatrix :=
  FiniteGateNative.singleGate (coefficient x) 0

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

end InfoLossLAR.WorstCase.AcceptanceRotation

end

section

namespace InfoLossLAR.WorstCase.CoherentWeightedPreparation

open QAlgorithms FiniteGateTransport

open scoped BigOperators

variable {O : Type*} [Fintype O] [Nonempty O]

noncomputable def weightSum (w : O → ℝ) : ℝ := ∑ o,w o

noncomputable def target (w : O → ℝ) (o : O) : ℂ :=
  (Real.sqrt (w o)/Real.sqrt (weightSum w) : ℝ)

end InfoLossLAR.WorstCase.CoherentWeightedPreparation

end

section

namespace InfoLossLAR.WorstCase.NativeAcceptanceGates

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open FiniteGateTransport FiniteGateNative

abbrev Input := ℚ×List Unit

def sqrtBudget (budget : List Unit) : List Unit := budget++budget++[()]

def target (x : Input) : NativeMatrix := AcceptanceRotation.nativeTarget (x.1,sqrtBudget x.2)

def current (a : ℕ) (x : Input) : List ℕ := nativeCompile a (x.2,target x)

end InfoLossLAR.WorstCase.NativeAcceptanceGates

end

section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

open AFT GaussianSource RationalNumerics

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

/-- The entire binary ticket cube is the uniform coherent proposal space. -/
def ticketCount (input : PointRequest) : ℕ := 2^Nat.size (intervalCount input)

abbrev Ticket (input : PointRequest) := Fin (ticketCount input)

def numericalProbability (x : PointRequest×ℕ) : ℚ :=
  if x.2 < intervalCount x.1 then Integration9_9.TM2NativeFiniteDraw.clipped (pointValue x) else 0

noncomputable def weight (input : PointRequest) (width : ℝ) (index : ℕ) : ℝ :=
  if index < intervalCount input then shiftedWeight width input.1.2 (point (input,index)) else 0

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

end

section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open QAlgorithms FiniteGateTransport FiniteGateNativeEnumeration

abbrev GateInput := (PointRequest×ℕ)×List Unit

/-- The input-dependent acceptance word is computed from the binary ticket,
using the actual guarded rational Gaussian evaluator. -/
def gateWord (a : ℕ) (x : GateInput) : List ℕ :=
  NativeAcceptanceGates.current a (numericalProbability x.1,x.2)

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

end

section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

/-- Literal little-endian ticket semantics of the physical proposal qubits. -/
def proposalTicket (input : PointRequest) : Bits (Nat.size (intervalCount input)) ≃ Ticket input :=
  boundedBoolTicket (Nat.size (intervalCount input))

/-- Reading the public binary word is a real polynomial-time operation,
not an arbitrary finite-type decoding oracle. -/
def gateWordBits (a : ℕ) (x : (PointRequest×List Bool)×List Unit) : List ℕ :=
  gateWord a ((x.1.1,QMCNumericRuntime.bitValue x.1.2),x.2)

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent

end

section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder

open QAlgorithms QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2PolynomialBudget

/-- A self-delimited copy of the original public binary input, which may
contain the original integer basis and all public numerical controls. -/
def publicHeader (word : Str) : Str := lengthToken word++word

def paddedPublic (slots : List Unit) (word : Str) : Str :=
  (publicHeader word++slots.map (fun _ => false)).take slots.length

@[simp] private theorem paddedPublic_length (slots : List Unit) (word : Str) : (paddedPublic slots word).length=slots.length := by
  simp only [paddedPublic,List.length_take,List.length_append,List.length_map]
  omega

def rawInput (slots : List Unit) (word tape : Str) : Str := lengthToken slots++paddedPublic slots word++tape

@[simp] private theorem rawInput_length (slots : List Unit) (word tape : Str) :
    (rawInput slots word tape).length=2*slots.length+1+tape.length := by
  simp only [rawInput,List.length_append,paddedPublic_length,lengthToken,List.length_map,List.length_singleton]
  omega

/-- Recover exactly the original public word and the final fixed-capacity
binary ticket block. Both lengths are bounded by tokens actually present. -/
def parsePublic (word : Str) : Str×Str :=
  let u := readUnary word
  let b := readUnary u.2
  (b.2.take (unarySlots u.2).length,u.2.drop (unarySlots word).length)

variable (request : Str→PointRequest×List Unit) (hr : Poly request)

/-- The real native public-input computation runs inside the reversible
word program; rational variance and center are never supplied by an oracle. -/
def parse (word : Str) : (PointRequest×Str)×List Unit :=
  let decoded :=  parsePublic word
  let x := request decoded.1
  ((x.1,decoded.2.take (Nat.bits (intervalCount x.1)).length),x.2)

def gateWord (a : ℕ) (word : Str) : List ℕ := gateWordBits a (parse request word)

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.NativeWordCoherent

open QAlgorithms QAlgorithms.Complexity NativeWordLayout ControlledNativeGates

open FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean

open scoped BigOperators

variable (words : Str → List ℕ) (hw : Poly words) (p : Polynomial ℕ)

private theorem initialWork_injective (n : ℕ) (a b : Str) (ha : a.length=n) (hb : b.length=n)
    (he : initialWork words hw p n a=initialWork words hw p n b) : a=b := by
  apply List.ext_getElem
  · omega
  · intro i hi hj
    have hwidth : i < width (P words hw p) n := by unfold width;omega
    have hh := congrFun he ⟨i,hwidth⟩
    change wordExtension a i=wordExtension b i at hh
    simpa only [wordExtension_before a i hi,wordExtension_before b i hj] using hh

variable {I : Type*} [Fintype I] [DecidableEq I]

end InfoLossLAR.WorstCase.NativeWordCoherent

end

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open NativeWordCoherent NativeWordLayout ControlledNativeGates FiniteGateNativeEnumeration

open Integration9_9.TM2PlatformSerialization

def activeTicket (input : PointRequest) {K : ℕ}
    (hK : Nat.size (intervalCount input)≤K) (tape : Bits K) : Ticket input :=
  proposalTicket input (Fin.take _ hK tape)

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding

end

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open NativeWordCoherent NativeWordLayout ControlledNativeGates FiniteGateNativeEnumeration

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2PolynomialBudget

def encoded (slots : List Unit) (word : Str) {K : ℕ} (tape : Bits K) : Str :=
  rawInput slots word (List.ofFn tape)

private theorem encoded_length (slots : List Unit) (word : Str) {K : ℕ} (tape : Bits K) :
    (encoded slots word tape).length=2*slots.length+1+K := by
  simp only [encoded,rawInput_length,List.length_ofFn]

private theorem encoded_injective (slots : List Unit) (word : Str) (K : ℕ) :
    Function.Injective (encoded slots word (K:=K)) := by
  intro a b h
  have hh := congrArg (List.drop (lengthToken slots++paddedPublic slots word).length) h
  simp only [encoded,rawInput,List.drop_left] at hh
  exact List.ofFn_inj.mp hh

variable (request : Str→PointRequest×List Unit) (hr : _root_.OAI.MetricKMedian.Binary.Automatic.Poly request)

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder

end

end

section

namespace InfoLossLAR.WorstCase.CoherentRejection

open scoped BigOperators

open CoherentProjection

variable {O J : Type*} [Fintype O] [Fintype J] [DecidableEq O] {m : ℕ}

abbrev Retained (O J : Type*) (m : ℕ) := (Fin m → Bool)×(Fin m → O×J)

end InfoLossLAR.WorstCase.CoherentRejection

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport CoherentWeightedPreparation

open scoped BigOperators

def capacityWeight (input : PointRequest) (s : ℝ) (K : ℕ)
    (hK : Nat.size (intervalCount input)≤K) (tape : Bits K) : ℝ :=
  weight input s (activeTicket input hK tape).val

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding

end

end

section

namespace InfoLossLAR.WorstCase.CoherentControlledSwap

open QAlgorithms.Complexity

/-- A Fredkin gate built only from the platform's H/T/CNOT instruction set. -/
def gates {n : ℕ} (c i j : Fin n) (hci : c≠i) (hcj : c≠j) (hij : i≠j) : List (Instr n) :=
  [.cnot j i hij.symm]++toffoliGates c i j hci hcj hij++[.cnot j i hij.symm]

open ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

end InfoLossLAR.WorstCase.CoherentControlledSwap

end

section

namespace InfoLossLAR.WorstCase.CoherentRejection

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

/-- Exact first-success one-hot controls; the all-failure case gives all false. -/
def controls (flags : List Bool) : List Bool :=
  (List.range flags.length).map (fun index => decide (flags.findIdx id=index))

@[fun_prop] private theorem controls_poly : Poly controls := by
  have hf : Poly (fun flags : List Bool => flags.findIdx id) :=
    Poly.list_findIdx Poly.snd (by fun_prop)
  unfold controls
  apply Poly.list_map
  · exact Poly.nat_eq_comp (Poly.comp hf Poly.fst) Poly.snd
  · exact Poly.list_indices

@[simp] private theorem controls_length (flags : List Bool) : (controls flags).length=flags.length := by
  simp [controls]

/-- The actual raw Boolean TM2 program is suitable for the verified
reversible compiler; it reads only the retained success flags. -/
noncomputable def controlsProgram : PolyProgram id id controls := by
  let P := (BooleanLists.packProgram.comp controls_poly.program).comp BooleanLists.unpackProgram
  exact P.congr _ (fun _ => rfl)

end InfoLossLAR.WorstCase.CoherentRejection

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms.Complexity NativeWordLayout

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2Boolean TM2Boolean.PolyProgramCircuit Integration9_9.TM2OutputLength

abbrev P : PolyProgram id id CoherentRejection.controls := CoherentRejection.controlsProgram

private theorem capacity_gt (m : ℕ) : m < capacity P m := by
  have h := actualOutput_length_lt_capacity P (List.replicate m false)
  simpa only [CoherentRejection.controls_length,List.length_replicate] using h

def controlIndex {m : ℕ} (i : Fin m) : Fin (capacity P m) := ⟨i.val,i.isLt.trans (capacity_gt m)⟩

def controlWire {m : ℕ} (i : Fin m) : Fin (width P m) :=
  outputWire P m (controlIndex i) (some true)

def initialWork (m : ℕ) (word : Str) : Bits (width P m) := fun i => wordExtension word i.val

def baseCircuit (m : ℕ) : Layered (width P m) := circuit P m

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end

section

namespace InfoLossLAR.WorstCase.CoherentControlledSwap

open QAlgorithms.Complexity

variable {b n : ℕ}

/-- Disjoint paired data wires and a control outside all pairs. -/
def pairGates (w : (Fin b×Bool) ↪ Fin n) (c : Fin n)
    (hc : ∀ p,c≠w p) (slot : Fin b) : List (Instr n) :=
  gates c (w (slot,false)) (w (slot,true)) (hc _) (hc _)
    (w.injective.ne (by simp))

def blockGates (w : (Fin b×Bool) ↪ Fin n) (c : Fin n)
    (hc : ∀ p,c≠w p) (slots : List (Fin b)) : List (Instr n) :=
  slots.flatMap (pairGates w c hc)

open ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

end InfoLossLAR.WorstCase.CoherentControlledSwap

end

section

namespace InfoLossLAR.WorstCase.CoherentControlledSwap

open QAlgorithms.Complexity

variable {b m n : ℕ}

def selectionGates (w : Fin m → (Fin b×Bool) ↪ Fin n) (c : Fin m → Fin n)
    (hc : ∀ i j p,c i≠w j p) (slots : List (Fin m)) : List (Instr n) :=
  slots.flatMap (fun i => blockGates (w i) (c i) (hc i i) (List.finRange b))

open ControlledNativeCode

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

end InfoLossLAR.WorstCase.CoherentControlledSwap

end

section

namespace InfoLossLAR.WorstCase.CoherentControlledSwap

open QAlgorithms.Complexity

variable {b m W : ℕ}

/-- Row zero is the designated output; row j+1 is candidate j. -/
def rowWire (r : Fin (m+1)) (i : Fin b) : Fin ((m+1)*b) := finProdFinEquiv (r,i)

def candidatePairs (chosen : Fin m) : (Fin b×Bool) ↪ Fin ((m+1)*b) where
  toFun p := rowWire (if p.2 then chosen.succ else 0) p.1
  inj' p q h := by
    have hh := finProdFinEquiv.injective h
    obtain ⟨p,s⟩ := p
    obtain ⟨q,t⟩ := q
    cases s <;> cases t <;> simp only [if_true,Prod.mk.injEq] at hh ⊢
    · exact ⟨hh.2,trivial⟩
    · have he := congrArg Fin.val hh.1
      simp at he
    · have he := congrArg Fin.val hh.1
      simp at he
    · exact ⟨hh.2,trivial⟩

def appendPairs (w : (Fin b×Bool) ↪ Fin ((m+1)*b)) :
    (Fin b×Bool) ↪ Fin (W+(m+1)*b) where
  toFun p := Fin.natAdd W (w p)
  inj' _p _q h := w.injective (Fin.ext (Nat.add_left_cancel (congrArg Fin.val h)))

def candidateFullPairs (chosen : Fin m) : (Fin b×Bool) ↪ Fin (W+(m+1)*b) :=
  appendPairs (candidatePairs chosen)

private theorem work_outside (work : Fin W) (chosen : Fin m) :
    work.castAdd ((m+1)*b)∉Set.range (candidateFullPairs (W:=W) (b:=b) chosen) := by
  rintro ⟨p,h⟩
  have he := congrArg Fin.val h
  change W+(candidatePairs chosen p).val=work.val at he
  omega

private theorem controls_fresh (controls : Fin m → Fin W) :
    ∀ i j p,(controls i).castAdd ((m+1)*b)≠candidateFullPairs (W:=W) (b:=b) j p := by
  intro i j p h
  exact work_outside (controls i) j ⟨p,h.symm⟩

end InfoLossLAR.WorstCase.CoherentControlledSwap

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms.Complexity NativeWordCoherent CoherentControlledSwap NativeWordLayout

open scoped BigOperators

/-- Each overlapping primitive is emitted as its own valid singleton layer. -/
def middle (b m : ℕ) : List (Instr (width P m+(m+1)*b)) :=
  selectionGates (candidateFullPairs (W:=width P m) (b:=b))
    (fun i => (controlWire i).castAdd ((m+1)*b)) (controls_fresh controlWire) (List.finRange m)

def wholeCircuit (b m : ℕ) : Layered (width P m+(m+1)*b) :=
  extendCircuit ((m+1)*b) (baseCircuit m)++(middle b m).map (fun g => [g])++
    extendCircuit ((m+1)*b) (inverseCircuit (baseCircuit m))

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end

section

namespace InfoLossLAR.WorstCase.CoherentControlledSwap

open QAlgorithms.Complexity

variable {b m : ℕ}

def dataRow (data : Bits ((m+1)*b)) (r : Fin (m+1)) : Bits b := fun j => data (rowWire r j)

def assembleRows (out : Bits b) (copies : Fin m → Bits b) : Bits ((m+1)*b) :=
  fun k => Fin.cases out copies (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

@[simp] private theorem assembleRows_zero (out : Bits b) (copies : Fin m → Bits b) :
    dataRow (assembleRows out copies) 0=out := by
  funext j
  simp [dataRow,assembleRows,rowWire]

@[simp] private theorem assembleRows_succ (out : Bits b) (copies : Fin m → Bits b) (i : Fin m) :
    dataRow (assembleRows out copies) i.succ=copies i := by
  funext j
  simp [dataRow,assembleRows,rowWire]

private theorem assembleRows_split (data : Bits ((m+1)*b)) :
    assembleRows (dataRow data 0) (fun i => dataRow data i.succ)=data := by
  funext k
  obtain ⟨⟨r,j⟩,rfl⟩ := finProdFinEquiv.surjective k
  refine Fin.cases ?_ (fun i => ?_) r
  · exact congrFun (assembleRows_zero (dataRow data 0) (fun i => dataRow data i.succ)) j
  · exact congrFun (assembleRows_succ (dataRow data 0) (fun i => dataRow data i.succ) i) j

end InfoLossLAR.WorstCase.CoherentControlledSwap

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute CoherentControlledSwap

open NativeWordLayout

open scoped BigOperators

abbrev Coordinates (b m k : ℕ) := Bits ((m+1)*b)×(Bits m×Bits k)

def encoded (b m k : ℕ) (x : Coordinates b m k) : Bits (width P m+(m+1)*b+k) :=
  Fin.append (Fin.append (initialWork m (List.ofFn x.2.1)) x.1) x.2.2

private theorem initial_flags {m : ℕ} (flags : Bits m) (i : Fin m) :
    initialWork m (List.ofFn flags) ⟨i.val,by unfold width;omega⟩=flags i := by
  have hi : i.val < (List.ofFn flags).length := by simp
  simp only [initialWork,TM2Boolean.wordExtension_before _ _ hi,List.getElem_ofFn]

private theorem encoded_injective (b m k : ℕ) : Function.Injective (encoded b m k) := by
  intro x y h
  have hd : x.1=y.1 := by
    funext i
    have hh:=congrFun h ((Fin.natAdd (width P m) i).castAdd k)
    simpa only [encoded,Fin.append_left,Fin.append_right] using hh
  have hj : x.2.2=y.2.2 := by
    funext i
    have hh:=congrFun h (Fin.natAdd (width P m+(m+1)*b) i)
    simpa only [encoded,Fin.append_right] using hh
  have hf : x.2.1=y.2.1 := by
    funext i
    let j : Fin (width P m) := ⟨i.val,by unfold width;omega⟩
    have hh:=congrFun h ((j.castAdd ((m+1)*b)).castAdd k)
    simp only [encoded,Fin.append_left] at hh
    change initialWork m (List.ofFn x.2.1) ⟨i.val,_⟩=initialWork m (List.ofFn y.2.1) ⟨i.val,_⟩ at hh
    simpa only [initial_flags] using hh
  exact Prod.ext hd (Prod.ext hf hj)

def physicalEmbedding (b m k : ℕ) : Coordinates b m k ↪ Bits (width P m+(m+1)*b+k) :=
  ⟨encoded b m k,encoded_injective b m k⟩

def fullCircuit (b m k : ℕ) : Layered (width P m+(m+1)*b+k) :=
  leftCircuit (wholeCircuit b m)

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms.Complexity CoherentComputeUncompute CoherentControlledSwap CoherentRejection CoherentProjection

open NativeWordLayout

open scoped BigOperators

abbrev AbstractCoordinates (b m k : ℕ) := Bits b×Retained (Bits b) (Bits k) m

def junkRows {m k : ℕ} (bits : Bits (m*k)) : Fin m → Bits k :=
  fun i j => bits (finProdFinEquiv (i,j))

def packJunk {m k : ℕ} (rows : Fin m → Bits k) : Bits (m*k) :=
  fun i => rows (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

@[simp] private theorem junkRows_pack {m k : ℕ} (rows : Fin m → Bits k) : junkRows (packJunk rows)=rows := by
  funext i j
  simp [junkRows,packJunk]

@[simp] private theorem packJunk_rows {m k : ℕ} (bits : Bits (m*k)) : packJunk (junkRows bits)=bits := by
  funext i
  change bits (finProdFinEquiv (finProdFinEquiv.symm i))=bits i
  rw [Equiv.apply_symm_apply]

/-- A mere regrouping keeps every flag, every unused output and every local
auxiliary bit. The designated output is the entire first physical data row. -/
def abstractCoordinates (b m k : ℕ) : Coordinates b m (m*k) ≃ AbstractCoordinates b m k where
  toFun x := (dataRow x.1 0,(x.2.1,fun i => (dataRow x.1 i.succ,junkRows x.2.2 i)))
  invFun x := (assembleRows x.1 (fun i => (x.2.2 i).1),(x.2.1,packJunk (fun i => (x.2.2 i).2)))
  left_inv x := by simp only [assembleRows_split,packJunk_rows,Prod.eta]
  right_inv x := by simp only [assembleRows_zero,assembleRows_succ,junkRows_pack,Prod.eta]

def abstractEmbedding (b m k : ℕ) : AbstractCoordinates b m k ↪ Bits (width P m+(m+1)*b+m*k) :=
  (abstractCoordinates b m k).symm.toEmbedding.trans (physicalEmbedding b m (m*k))

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end

section

namespace InfoLossLAR.WorstCase.CoherentParallelTrials

open QAlgorithms QAlgorithms.Complexity

open scoped BigOperators

def width (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | m+1 => n+width n m

@[simp] private theorem width_eq (n m : ℕ) : width n m=m*n := by
  induction m with
  | zero => simp [width]
  | succ m ih => simp only [width,ih,Nat.succ_mul];omega

def circuit {n : ℕ} (trial : Layered n) : (m : ℕ) → Layered (width n m)
  | 0 => []
  | m+1 => leftCircuit trial++rightCircuit (circuit trial m)

end InfoLossLAR.WorstCase.CoherentParallelTrials

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms QAlgorithms.Complexity CoherentControlledSwap NativeWordLayout

abbrev TrialPositions (b m k : ℕ) := (Fin m×Fin b)⊕(Fin m⊕(Fin m×Fin k))

/-- Separate a trial's output, flag and complete local auxiliary positions. -/
def trialPositions (b m k : ℕ) : (Fin m×Fin (b+1+k)) ≃ TrialPositions b m k where
  toFun x := Fin.addCases
    (Fin.addCases (fun j => Sum.inl (x.1,j)) (fun _ => Sum.inr (Sum.inl x.1)))
    (fun j => Sum.inr (Sum.inr (x.1,j))) x.2
  invFun x := match x with
    | .inl (i,j) => (i,(j.castAdd 1).castAdd k)
    | .inr (.inl i) => (i,(Fin.natAdd b (0 : Fin 1)).castAdd k)
    | .inr (.inr (i,j)) => (i,Fin.natAdd (b+1) j)
  left_inv x := by
    rcases x with ⟨i,j⟩
    refine Fin.addCases ?_ ?_ j
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro l;simp
      · intro l
        have he : l=(0 : Fin 1) := Subsingleton.elim _ _
        subst l;simp
    · intro l;simp
  right_inv x := by
    rcases x with ⟨i,j⟩ | (i | ⟨i,j⟩) <;> simp

abbrev WholePositions (b m k : ℕ) := Fin (width P m)⊕(Fin ((m+1)*b)⊕Fin (m*k))

def flagPosition {m : ℕ} (i : Fin m) : Fin (width P m) := ⟨i.val,by unfold width;omega⟩

def trialLocation (b m k : ℕ) : TrialPositions b m k → WholePositions b m k
  | .inl (i,j) => .inr (.inl (rowWire i.succ j))
  | .inr (.inl i) => .inl (flagPosition i)
  | .inr (.inr (i,j)) => .inr (.inr (finProdFinEquiv (i,j)))

private theorem trialLocation_injective (b m k : ℕ) : Function.Injective (trialLocation b m k) := by
  intro x y h
  rcases x with ⟨i,j⟩ | (i | ⟨i,j⟩) <;>
    rcases y with ⟨i',j'⟩ | (i' | ⟨i',j'⟩)
  all_goals simp only [trialLocation,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl] at h
  all_goals try contradiction
  · have hh := finProdFinEquiv.injective h
    have hi := Fin.succ_injective _ (congrArg Prod.fst hh)
    have hj : j=j' := congrArg Prod.snd hh
    subst i';subst j';rfl
  · have hv := congrArg Fin.val h
    have hi : i=i' := Fin.ext hv
    subst i';rfl
  · have hh := finProdFinEquiv.injective h
    exact congrArg (fun p : Fin m×Fin k => Sum.inr (Sum.inr p)) hh

def wholePositionEquiv (b m k : ℕ) : WholePositions b m k ≃ Fin (width P m+(m+1)*b+m*k) :=
  (Equiv.sumAssoc _ _ _).symm.trans
    ((Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv)

/-- One public injection places every trial output in its candidate row,
every flag in the actual machine input, and every auxiliary in the spectator
region. No two trial positions share a physical wire. -/
def trialPlacement (b m k : ℕ) : (Fin m×Fin (b+1+k)) ↪ Fin (width P m+(m+1)*b+m*k) :=
  (trialPositions b m k).toEmbedding.trans
    ((⟨trialLocation b m k,trialLocation_injective b m k⟩ : TrialPositions b m k ↪ WholePositions b m k).trans
      (wholePositionEquiv b m k).toEmbedding)

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms QAlgorithms.Complexity CoherentControlledSwap NativeWordLayout

/-- The physical trial order is output, one flag, and all local auxiliaries. -/
def splitTrial (b k : ℕ) : Bits (b+1+k) ≃ Bool×(Bits b×Bits k) where
  toFun x := (x ((Fin.natAdd b (0 : Fin 1)).castAdd k),
    (fun j => x ((j.castAdd 1).castAdd k),fun j => x (Fin.natAdd (b+1) j)))
  invFun x := Fin.append (Fin.append x.2.1 (fun _ => x.1)) x.2.2
  left_inv x := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro l;simp
      · intro l
        have he : l=(0 : Fin 1) := Subsingleton.elim _ _
        subst l;simp
    · intro l;simp
  right_inv x := by simp

def copyEncoding (b m k : ℕ) (copies : Fin m → Bits (b+1+k)) :
    Bits (width P m+(m+1)*b+m*k) :=
  encoded b m (m*k) (assembleRows (fun _ => false) (fun i => (splitTrial b k (copies i)).2.1),
    (fun i => (splitTrial b k (copies i)).1,packJunk (fun i => (splitTrial b k (copies i)).2.2)))

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end

section

namespace InfoLossLAR.WorstCase.CoherentParallelTrials

open QAlgorithms.Complexity

/-- Canonical physical wire order of the recursively concatenated trial
registers, with the same order as the actual repeated circuit. -/
def flatWire (n m : ℕ) : (Fin m×Fin n) ≃ Fin (width n m) :=
  finProdFinEquiv.trans (finCongr (width_eq n m).symm)

end InfoLossLAR.WorstCase.CoherentParallelTrials

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms.Complexity CoherentComputeUncompute FiniteGateTransport CoherentProjection

open NativeWordLayout

open scoped BigOperators

def allTrialWires (b m k : ℕ) :
    Fin (CoherentParallelTrials.width (b+1+k) m) ↪ Fin (width P m+(m+1)*b+m*k) :=
  (CoherentParallelTrials.flatWire (b+1+k) m).symm.toEmbedding.trans (trialPlacement b m k)

def parallelPreparation (b m k : ℕ) (trial : Layered (b+1+k)) :
    Layered (width P m+(m+1)*b+m*k) :=
  relocateCircuit (allTrialWires b m k) (CoherentParallelTrials.circuit trial m)

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentFirstSuccessNative

open QAlgorithms.Complexity CoherentComputeUncompute CoherentProjection CoherentRejection

open NativeWordLayout

open scoped BigOperators

/-- Literal parallel finite-gate preparation followed by the complete
first-success compute, row selection and inverse computation. -/
def pipelineCircuit (b m k : ℕ) (trial : Layered (b+1+k)) :
    Layered (width P m+(m+1)*b+m*k) :=
  parallelPreparation b m k trial++fullCircuit b m (m*k)

end InfoLossLAR.WorstCase.CoherentFirstSuccessNative

end

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.CoherentEmbeddedWeightedTrial

open CoherentComputeUncompute CoherentWeightedPreparation CoherentRejection

open scoped BigOperators

variable {I W J : Type*} [Fintype I] [Fintype W] [Fintype J]
  [Nonempty I] [DecidableEq W] [DecidableEq J]

def target (e : I↪W) (w : I→ℝ) : W→ℂ := basisEmbedding e (CoherentWeightedPreparation.target w)

end InfoLossLAR.WorstCase.CoherentEmbeddedWeightedTrial

end

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder.Pipeline

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeWordCoherent NativeWordLayout

open CoherentWeightedPreparation CoherentComputeUncompute ControlledNativeGates CoherentRejection

open CoherentFirstSuccessNative

open scoped BigOperators

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

variable (request : Str→PointRequest×List Unit) (hr : Poly request)

def fixedTicketWires (words : Str→List ℕ) (hw : Poly words) (p : Polynomial ℕ) (H K : ℕ) :
    Fin K↪Fin (width (NativeWordCoherent.P words hw p) (H+K)+1+4) where
  toFun i := ⟨H+i.val,by unfold width;omega⟩
  inj' := by intro i j h;apply Fin.ext;exact Nat.add_left_cancel (congrArg Fin.val h)

def fixedProposalCircuit (words : Str→List ℕ) (hw : Poly words) (p : Polynomial ℕ) (H K : ℕ) :=
  relocateCircuit (fixedTicketWires words hw p H K) (coinCircuit K)

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.Builder.Pipeline

end

end

section

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.RegisteredTrial

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport NativeWordCoherent NativeWordLayout

open CoherentWeightedPreparation CoherentComputeUncompute ControlledNativeGates CoherentRejection

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Builder

noncomputable section

variable (request : Str→PointRequest×List Unit) (hp : ∀ a : ℕ, Poly (Builder.gateWord request a))

noncomputable def programBound (a : ℕ) : Polynomial ℕ :=
  (hp a).program.sizeBound.comp (3*Polynomial.X)

def acceptanceGates (synthesis interpreter : ℕ) (slots : List Unit) (K : ℕ)
    (interpreterBudget : List Unit) :=
  wholeCircuit (Builder.gateWord request synthesis) (hp synthesis)
    (programBound request hp synthesis) (2*slots.length+1+K) interpreter interpreterBudget

abbrev ticketWidth (a : ℕ) (slots : List Unit) (K : ℕ) : ℕ :=
  width (P (Builder.gateWord request a) (hp a) (programBound request hp a)) (2*slots.length+1+K)

def ticketRow (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (tape : Bits K) :
    Bits (ticketWidth request hp a slots K) :=
  NativeWordCoherent.initialWork (Builder.gateWord request a) (hp a)
    (programBound request hp a) (2*slots.length+1+K) (Builder.encoded slots word tape)

def ticketEmbedding (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) :
    Bits K↪Bits (ticketWidth request hp a slots K) where
  toFun := ticketRow request hp a slots word K
  inj' := by
    intro i j h
    apply Builder.encoded_injective slots word K
    exact initialWork_injective (Builder.gateWord request a) (hp a) (programBound request hp a)
      _ _ _ (Builder.encoded_length slots word i) (Builder.encoded_length slots word j) h

def sourceError (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (budget : List Unit) : ℝ :=
  180*(((programBound request hp a).eval (2*slots.length+1+K) : ℕ) : ℝ)/((budget.length : ℝ)+1)+
    (5/(((request word).2.length : ℝ)+1)+2*Real.sqrt (1/(2 : ℝ)^((request word).1.2.2.length)))

def targetAmplitude (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (s : ℝ)
    (hK : Nat.size (intervalCount (request word).1) ≤ K) :
    EuclideanSpace ℂ (Bits (ticketWidth request hp a slots K)) :=
  WithLp.toLp 2 (CoherentEmbeddedWeightedTrial.target (ticketEmbedding request hp a slots word K)
    (capacityWeight (request word).1 s K hK))

def headGates (a : ℕ) (slots : List Unit) (_word : Str) (K : ℕ) :
    Layered (ticketWidth request hp a slots K+1+4) :=
  Builder.Pipeline.fixedProposalCircuit (Builder.gateWord request a) (hp a) (programBound request hp a)
    (2*slots.length+1) K

def zeroWord (a : ℕ) (slots : List Unit) (word : Str) (K : ℕ) :
    Bits (ticketWidth request hp a slots K+1+4) :=
  fun i => TM2Boolean.wordExtension (Builder.encoded slots word (fun _ : Fin K => false)) i.val

def singleTrial (a b : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (budget : List Unit) :=
  headGates request hp a slots word K++acceptanceGates request hp a b slots K budget

def prepare (a b : ℕ) (slots : List Unit) (word : Str) (K : ℕ) (budget : List Unit) (m : ℕ) :=
  CoherentFirstSuccessNative.pipelineCircuit (ticketWidth request hp a slots K) m 4 (singleTrial request hp a b slots word K budget)

def input (a : ℕ) (slots : List Unit) (word : Str) (K m : ℕ) :=
  CoherentFirstSuccessNative.copyEncoding (ticketWidth request hp a slots K) m 4 (fun _ => zeroWord request hp a slots word K)

def contract : Prop :=
    ∃ synthesis interpreter : ℕ,0 < synthesis ∧ 0 < interpreter ∧
      ∀ (slots : List Unit) (word : Str) (s : ℝ) (budget : List Unit),
        2*word.length+1 ≤ slots.length →
        ∀ (K : ℕ) (hK : Nat.size (intervalCount (request word).1) ≤ K),
        1 ≤ s → s^2=(variance (request word).1 : ℝ) → 2 ≤ (request word).1.2.1.length →
        ∀ m : ℕ,m≠0 →
        ∃ clean : EuclideanSpace ℂ (Retained (Bits (ticketWidth request hp synthesis slots K)) (Bits 4) m),
          ‖clean‖=1 ∧
          ‖(WithLp.toLp 2 (runLayered (prepare request hp synthesis interpreter slots word K budget m)
              (basis (input request hp synthesis slots word K m))-
            basisEmbedding (CoherentFirstSuccessNative.abstractEmbedding (ticketWidth request hp synthesis slots K) m 4)
              (CoherentProjection.tensorState (targetAmplitude request hp synthesis slots word K s hK) clean)) : EuclideanSpace ℂ _)‖ ≤
            (m : ℝ)*sourceError request hp synthesis slots word K budget+
              2*Real.exp (-(m : ℝ)/(112*((request word).1.2.1.length : ℝ)))

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide.Coherent.Padding.RegisteredTrial

end


