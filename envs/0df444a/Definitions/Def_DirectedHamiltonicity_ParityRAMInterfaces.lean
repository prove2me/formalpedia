-- Prove2me | Definitions.Def_DirectedHamiltonicity_ParityRAMInterfaces
-- name    : DirectedHamiltonicity_ParityRAMInterfaces
-- status  : Definition
-- author  : @Soh Kumabe
-- created : 2026-11-26T17:18:52.150218+00:00
-- url     : https://prove2.me/theorems/f7595483-f5f5-51b0-a5c9-8881e737d831
-- title:
--   Input layout and trial execution for Hamiltonian path parity
-- statement:
--   The input tape encodes a weighted directed multigraph, its two distinguished endpoints and a signed target. The parser's postcondition identifies each retained arc field, the maximum weight and the admissible target range. The normalized graph view, numeric request and trial state then specify the data exchanged by the graph and affine-counting subroutines.
--
--   For a valid target, the execution contract requires that the program produce the finite-coin estimator with a bounded word width and a number of steps linear in the trial budget up to a polynomial. A separate whole-input contract states this requirement in the published RAM semantics on every finite tape.
-- source:
--   Auxiliary result for the log-cost RAM formalization of Proposition 4 in T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, STOC 2027 submission 811, PDF pp. 5 and 8–11. https://prove2.me/theorems/aa04b14a-8225-48c8-904c-8725ebdcac66

import Definitions.Def_DirectedHamiltonicity_Main_Algorithms
import Definitions.Def_DirectedHamiltonicity_ParitySampler

set_option autoImplicit false

section HamiltonianInputFields

namespace DirectedHamiltonicity.Main

open TargetedSamplers.Structured.BinaryRead

/-- The words following n and m, in exactly the order present on the external tape. -/
def arcFields {n m : ℕ} (tail head : Fin m → Fin n) (weight : Fin m → ℕ) (s t : Fin n) : List ℕ :=
  (List.finRange m).flatMap (fun e => [(tail e).val,(head e).val,weight e]) ++ [s.val,t.val]

end DirectedHamiltonicity.Main

end HamiltonianInputFields

section HamiltonianInputBound

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.BinaryRead

/-- The graph table starts at a fixed address beyond the routine's scalar registers. -/
def graphBase : ℕ := 128

def headerRegs : Fin 11 ↪ ℕ := Fin.valEmbedding

 def maxRegs : Fin 8 ↪ ℕ where
  toFun i := 11+i.val
  inj' _ _ h := Fin.ext (Nat.add_left_cancel h)

 def factorRegs : Fin 5 ↪ ℕ where
  toFun i := [19,17,20,18,13][i.val]'(by simpa using i.isLt)
  inj' := by decide

 def setupMax : Fragment := Structured.sequence [
  .op (.const 18 0), .op (.const 13 1), .op (.const 11 0), .op (.add 12 8 18),
  .op (.const 14 (graphBase+2)), .op (.const 15 3), .op (.const 17 0)]

 def setupFactor : Fragment := Structured.sequence [.op (.sub 19 7 13), .op (.const 20 0)]

/-- Compute the maximum weight and the target cutoff from the stored graph dimensions
and the weight field of each record. The graph and the external input cursor are preserved. -/
def computeBound : Cmd :=
  .seq setupMax.cmd (.seq (stridedMax maxRegs) (.seq setupFactor.cmd (Word.addRepeatedly factorRegs)))

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianInputBound

section HamiltonianRAMInput

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.BinaryRead

/-- The entire external parser, including discovery of the weight cutoff from the graph. -/
def readInstance : Cmd := .seq (.op (.const 10 graphBase)) (.seq (graphHeader headerRegs)
  (.seq computeBound (readSigned (digitRegs headerRegs) 20 9)))

/-- The retained register and table values on return from the actual input routine. -/
structure Parsed {n m : ℕ} (tail head : Fin m → Fin n) (weight : Fin m → ℕ)
    (s t : Fin n) (B : ℤ) (u : Store) : Prop where
  vertices : u.mem 7 = n
  edges : u.mem 8 = m
  maxWeight : u.mem 17 = Finset.univ.sup weight
  cutoff : u.mem 20 = (n-1)*Finset.univ.sup weight
  valid : u.mem 9 = 0 ↔ 0 ≤ B ∧ B ≤ (((n-1)*Finset.univ.sup weight : ℕ) : ℤ)
  target : 0 ≤ B → B ≤ (((n-1)*Finset.univ.sup weight : ℕ) : ℤ) → u.mem 1 = B.toNat
  tableEnd : u.mem 10 = graphBase+(3*m+2)
  table : ∀ i (hi : i < (arcFields tail head weight s t).length),
    u.mem (graphBase+i) = (arcFields tail head weight s t)[i]
  free : ∀ a, 21 ≤ a → (a < graphBase ∨ graphBase+(3*m+2) ≤ a) → u.mem a = 0
  output : u.out = []

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMInput

section HamiltonianRAMArcs

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.TripleScan

open Multidigraph

def edgeRecords {n m : ℕ} (tail head : Fin m → Fin n) (w : Fin m → ℕ) : List Record :=
  (List.finRange m).map (fun e => ((tail e).val,(head e).val,w e))

 def forbidden (r : Fin 10 ↪ ℕ) (src dst : ℕ) := [(r 3,r 4),(r 4,src),(r 3,dst)]

/-- Query the normalized graph directly in the original table, using constant scratch space. -/
def retainedQuery (r : Fin 10 ↪ ℕ) (src dst : ℕ) : Cmd :=
  .seq (.op (.const (r 6) 0)) (.seq (loop r) (clearEqual (r 6) (forbidden r src dst)))

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMArcs

section HamiltonianRAMNeighborhood

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.TripleScan

open Multidigraph Classical

def arcRegs : Fin 10 ↪ ℕ := ⟨fun i => 40+i.val,fun _ _ h => Fin.ext (Nat.add_left_cancel h)⟩

def tailRegs : Fin 6 ↪ ℕ := ⟨![43,33,42,50,46,32],by decide⟩

def weightRegs : Fin 6 ↪ ℕ := ⟨![45,34,42,51,50,32],by decide⟩

def vertexRegs : Fin 6 ↪ ℕ := ⟨![44,33,42,52,51,32],by decide⟩

structure GraphView {n m W : ℕ} (tail head : Fin m → Fin n) (w : Fin m → ℕ)
    (s t : Fin n) (base : ℕ) (v : Store) : Prop where
  low : 60 ≤ base
  records : RecordsAt v base (edgeRecords tail head w)
  source : v.mem 30 = s.val
  sink : v.mem 31 = t.val
  zero : v.mem 32 = 0
  vertices : v.mem 33 = n
  weights : v.mem 34 = W+1
  table : v.mem 35 = base
  stop : v.mem 41 = base+3*m
  unit : v.mem 42 = 1

def inspectArc : Cmd := .seq (.op (.add 40 35 32)) (retainedQuery arcRegs 30 31)

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMNeighborhood

section HamiltonianRAMView

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured

/-- Prepare a reusable view of the parsed edge records and save the target for subsequent trials. -/
def prepareView : Fragment := Structured.sequence [
  .op (.const 32 0),.op (.const 42 1),.op (.add 33 7 32),.op (.add 34 17 42),.op (.const 35 graphBase),
  .op (.sub 36 10 42),.op (.sub 41 36 42),.op (.load 30 41),.op (.load 31 36),.op (.add 53 1 32)]

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMView

section HamiltonianRAMDegree

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured

open Multidigraph Classical

def incomingTest : Cmd := Reduction.maximum.reduce tailRegs 0 inspectArc

def countIncoming : Cmd := Reduction.sum.reduce weightRegs 0 incomingTest

def findSamplingDegree : Cmd := Reduction.maximum.reduce vertexRegs 1 countIncoming

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMDegree

section HamiltonianRAMGuard

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured

/-- The estimator body is entered only for a target in the range attained by a path. -/
def onValid (body : Cmd) : Cmd :=
  .seq readInstance (.branch 9 21 body (.op (.output 21)))

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMGuard

section HamiltonianRAMPreprocess

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open Multidigraph Classical

 def scheduleArgs := Structured.sequence [
  .op (.add (cell 0) 33 32),.op (.add (cell 1) 52 32)]

/-- The two scheduling inputs are copied from the graph view; no parameter is read from an
advice tape. The trial count is saved above the arithmetic subroutine's registers. -/
def scheduleFromView : Cmd := .seq scheduleArgs.cmd (.seq (Circuit.cmd trialSchedule) (.op (.add 54 (cell 13) 32)))

def preprocess : Cmd := .seq prepareView.cmd (.seq findSamplingDegree scheduleFromView)

def preprocessWork (n m W d : ℕ) := n*((W+1)*(n*(18*m+20)+8)+8)+scheduleSteps n d+16

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMPreprocess

section HamiltonianRAMGrid

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

/-- Decode a row-major position in n by n by width storage. The logical registers
for the three coordinates coincide with the parsed-graph query registers. -/
def gridCoordinates : List Assignment := [
  ⟨13,.sub 41 44⟩,⟨29,.arithmetic .div 13 43⟩,⟨14,.arithmetic .div 13 20⟩,
  ⟨30,.arithmetic .mod 14 19⟩,⟨31,.arithmetic .mod 13 20⟩]

theorem gridCoordinates_bounds {n w i : ℕ} (h : i < n*(n*w)) (hn : 0 < n) (hw : 0 < w) :
    i/(n*w) < n ∧ (i/w)%n < n ∧ i%w < w :=
  ⟨(Nat.div_lt_iff_lt_mul (Nat.mul_pos hn hw)).mpr h,Nat.mod_lt _ hn,Nat.mod_lt _ hw⟩

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMGrid

section HamiltonianRAMDenseEntry

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open TargetedSamplers.Structured.TripleScan Multidigraph Classical

def normalizedEntry : Cmd := .seq (Circuit.cmd gridCoordinates) inspectArc

def linearArc {n W : ℕ} (hn : 0 < n) (i : ℕ) (hi : i < n*(n*(W+1))) : ArcType (Fin n) W :=
  let h := gridCoordinates_bounds hi hn (Nat.succ_pos W)
  (⟨i/(n*(W+1)),h.1⟩,⟨(i/(W+1))%n,h.2.1⟩,⟨i%(W+1),h.2.2⟩)

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMDenseEntry

section HamiltonianRAMDenseTable

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured Multidigraph

/-- Tabulate normalized parity-of-multiplicity flags in tail/head/weight order. -/
def normalizedTable : Cmd := tabulate 55 56 42 46 normalizedEntry

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMDenseTable

section HamiltonianRAMBuildGrid

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

/-- Keep a fixed caller-selected reserve between the graph records and the dense table. -/
def gridSetup (reserve : ℕ) : List Assignment := [
  ⟨45,.literal (reserve+2)⟩,⟨44,.add 27 45⟩,⟨41,.add 44 18⟩,
  ⟨43,.arithmetic .mul 19 20⟩,⟨42,.arithmetic .mul 19 43⟩,⟨42,.add 42 44⟩]

def buildNormalizedGrid (reserve : ℕ) : Cmd := .seq (Circuit.cmd (gridSetup reserve)) normalizedTable

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMBuildGrid

section HamiltonianAdjacencyBits

namespace DirectedHamiltonicity.Main.NativeGraph

open Multidigraph InputRAM Classical TargetedSamplers.Structured.BinaryStack

variable {n m W : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ) (hw : ∀ e, w e ≤ W) (s t : Fin n)

/-- Exactly the flag table written by the normalized graph scan, in physical address order. -/
noncomputable def adjacencyBits : List Bool := List.ofFn fun i : Fin (n*(n*(W+1))) =>
  decide (H.retainArc w s t hw (linearArc (Nat.zero_lt_of_lt s.isLt) i.val i.isLt))

end DirectedHamiltonicity.Main.NativeGraph

end HamiltonianAdjacencyBits

section HamiltonianRAMGraphArgument

namespace DirectedHamiltonicity.Main.InputRAM

open Multidigraph NativeGraph TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open TargetedSamplers.Structured.BinaryStack

 def copyBounds : Fragment := Structured.sequence [
  .op (.add (cell 9) 55 32),.op (.add (cell 10) 58 32)]

def packNormalizedGrid (reserve : ℕ) : Cmd :=
  .seq (buildNormalizedGrid reserve) (.seq copyBounds.cmd packMemory)

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMGraphArgument

section HamiltonianRAMCapture

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured

/-- Copy the live graph words out of the parser area before reusing low memory
for polynomial subroutines. The adjacency word in physical register 22 may have exponentially large value. -/
def captureGraph (base : ℕ) : Fragment := Structured.sequence [
  .op (.add (base+0) 33 32),.op (.add (base+1) 34 32),.op (.add (base+2) 30 32),
  .op (.add (base+3) 31 32),.op (.add (base+4) 22 32),.op (.add (base+10) 54 32),
  .op (.add (base+11) 53 32),.op (.add (base+26) 55 32)]

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMCapture

section HamiltonianRequestWidth

namespace DirectedHamiltonicity.Main.InputRAM

/-- The numeric value of a key can be exponential. All numeric request fields fit
in this graph-derived number of bits, which is polynomial in the public parameters. -/
def argumentWidth (n h : ℕ) := (n+1)*(n*(n*h)+1)+n+h+16

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRequestWidth

section HamiltonianRAMFieldSetup

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

 def initDimensions : List Assignment := [
  ⟨23,.literal 0⟩,⟨24,.literal 1⟩,⟨25,.literal 2⟩,⟨12,.sub 0 25⟩,
  ⟨30,.arithmetic .mul 0 1⟩,⟨30,.arithmetic .mul 0 30⟩,⟨30,.add 30 24⟩,⟨31,.add 0 24⟩,
  ⟨27,.arithmetic .mul 31 30⟩,⟨27,.add 27 0⟩,⟨27,.add 27 1⟩,⟨32,.literal 16⟩,⟨27,.add 27 32⟩]

 def initLimits : List Assignment := [
  ⟨9,.arithmetic .pow 25 27⟩,⟨32,.literal 12⟩,⟨19,.arithmetic .mul 32 10⟩]

 def initCursors : List Assignment := [
  ⟨5,.literal 0⟩,⟨6,.literal 0⟩,⟨7,.literal 0⟩,⟨8,.literal 0⟩,⟨22,.literal 0⟩,
  ⟨65,.literal 0⟩,⟨66,.add 10 23⟩,⟨67,.literal 1⟩,⟨68,.literal 0⟩]

/-- Initialize the field radix, reporting cap and two enumeration cursors. -/
def initFields : List Assignment := initDimensions ++ initLimits ++ initCursors

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMFieldSetup

section HamiltonianRequestRegisters

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers.Structured

/-- The immutable graph and common field radix stay in the caller's register bank. -/
structure RequestHeader (base n h source sink graph width : ℕ) (u : Store) : Prop where
  vertices : u.mem (base+0)=n
  weights : u.mem (base+1)=h
  src : u.mem (base+2)=source
  dst : u.mem (base+3)=sink
  adjacency : u.mem (base+4)=graph
  radix : u.mem (base+9)=2^width

structure RequestArgs (base mask key index kind : ℕ) (u : Store) : Prop where
  maskWord : u.mem (base+5)=mask
  keyWord : u.mem (base+6)=key
  indexWord : u.mem (base+7)=index
  kindWord : u.mem (base+8)=kind

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRequestRegisters

section HamiltonianRAMPrepareQuery

namespace DirectedHamiltonicity.Main.InputRAM

open Multidigraph NativeGraph TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open TargetedSamplers.Structured.BinaryStack

def prepareRequest (bank : ℕ) : Cmd :=
  .seq (packNormalizedGrid 0) (.seq (captureGraph (cell bank)).cmd (Circuit.bankCmd bank initFields))

/-- Values needed by the solver setup and by the first shared-mask query. -/
structure PreparedRequest (a n h s t graph trials target gridEnd : ℕ) (u : Store) : Prop where
  header : RequestHeader a n h s t graph (argumentWidth n h) u
  args : RequestArgs a 0 0 0 0 u
  count : u.mem (a+10)=trials
  degree : u.mem (a+11)=target
  dim : u.mem (a+12)=n-2
  cap : u.mem (a+19)=12*trials
  parity : u.mem (a+22)=0
  zero : u.mem (a+23)=0
  one : u.mem (a+24)=1
  two : u.mem (a+25)=2
  grid : u.mem (a+26)=gridEnd
  width : u.mem (a+27)=argumentWidth n h
  cursor : u.mem (a+65)=0
  limit : u.mem (a+66)=trials
  stride : u.mem (a+67)=1
  total : u.mem (a+68)=0

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMPrepareQuery

section HamiltonianRAMTrialRead

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word FiniteSampling

def window (base k : ℕ) : Fin k ↪ ℕ := ⟨fun i => base+i.val,fun _ _ h => Fin.ext (Nat.add_left_cancel h)⟩

def saveWord (base dst src : ℕ) : Cmd := .op (.add (base+dst) src (base+23))

def trialAddress : List Assignment := [
  ⟨31,.arithmetic .mul 15 65⟩,⟨31,.add 13 31⟩,⟨30,.add 31 15⟩,⟨32,.literal 1⟩]

/-- Seek directly to the requested trial, then read precisely that block. -/
def readTrial (bank : ℕ) : Cmd :=
  let a := cell bank
  .seq (Circuit.bankCmd bank trialAddress) (.seq (readRank (window (a+30) 5)) (saveWord a 6 (a+34)))

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMTrialRead

section HamiltonianRAMSharedRead

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word FiniteSampling

 def offsets (base : ℕ) {k : ℕ} (f : Fin k → ℕ) (inj : Function.Injective f) : Fin k ↪ ℕ :=
  ⟨fun i => base+f i,fun i j h => inj (Nat.add_left_cancel h)⟩

/-- The cardinality and the bit width occupy permanent registers. Only the power and unit are scratch. -/
def logRegisters (a : ℕ) : Fin 4 ↪ ℕ := offsets a (fun i => match i.val with | 0 => 14 | 1 => 31 | 2 => 15 | _ => 33) (by decide)

/-- Read the mask into its permanent argument register, with the zero base and one already installed. -/
def maskRegisters (a : ℕ) : Fin 5 ↪ ℕ :=
  offsets a (fun i => match i.val with | 0 => 30 | 1 => 23 | 2 => 24 | 3 => 33 | _ => 5) (by decide)

def sharedRead (a : ℕ) : Cmd :=
  .seq (ceilLog (logRegisters a)) (.seq (saveWord a 30 (a+13)) (readRank (maskRegisters a)))

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMSharedRead

section HamiltonianRAMSharedPrefix

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word FiniteSampling

def sharedPrefix (bank : ℕ) (kernel : Cmd) : Cmd :=
  let a := cell bank
  .seq kernel (.seq (saveWord a 13 0) (.seq (.op (.const (a+8) 1))
    (.seq kernel (.seq (saveWord a 14 0) (sharedRead a)))))

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMSharedPrefix

section HamiltonianRAMSolverLayout

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers.Structured TargetedSamplers.Structured.Word

/-- Offsets 40 through 58 contain the persistent Gaussian register bank. Rows start
above these registers, followed by one slot per pinned variable and the solver buffer. -/
def rowArea (bank : ℕ) := cell bank+104

def pinArea (bank q : ℕ) := rowArea bank+q*(q+1)

def solverArea (bank q : ℕ) := pinArea bank q+q

def seenArea (bank q c d gridEnd : ℕ) := solverArea bank q+c*(q+(q+q)+1)^d+gridEnd+2

def initSolverLayout (bank c d : ℕ) : List Assignment := [
  ⟨41,.add 12 23⟩,⟨51,.add 12 23⟩,⟨52,.literal (rowArea bank)⟩,
  ⟨30,.add 12 24⟩,⟨30,.arithmetic .mul 12 30⟩,⟨53,.add 52 30⟩,
  ⟨50,.add 53 12⟩,⟨40,.add 50 23⟩,
  ⟨54,.literal 0⟩,⟨55,.literal 1⟩,⟨56,.literal 2⟩,
  ⟨30,.add 12 12⟩,⟨30,.add 12 30⟩,⟨30,.add 30 24⟩,
  ⟨31,.literal d⟩,⟨30,.arithmetic .pow 30 31⟩,⟨31,.literal c⟩,
  ⟨30,.arithmetic .mul 31 30⟩,⟨16,.add 40 30⟩,⟨16,.add 16 26⟩,⟨16,.add 16 25⟩]

def solverRoom (bank q c d gridEnd : ℕ) :=
  4*(seenArea bank q c d gridEnd+(q+(q+q)+1)^d+c+d+3*q+20)

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMSolverLayout

section HamiltonianRAMVisitWord

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.BinaryStack

open scoped BigOperators

def parityWord (value : List Bool → ZMod 2) (seen : Finset (List Bool)) : ℕ :=
  (decide ((∑ x ∈ seen, value x) ≠ 0)).toNat

def markRegisters (a : ℕ) : Fin 5 ↪ ℕ :=
  let f (i : Fin 5) := match i.val with | 0 => 16 | 1 => 58 | 2 => 24 | 3 => 33 | _ => 34
  ⟨fun i => a+f i,fun _ _ h => (by decide : Function.Injective f) (Nat.add_left_cancel h)⟩

def leafArgs (a : ℕ) : Fragment := Structured.sequence [
  .op (.add (a+6) (a+58) (a+23)),.op (.add (a+7) (a+11) (a+23)),.op (.const (a+8) 3)]

def evalFresh (a : ℕ) (kernel : Cmd) : Cmd :=
  .seq (leafArgs a).cmd (.seq kernel (.branch 0 (a+23) .skip (.op (.sub (a+22) (a+24) (a+22)))))

def visitWord (a : ℕ) (kernel : Cmd) : Cmd :=
  .seq (markWord (markRegisters a)).cmd (.branch (a+34) (a+23) (evalFresh a kernel) .skip)

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMVisitWord

section HamiltonianRAMTrialState

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers.Structured TargetedSamplers.Structured.Word TargetedSamplers.Structured.BinaryStack

/-- Permanent inputs for the two passes. The dense row area and the pinned suffix are scratch.
The sparse table starts after both the Gaussian workspace and the last original input cell. -/
structure TrialState (bank n h src dst graph wbits mask maskLen card q M B seenBase : ℕ) (u : Store) : Prop where
  header : RequestHeader (cell bank) n h src dst graph wbits u
  maskAt : u.mem (cell bank+5)=mask
  target : u.mem (cell bank+11)=B
  dim : u.mem (cell bank+12)=q
  masks : u.mem (cell bank+13)=maskLen
  choices : u.mem (cell bank+14)=card
  coinWidth : u.mem (cell bank+15)=Nat.clog 2 card
  seenAt : u.mem (cell bank+16)=seenBase
  cap : u.mem (cell bank+19)=12*M
  zero : u.mem (cell bank+23)=0
  one : u.mem (cell bank+24)=1
  baseAt : u.mem (cell bank+40)=solverArea bank q
  columns : u.mem (cell bank+41)=q
  pinEnd : u.mem (cell bank+50)=pinArea bank q+q
  rows : u.mem (cell bank+51)=q
  first : u.mem (cell bank+52)=rowArea bank
  after : u.mem (cell bank+53)=pinArea bank q
  pause : u.mem (cell bank+54)=0
  unit : u.mem (cell bank+55)=1
  two : u.mem (cell bank+56)=2
  limit : u.mem (cell bank+66)=M
  stride : u.mem (cell bank+67)=1

structure TrialInvariant (bank n h src dst graph wbits mask maskLen card q M B seenBase : ℕ)
    (f : List Bool → ZMod 2) (seen : Finset (List Bool)) (u : Store) : Prop where
  layout : TrialState bank n h src dst graph wbits mask maskLen card q M B seenBase u
  flags : tracksWords q seenBase seen u
  parity : u.mem (cell bank+22)=parityWord f seen

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMTrialState

section HamiltonianRAMRowQueries

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open AffinePrefixEnumeration EditGV897.Main

def rowQueries (bank : ℕ) (kernel : Cmd) : Cmd :=
  let a := cell bank
  indexedQueries (a+34) (a+53) (a+24) 0 (a+52) (a+7) kernel

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMRowQueries

section HamiltonianRAMAffineCall

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open TargetedSamplers.Structured.BinaryStack TargetedSamplers.Structured.RankedPrefix

open AffinePrefixEnumeration EditGV897.Main

def restoreCursor (a : ℕ) : Fragment := Structured.sequence [
  .op (.add (a+46) (a+12) (a+23)),.op (.add (a+49) (a+50) (a+23))]

def startRank (a : ℕ) : Fragment := Structured.sequence [.op (.add (a+57) (a+68) (a+23)),.op (.const (a+58) 1)]

def countPrepared (bank : ℕ) (counter : Cmd) : Cmd :=
  let a := cell bank
  .seq (restoreCursor a).cmd (.seq (countPort (a+40) counter) (saveWord a 69 4))

def rankPrepared (bank : ℕ) (counter : Cmd) : Cmd :=
  let a := cell bank
  .seq (restoreCursor a).cmd (.seq (startRank a).cmd (walkRank (a+40) counter))

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMAffineCall

section HamiltonianRAMTrialProblem

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open TargetedSamplers.Structured.BinaryStack AffinePrefixEnumeration EditGV897.Main FiniteSampling Multidigraph

structure TrialParameters where
  bank : ℕ
  vertices : ℕ
  weights : ℕ
  source : ℕ
  sink : ℕ
  graph : ℕ
  fieldWidth : ℕ
  mask : ℕ
  maskLength : ℕ
  card : ℕ
  dim : ℕ
  trials : ℕ
  target : ℕ
  seenBase : ℕ

namespace TrialParameters

abbrev a (P : TrialParameters) := cell P.bank

abbrev N (P : TrialParameters) := P.dim+(P.dim+P.dim)

abbrev pin (P : TrialParameters) := pinArea P.bank P.dim

abbrev base (P : TrialParameters) := solverArea P.bank P.dim

abbrev header (P : TrialParameters) := RequestHeader P.a P.vertices P.weights P.source P.sink P.graph P.fieldWidth

abbrev invariant (P : TrialParameters) := TrialInvariant P.bank P.vertices P.weights P.source P.sink P.graph P.fieldWidth
  P.mask P.maskLength P.card P.dim P.trials P.target P.seenBase

def key (P : TrialParameters) (τ : Tapes) (i : ℕ) :=
  let k := Nat.clog 2 P.card
  (binaryRank k fun j => τ.coins[P.maskLength+k*i+j.val]?.getD false).val

/-- Conditions on bit capacity and on the two disjoint workspaces for a single instance. -/
structure Space (P : TrialParameters) (S : Solver) (floor b : ℕ) : Prop where
  two : 2 ≤ b
  floorQuery : floor ≤ P.a
  floorSolve : S.floor ≤ P.a
  trialWidth : Nat.clog 2 P.card+1 ≤ b
  seekWidth : ∀ i < P.trials, (P.maskLength+Nat.clog 2 P.card*i+Nat.clog 2 P.card+2*Nat.clog 2 P.card+2).size ≤ b
  rowWidth : P.pin.size ≤ b
  kernelWidth : P.dim+2 ≤ b
  solverWidth : (P.base+S.space P.N).size ≤ b
  floorWidth : S.floor.size ≤ b
  table : P.base+S.space P.N ≤ P.seenBase
  seenWidth : ∀ xs : List Bool, xs.length=P.dim → (P.seenBase+packed xs).size ≤ b
  countWidth : P.trials.size+P.dim+1 ≤ b

/-- Only the two graph-specific calls remain at this interface. They use the same
finite kernel and the common nine-field calling convention. -/
structure Queries (P : TrialParameters) (τ : Tapes) (b floor cost : ℕ) (kernel : Cmd)
    (eqs : ℕ → Option (List (Equation P.dim))) (value : List Bool → ZMod 2) : Prop where
  padding : ∀ i < P.trials, P.card ≤ P.key τ i → eqs i=none
  valid : ∀ i < P.trials, P.key τ i < P.card →
    ∃ E, eqs i=some E ∧ E.length=P.dim ∧
      ∀ (j : ℕ) (hj : j < (denseWords E).length) (u : Store), P.header u →
        RequestArgs P.a P.mask (P.key τ i) j 2 u → u.Fits b →
        ∃ v k, Exec τ (fun z => z.Fits b) kernel u v k ∧ k ≤ cost ∧ v.mem 0=(denseWords E)[j] ∧
          v.out=u.out ∧ ∀ x ≥ floor,v.mem x=u.mem x
  leaf : ∀ (xs : List Bool), xs.length=P.dim → ∀ u : Store, P.header u →
    RequestArgs P.a P.mask (packed xs) P.target 3 u → u.Fits b →
    ∃ v k, Exec τ (fun z => z.Fits b) kernel u v k ∧ k ≤ cost ∧ v.mem 0=(decide (value xs ≠ 0)).toNat ∧
      v.out=u.out ∧ ∀ x ≥ floor,v.mem x=u.mem x

end TrialParameters

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMTrialProblem

section HamiltonianRAMBootstrap

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open TargetedSamplers.Structured.BinaryStack FiniteSampling

def bootstrap (bank c d : ℕ) (kernel : Cmd) : Cmd :=
  .seq (Circuit.bankCmd bank (initSolverLayout bank c d)) (sharedPrefix bank kernel)

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMBootstrap

section HamiltonianRAMTrialCount

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word AffinePrefixEnumeration

open EditGV897.Main Multidigraph

def startRows (a : ℕ) : Fragment := Structured.sequence [.op (.const (a+8) 2),.op (.add (a+34) (a+52) (a+23))]

def countTrial (bank : ℕ) (kernel counter : Cmd) : Cmd :=
  let a := cell bank
  let valid := Cmd.seq (startRows a).cmd (.seq (rowQueries bank kernel) (countPrepared bank counter))
  .seq (readTrial bank) (.branch (a+14) (a+6) (.op (.const (a+69) 0)) valid)

namespace TrialParameters

def countCost (P : TrialParameters) (S : Solver) (b cost : ℕ) :=
  4*(b*(5*b+9)+15)+9*Nat.clog 2 P.card+P.dim*(P.dim+1)*(cost+5)+S.work P.N+12

end TrialParameters

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMTrialCount

section HamiltonianRAMTrialVisit

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word TargetedSamplers.Structured.BinaryStack

open TargetedSamplers.Structured.RankedPrefix AffinePrefixEnumeration EditGV897.Main Multidigraph BoundedEnumeration

def visitRank (bank : ℕ) (kernel counter : Cmd) : Cmd :=
  .seq (rankPrepared bank counter) (visitWord (cell bank) kernel)

namespace TrialParameters

def visitCost (P : TrialParameters) (S : Solver) (cost : ℕ) := P.dim*(S.work P.N+10)+cost+17

end TrialParameters

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMTrialVisit

section HamiltonianRAMTrialLoop

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open AffinePrefixEnumeration EditGV897.Main Multidigraph

open scoped BigOperators

def runTrials (bank : ℕ) (kernel counter : Cmd) : Cmd :=
  let a := cell bank
  cappedReports (window (a+65) 5) (a+19) (a+23) (a+22) (countTrial bank kernel counter) (visitRank bank kernel counter)

namespace TrialParameters

def emits (f : List Bool → ZMod 2) (seen : Finset (List Bool)) : Bool := decide ((∑ x ∈ seen, f x) ≠ 0)

def estimate (P : TrialParameters) (eqs : ℕ → Option (List (Equation P.dim))) (f : List Bool → ZMod 2) : Bool :=
  let words := fun i => wordsByRank (eqs i)
  let count := fun i => (words i).length
  let seen := applyPrefix (fun i => applyPrefix (insertAt (words i)) (count i)) P.trials ∅
  if prefixReports count P.trials ≤ 12*P.trials then emits f seen else false

end TrialParameters

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMTrialLoop

section HamiltonianInputRunReduction

namespace DirectedHamiltonicity.Main

open Multidigraph Classical FiniteSampling

/-- One finite RAM realizes the graph-derived estimator on every finite coin string.
The budget charges the actual number of trials once and a polynomial per trial. -/
def BoundedInputRuns (P : TargetedSamplers.Program) (A k : ℕ) : Prop :=
  ∀ (n m W : ℕ) (tail head : Fin m → Fin n) (w : Fin m → ℕ), (∀ e, w e ≤ W) →
    ∀ (s t : Fin n), s ≠ t → ∀ (B : ℤ) (coins : List Bool),
      let H : Multidigraph (Fin n) (Fin m) := ⟨tail,head⟩
      let hw := le_inputMaxWeight w
      let G := H.normalizedGraph w s t hw
      let p := H.normalizedWeight w s t hw
      let M := samplingBlockSize n (G.samplingDegree p)*(n+4)
      ∃ cost, P.RunsIn (runTapes (encodeParityInstance n m tail head w s t B) coins) cost
        (some [H.inputEstimator w s t (encInt B) coins]) ∧ cost ≤ (M+1)*A*(n+m+W+1)^k

end DirectedHamiltonicity.Main

end HamiltonianInputRunReduction

section HamiltonianRAMBodyReduction

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured Multidigraph Classical

/-- The estimator body starts at the exact end of the parser and scheduler. The width
and cost polynomials are uniform over both public parameter bounds and over all tapes. -/
def ValidBodyRuns (body : Cmd) (required work : Polynomial ℕ) : Prop :=
  ∀ (n m W : ℕ) (tail head : Fin m → Fin n) (w : Fin m → ℕ), (∀ e, w e ≤ W) →
    ∀ (s t : Fin n), s ≠ t → ∀ (B : ℤ) (coins : List Bool),
    let H : Multidigraph (Fin n) (Fin m) := ⟨tail,head⟩
    let V := inputMaxWeight w
    let G := H.normalizedGraph w s t (le_inputMaxWeight w)
    let p := H.normalizedWeight w s t (le_inputMaxWeight w)
    let d := G.samplingDegree p
    let M := samplingBlockSize n d*(n+4)
    let τ := runTapes (encodeParityInstance n m tail head w s t B) coins
    0 ≤ B ∧ B ≤ (((n-1)*V : ℕ):ℤ) → ∀ (u : Store) (b : ℕ), required.eval (n+m+W+1) ≤ b →
      u.Fits b → GraphView (W := V) tail head w s t graphBase u → u.mem 52=d → u.mem 53=B.toNat →
      u.mem 54=M → u.out=[] → (∀ a ≥ graphBase+(3*m+2),u.mem a=0) →
      ∃ z j, Exec τ (fun v => v.Fits b) body u z j ∧ j ≤ (M+1)*work.eval b ∧
        z.out=[H.inputEstimator w s t (encInt B) coins]

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMBodyReduction


