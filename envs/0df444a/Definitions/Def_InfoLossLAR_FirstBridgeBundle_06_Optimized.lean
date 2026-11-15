-- Prove2me | Definitions.Def_InfoLossLAR_FirstBridgeBundle_06_Optimized
-- name    : InfoLossLAR_FirstBridgeBundle_06_Optimized
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T00:20:19.754204+00:00
-- url     : https://prove2.me/theorems/f9ce1d59-80f5-48a2-8f3a-39e88c79bd77
-- title:
--   Reversible simulation of polynomial classical machines (minimal Toffoli dependencies)
-- statement:
--   A bounded classical computation is translated into a reversible quantum circuit. The definitions specify Boolean expressions and programs, machine states and transitions, bounded execution, code enumeration, and the register addresses used by the generated circuit. The interface keeps the input, random tape, and output registers explicit.
--
--   This version preserves all original declaration types and values. The original pure Toffoli H/T/CNOT gate list is delta-expanded verbatim at its existing use. All serialization functions retain their original names and values. The package imports RuntimeBundle03 directly and does not import FirstBridgeBundle01 through FirstBridgeBundle05. All original public declarations keep their names.
-- source:
--   Companion Lean implementation for InfoLossLAR.WorstCase.fixed_family_gaussian_advantage_transfer. The definitions are extracted from the checked source modules listed in the publication manifest at /private/tmp/p2m_task4/first_bridge_extraction/publication_ready.json. Original generated-source SHA-256: 9ced13bb6887df3de17e3c8defbafa4e3ba1607b4373e6a4332d80eb79c6e384. Current submitted-source SHA-256: 938149d92e81c21b9fd6fb0e6e0ca6db09ee80457378fddd8c02bcdfdcc64db2. Source modules: Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeReversibleCircuit, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeReversibleUniform, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeBooleanCircuit, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_AdvantageBridgeDisjointCircuit, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_AdvantageBridgeSelector, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeBooleanUniform, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeBooleanProgram, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeBooleanExpr, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeBooleanBundle, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeBooleanSize, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeTM2Symbolic, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeTM2Transition, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeTM2CompileStep, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeTM2BoundedRun, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeTM2Size, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeTM2Initial, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeTM2MachineProgram, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeBooleanRPN, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeBooleanRPNRun, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeBooleanCodePoly, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeTM2CodeFamily, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeTM2CodeTransition, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeTM2SlotEnumeration, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeTM2CodeEnumeration, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeTM2CodeRegisters, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeTM2CodeStep, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeTM2CodeLoop, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeTM2CodeLoopSemantics, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeTM2ViewCompilation, Definitions.Def_InfoLossLAR_FirstBridge_Solutions_RegevBridgeTM2CodeGenerate. Current change: delta-expand only the original Toffoli gate-list value, import RuntimeBundle03 directly, and remove unused NativeSupplement alias opens.

import Definitions.Def_InfoLossLAR_RuntimeBundle_03

















































section




















































set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime
open Integration9_9.TM2PlatformSerialization

/-- Reversible Boolean instructions, with distinct control and target wires. -/
inductive ReversibleGate (n : ℕ) where
  | flip (i : Fin n)
  | controlled (i j : Fin n) (hij : i ≠ j)
  | toffoli (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)

namespace ReversibleGate

def act {n : ℕ} : _root_.InfoLossLAR.WorstCase.ReversibleGate n → Bits n → Bits n
  | .flip i, x => Function.update x i (!x i)
  | .controlled i j _, x => Function.update x j (xor (x j) (x i))
  | .toffoli i j k _ _ _, x => Function.update x k (xor (x k) (x i && x j))

theorem act_involutive {n : ℕ} (g : _root_.InfoLossLAR.WorstCase.ReversibleGate n) : Function.Involutive g.act := by
  intro x
  cases g with
  | flip i => simp [_root_.InfoLossLAR.WorstCase.ReversibleGate.act]
  | controlled i j hij =>
    simp [_root_.InfoLossLAR.WorstCase.ReversibleGate.act, Function.update_of_ne hij, Bool.xor_assoc]
  | toffoli i j k hij hik hjk =>
    simp [_root_.InfoLossLAR.WorstCase.ReversibleGate.act, Function.update_of_ne hik, Function.update_of_ne hjk, Bool.xor_assoc]

def equiv {n : ℕ} (g : _root_.InfoLossLAR.WorstCase.ReversibleGate n) : Bits n ≃ Bits n := g.act_involutive.toPerm g.act

@[simp] theorem equiv_apply {n : ℕ} (g : _root_.InfoLossLAR.WorstCase.ReversibleGate n) (x : Bits n) : g.equiv x = g.act x := rfl
@[simp] theorem equiv_symm_apply {n : ℕ} (g : _root_.InfoLossLAR.WorstCase.ReversibleGate n) (x : Bits n) : g.equiv.symm x = g.act x := rfl

/-- Compile directly to the fixed Clifford+T alphabet. -/
def compile {n : ℕ} : _root_.InfoLossLAR.WorstCase.ReversibleGate n → Layered n
  | .flip i => [[.x i]]
  | .controlled i j hij => [[.cnot i j hij]]
  | .toffoli i j k hij hik hjk => ([ Instr.h k,
    Instr.t i, Instr.t j, Instr.t k,
    Instr.cnot i j hij,
    Instr.t j, Instr.t j, Instr.t j, Instr.t j, Instr.t j, Instr.t j, Instr.t j,
    Instr.cnot i j hij,
    Instr.cnot j k hjk,
    Instr.t k, Instr.t k, Instr.t k, Instr.t k, Instr.t k, Instr.t k, Instr.t k,
    Instr.cnot j k hjk,
    Instr.cnot i k hik,
    Instr.t k, Instr.t k, Instr.t k, Instr.t k, Instr.t k, Instr.t k, Instr.t k,
    Instr.cnot i k hik,
    Instr.cnot i k hik,
    Instr.cnot j k hjk,
    Instr.t k,
    Instr.cnot j k hjk,
    Instr.cnot i k hik,
    Instr.h k ]).map (fun gate => [gate])







def code {n : ℕ} : _root_.InfoLossLAR.WorstCase.ReversibleGate n → Str
  | .flip i => encNat 0 ++ encNat i.val
  | .controlled i j _ => encNat 1 ++ encNat i.val ++ encNat j.val
  | .toffoli i j k _ _ _ => encNat 2 ++ encNat i.val ++ encNat j.val ++ encNat k.val
end ReversibleGate

/-- The forward classical action of a finite reversible program. -/
def reversibleAction {n : ℕ} : List (_root_.InfoLossLAR.WorstCase.ReversibleGate n) → Bits n ≃ Bits n
  | [] => Equiv.refl _
  | g :: gs => g.equiv.trans (reversibleAction gs)

def compileReversible {n : ℕ} (gates : List (_root_.InfoLossLAR.WorstCase.ReversibleGate n)) : Layered n :=
  gates.flatMap _root_.InfoLossLAR.WorstCase.ReversibleGate.compile











end InfoLossLAR.WorstCase

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime
open Integration9_9.TM2PlatformSerialization

/-- The explicit Toffoli expansion at the level of unary wire tokens. -/
def toffoliInstructionWords (p q r : Str) : List Str :=
  let h (i : Str) := encNat 0 ++ i
  let t (i : Str) := encNat 2 ++ i
  let c (i j : Str) := encNat 4 ++ i ++ j
  [h r, t p, t q, t r, c p q,
   t q, t q, t q, t q, t q, t q, t q, c p q, c q r,
   t r, t r, t r, t r, t r, t r, t r, c q r, c p r,
   t r, t r, t r, t r, t r, t r, t r, c p r, c p r,
   c q r, t r, c q r, c p r, h r]



/-- Read a reversible instruction and emit the literal list of Clifford+T gate codes. -/
def readReversibleInstruction (xs : Str) : Str × List Str :=
  let tag := _root_.Integration9_9.TM2PlatformSerialization.readUnary xs
  let first := _root_.Integration9_9.TM2PlatformSerialization.readUnary tag.2
  if inputWidth xs = 0 then
    (first.2, [encNat 3 ++ first.1])
  else
    let second := _root_.Integration9_9.TM2PlatformSerialization.readUnary first.2
    if inputWidth xs = 1 then
      (second.2, [encNat 4 ++ first.1 ++ second.1])
    else
      let third := _root_.Integration9_9.TM2PlatformSerialization.readUnary second.2
      (third.2, _root_.InfoLossLAR.WorstCase.toffoliInstructionWords first.1 second.1 third.1)









def readReversibleProgram : Str → Str × List (List Str) := _root_.Integration9_9.TM2PlatformSerialization.readList _root_.InfoLossLAR.WorstCase.readReversibleInstruction







/-- Convert a unary-counted reversible program description, preserving its header. -/
def compileReversibleDescription (xs : Str) : Str :=
  let anc := _root_.Integration9_9.TM2PlatformSerialization.readUnary xs
  let out := _root_.Integration9_9.TM2PlatformSerialization.readUnary anc.2
  let pieces := (_root_.InfoLossLAR.WorstCase.readReversibleProgram out.2).2
  anc.1 ++ out.1 ++ _root_.Integration9_9.TM2PlatformSerialization.serializeWords (pieces.flatten.map (fun word => _root_.Integration9_9.TM2PlatformSerialization.serializeWords [word]))





/-- A family of ordinary finite reversible Boolean circuits. -/
structure ReversibleFamily where
  anc : ℕ → ℕ
  gates : (n : ℕ) → List (_root_.InfoLossLAR.WorstCase.ReversibleGate (n + (anc n + 1)))
  out : (n : ℕ) → Fin (n + (anc n + 1))

def ReversibleFamily.code (F : _root_.InfoLossLAR.WorstCase.ReversibleFamily) (n : ℕ) : Str :=
  encNat (F.anc n) ++ encNat (F.out n).val ++ encStr ((F.gates n).map _root_.InfoLossLAR.WorstCase.ReversibleGate.code)

def ReversibleFamily.compile (F : _root_.InfoLossLAR.WorstCase.ReversibleFamily) : Family where
  anc := F.anc
  circ n := _root_.InfoLossLAR.WorstCase.compileReversible (F.gates n)
  out := F.out











end InfoLossLAR.WorstCase

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity

/-- Boolean assignment instructions with a destination distinct from each source.
The two sources may coincide. -/
inductive BooleanGate (n : ℕ) where
  | constant (target : Fin n) (value : Bool)
  | copy (source target : Fin n) (h : source ≠ target)
  | negate (source target : Fin n) (h : source ≠ target)
  | xor (first second target : Fin n) (hf : first ≠ target) (hs : second ≠ target)
  | and (first second target : Fin n) (hf : first ≠ target) (hs : second ≠ target)

namespace BooleanGate

def target {n : ℕ} : _root_.InfoLossLAR.WorstCase.BooleanGate n → Fin n
  | .constant t _ => t
  | .copy _ t _ => t
  | .negate _ t _ => t
  | .xor _ _ t _ _ => t
  | .and _ _ t _ _ => t

def value {n : ℕ} : _root_.InfoLossLAR.WorstCase.BooleanGate n → Bits n → Bool
  | .constant _ b, _ => b
  | .copy s _ _, x => x s
  | .negate s _ _, x => !x s
  | .xor a b _ _ _, x => Bool.xor (x a) (x b)
  | .and a b _ _ _, x => x a && x b

def assign {n : ℕ} (g : _root_.InfoLossLAR.WorstCase.BooleanGate n) (x : Bits n) : Bits n :=
  Function.update x g.target (g.value x)



/-- The fresh target stores the Boolean value while the input wires are retained. -/
def compile {n : ℕ} : _root_.InfoLossLAR.WorstCase.BooleanGate n → List (_root_.InfoLossLAR.WorstCase.ReversibleGate n)
  | .constant t b => if b then [.flip t] else []
  | .copy s t h => [.controlled s t h]
  | .negate s t h => [.flip t, .controlled s t h]
  | .xor a b t ha hb => [.controlled a t ha, .controlled b t hb]
  | .and a b t ha hb =>
    if hab : a = b then [.controlled a t ha]
    else [.toffoli a b t hab ha hb]




end BooleanGate

/-- Every assignment gets a distinct fresh destination. -/
def BooleanFresh {n : ℕ} (gates : List (_root_.InfoLossLAR.WorstCase.BooleanGate n)) : Prop :=
  gates.Pairwise (fun a b => a.target ≠ b.target)

def booleanRun {n : ℕ} (gates : List (_root_.InfoLossLAR.WorstCase.BooleanGate n)) (x : Bits n) : Bits n :=
  gates.foldl (fun state g => g.assign state) x

def booleanToReversible {n : ℕ} (gates : List (_root_.InfoLossLAR.WorstCase.BooleanGate n)) : List (_root_.InfoLossLAR.WorstCase.ReversibleGate n) :=
  gates.flatMap _root_.InfoLossLAR.WorstCase.BooleanGate.compile











end InfoLossLAR.WorstCase

end

section


















































namespace Integration9_9
end Integration9_9
namespace Integration9_9.FairBitPadding
end Integration9_9.FairBitPadding




set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open scoped BigOperators

/-- Consecutive physical registers, retaining their original wire order. -/
def leftRegister {n m : ℕ} (state : Bits (n+m)) : Bits n := fun i => state (Fin.castAdd m i)
def rightRegister {n m : ℕ} (state : Bits (n+m)) : Bits m := fun i => state (Fin.natAdd n i)

/-- Literal product amplitudes on two disjoint physical registers. -/
def tensorState {n m : ℕ} (first : QState n) (second : QState m) : QState (n+m) :=
  fun state => first (_root_.InfoLossLAR.WorstCase.leftRegister state)*second (_root_.InfoLossLAR.WorstCase.rightRegister state)

def leftInstruction {n m : ℕ} : Instr n → Instr (n+m)
  | .h i => .h (Fin.castAdd m i)
  | .s i => .s (Fin.castAdd m i)
  | .t i => .t (Fin.castAdd m i)
  | .x i => .x (Fin.castAdd m i)
  | .cnot i j hij => .cnot (Fin.castAdd m i) (Fin.castAdd m j) (by
      intro h
      exact hij (Fin.ext (congrArg (fun k : Fin (n+m) => k.val) h)))

def rightInstruction {n m : ℕ} : Instr m → Instr (n+m)
  | .h i => .h (Fin.natAdd n i)
  | .s i => .s (Fin.natAdd n i)
  | .t i => .t (Fin.natAdd n i)
  | .x i => .x (Fin.natAdd n i)
  | .cnot i j hij => .cnot (Fin.natAdd n i) (Fin.natAdd n j) (by
      intro h
      have hv := congrArg Fin.val h
      exact hij (Fin.ext (Nat.add_left_cancel hv)))

















def leftCircuit {n m : ℕ} (circuit : Layered n) : Layered (n+m) :=
  circuit.map (fun layer => layer.map _root_.InfoLossLAR.WorstCase.leftInstruction)
def rightCircuit {n m : ℕ} (circuit : Layered m) : Layered (n+m) :=
  circuit.map (fun layer => layer.map _root_.InfoLossLAR.WorstCase.rightInstruction)



















@[simp] theorem leftInstruction_support {n m : ℕ} (gate : Instr n) :
    (_root_.InfoLossLAR.WorstCase.leftInstruction (m := m) gate).support=gate.support.image (Fin.castAdd m) := by
  cases gate <;> simp [_root_.InfoLossLAR.WorstCase.leftInstruction,Instr.support]

@[simp] theorem rightInstruction_support {n m : ℕ} (gate : Instr m) :
    (_root_.InfoLossLAR.WorstCase.rightInstruction (n := n) gate).support=gate.support.image (Fin.natAdd n) := by
  cases gate <;> simp [_root_.InfoLossLAR.WorstCase.rightInstruction,Instr.support]













@[simp] theorem leftCircuit_depth {n m : ℕ} (circuit : Layered n) :
    depth (_root_.InfoLossLAR.WorstCase.leftCircuit (m := m) circuit)=depth circuit := by simp [depth,_root_.InfoLossLAR.WorstCase.leftCircuit]
@[simp] theorem rightCircuit_depth {n m : ℕ} (circuit : Layered m) :
    depth (_root_.InfoLossLAR.WorstCase.rightCircuit (n := n) circuit)=depth circuit := by simp [depth,_root_.InfoLossLAR.WorstCase.rightCircuit]











end InfoLossLAR.WorstCase

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open scoped BigOperators

@[simp]  theorem _root_.InfoLossLAR.WorstCase.selector_old_ne_new {n : ℕ} (old : Fin n) (fresh : Fin 4) :
    Fin.castAdd 4 old ≠ Fin.natAdd n fresh := by
  intro h
  have hv := congrArg (fun i : Fin (n+4) => i.val) h
  have ho := old.isLt
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

@[simp]  theorem _root_.InfoLossLAR.WorstCase.selector_new_ne_old {n : ℕ} (fresh : Fin 4) (old : Fin n) :
    Fin.natAdd n fresh ≠ Fin.castAdd 4 old := Ne.symm (_root_.InfoLossLAR.WorstCase.selector_old_ne_new old fresh)



















end InfoLossLAR.WorstCase

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime
open Integration9_9.TM2PlatformSerialization

def BooleanGate.code {n : ℕ} : _root_.InfoLossLAR.WorstCase.BooleanGate n → Str
  | .constant t b => encNat (if b then 1 else 0) ++ encNat t.val
  | .copy s t _ => encNat 2 ++ encNat s.val ++ encNat t.val
  | .negate s t _ => encNat 3 ++ encNat s.val ++ encNat t.val
  | .xor a b t _ _ => encNat 4 ++ encNat a.val ++ encNat b.val ++ encNat t.val
  | .and a b t _ _ => encNat 5 ++ encNat a.val ++ encNat b.val ++ encNat t.val

def readBooleanInstruction (xs : Str) : Str × List Str :=
  let tag := _root_.Integration9_9.TM2PlatformSerialization.readUnary xs
  let first := _root_.Integration9_9.TM2PlatformSerialization.readUnary tag.2
  if inputWidth xs = 0 then (first.2, [])
  else if inputWidth xs = 1 then (first.2, [encNat 0 ++ first.1])
  else
    let second := _root_.Integration9_9.TM2PlatformSerialization.readUnary first.2
    if inputWidth xs = 2 then (second.2, [encNat 1 ++ first.1 ++ second.1])
    else if inputWidth xs = 3 then
      (second.2, [encNat 0 ++ second.1, encNat 1 ++ first.1 ++ second.1])
    else
      let third := _root_.Integration9_9.TM2PlatformSerialization.readUnary second.2
      if inputWidth xs = 4 then
        (third.2, [encNat 1 ++ first.1 ++ third.1, encNat 1 ++ second.1 ++ third.1])
      else if inputWidth first.1 = inputWidth second.1 then
        (third.2, [encNat 1 ++ first.1 ++ third.1])
      else (third.2, [encNat 2 ++ first.1 ++ second.1 ++ third.1])











def readBooleanProgram : Str → Str × List (List Str) := _root_.Integration9_9.TM2PlatformSerialization.readList _root_.InfoLossLAR.WorstCase.readBooleanInstruction





def compileBooleanDescription (xs : Str) : Str :=
  let anc := _root_.Integration9_9.TM2PlatformSerialization.readUnary xs
  let out := _root_.Integration9_9.TM2PlatformSerialization.readUnary anc.2
  let pieces := (_root_.InfoLossLAR.WorstCase.readBooleanProgram out.2).2
  anc.1 ++ out.1 ++ _root_.Integration9_9.TM2PlatformSerialization.serializeWords pieces.flatten





structure BooleanFamily where
  anc : ℕ → ℕ
  gates : (n : ℕ) → List (_root_.InfoLossLAR.WorstCase.BooleanGate (n + (anc n + 1)))
  out : (n : ℕ) → Fin (n + (anc n + 1))

def BooleanFamily.code (F : _root_.InfoLossLAR.WorstCase.BooleanFamily) (n : ℕ) : Str :=
  encNat (F.anc n) ++ encNat (F.out n).val ++ encStr ((F.gates n).map _root_.InfoLossLAR.WorstCase.BooleanGate.code)

def BooleanFamily.reversible (F : _root_.InfoLossLAR.WorstCase.BooleanFamily) : _root_.InfoLossLAR.WorstCase.ReversibleFamily where
  anc := F.anc
  gates n := _root_.InfoLossLAR.WorstCase.booleanToReversible (F.gates n)
  out := F.out













end InfoLossLAR.WorstCase

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase
open QAlgorithms.Complexity

/-- A natural-addressed Boolean instruction. The destination is the next fresh wire. -/
inductive BooleanOp where
  | constant (value : Bool)
  | copy (source : ℕ)
  | negate (source : ℕ)
  | xor (first second : ℕ)
  | and (first second : ℕ)
  deriving DecidableEq

namespace BooleanOp

def sources : _root_.InfoLossLAR.WorstCase.BooleanOp → List ℕ
  | .constant _ => []
  | .copy a | .negate a => [a]
  | .xor a b | .and a b => [a, b]

def Valid (bound : ℕ) (op : _root_.InfoLossLAR.WorstCase.BooleanOp) : Prop := ∀ i ∈ op.sources, i < bound

instance _root_.InfoLossLAR.WorstCase.BooleanOp.instDecidableValid (bound : ℕ) (op : _root_.InfoLossLAR.WorstCase.BooleanOp) : Decidable (op.Valid bound) :=
  inferInstanceAs (Decidable (∀ i ∈ op.sources, i < bound))

def eval (op : _root_.InfoLossLAR.WorstCase.BooleanOp) (state : ℕ → Bool) : Bool :=
  match op with
  | .constant b => b
  | .copy a => state a
  | .negate a => !state a
  | .xor a b => Bool.xor (state a) (state b)
  | .and a b => state a && state b



def assign (op : _root_.InfoLossLAR.WorstCase.BooleanOp) (target : ℕ) (state : ℕ → Bool) : ℕ → Bool :=
  Function.update state target (op.eval state)

/-- Invalid references produce a zero instruction; on valid programs the fallback is unused. -/
def toGate {total : ℕ} (op : _root_.InfoLossLAR.WorstCase.BooleanOp) (target : Fin total) : _root_.InfoLossLAR.WorstCase.BooleanGate total :=
  match op with
  | .constant b => .constant target b
  | .copy a => if h : a < target.val then
      .copy ⟨a, h.trans target.isLt⟩ target (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_mk] at hv; omega)
    else .constant target false
  | .negate a => if h : a < target.val then
      .negate ⟨a, h.trans target.isLt⟩ target (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_mk] at hv; omega)
    else .constant target false
  | .xor a b => if h : a < target.val ∧ b < target.val then
      .xor ⟨a, h.1.trans target.isLt⟩ ⟨b, h.2.trans target.isLt⟩ target
        (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_mk] at hv; omega)
        (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_mk] at hv; omega)
    else .constant target false
  | .and a b => if h : a < target.val ∧ b < target.val then
      .and ⟨a, h.1.trans target.isLt⟩ ⟨b, h.2.trans target.isLt⟩ target
        (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_mk] at hv; omega)
        (by intro he; have hv := congrArg Fin.val he; simp only [Fin.val_mk] at hv; omega)
    else .constant target false






end BooleanOp

namespace BooleanProgram

def run : ℕ → List _root_.InfoLossLAR.WorstCase.BooleanOp → (ℕ → Bool) → (ℕ → Bool)
  | _, [], s => s
  | start, op :: rest, s => run (start + 1) rest (op.assign start s)

def Valid : ℕ → List _root_.InfoLossLAR.WorstCase.BooleanOp → Prop
  | _, [] => True
  | start, op :: rest => op.Valid start ∧ Valid (start + 1) rest

/-- Instantiate a fresh-address program on a finite register large enough for its writes. -/
def gates {total : ℕ} (start : ℕ) (ops : List _root_.InfoLossLAR.WorstCase.BooleanOp)
    (h : start + ops.length ≤ total) : List (_root_.InfoLossLAR.WorstCase.BooleanGate total) :=
  match ops with
  | [] => []
  | op :: rest =>
      op.toGate ⟨start, by simp only [List.length_cons] at h; omega⟩ ::
        gates (start + 1) rest (by simp only [List.length_cons] at h; omega)

@[simp] theorem gates_length {total start : ℕ} (ops : List _root_.InfoLossLAR.WorstCase.BooleanOp)
    (h : start + ops.length ≤ total) : (_root_.InfoLossLAR.WorstCase.BooleanProgram.gates start ops h).length = ops.length := by
  induction ops generalizing start with
  | nil => rfl
  | cons op rest ih => simp only [_root_.InfoLossLAR.WorstCase.BooleanProgram.gates, List.length_cons, ih]









theorem valid_append (start : ℕ) (a b : List _root_.InfoLossLAR.WorstCase.BooleanOp) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid start (a ++ b) ↔ _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid start a ∧ _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid (start + a.length) b := by
  induction a generalizing start with
  | nil => simp [_root_.InfoLossLAR.WorstCase.BooleanProgram.Valid]
  | cons op a ih =>
    simp only [List.cons_append, _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid, ih, List.length_cons]
    have he : start + 1 + a.length = start + (a.length + 1) := by omega
    rw [he]; tauto









end BooleanProgram
end InfoLossLAR.WorstCase

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase

/-- Boolean formula syntax used to compile a fixed finite-state transition. -/
inductive BooleanExpr where
  | input (wire : ℕ)
  | constant (value : Bool)
  | negate (arg : BooleanExpr)
  | xor (first second : BooleanExpr)
  | and (first second : BooleanExpr)
  deriving DecidableEq

namespace BooleanExpr

def eval : _root_.InfoLossLAR.WorstCase.BooleanExpr → (ℕ → Bool) → Bool
  | .input i, s => s i
  | .constant b, _ => b
  | .negate a, s => !(a.eval s)
  | .xor a b, s => Bool.xor (a.eval s) (b.eval s)
  | .and a b, s => a.eval s && b.eval s

def Valid (bound : ℕ) : _root_.InfoLossLAR.WorstCase.BooleanExpr → Prop
  | .input i => i < bound
  | .constant _ => True
  | .negate a => a.Valid bound
  | .xor a b | .and a b => a.Valid bound ∧ b.Valid bound

def size : _root_.InfoLossLAR.WorstCase.BooleanExpr → ℕ
  | .input _ => 0
  | .constant _ => 1
  | .negate a => a.size + 1
  | .xor a b | .and a b => a.size + b.size + 1

theorem valid_mono {bound upper : ℕ} (e : _root_.InfoLossLAR.WorstCase.BooleanExpr) (h : e.Valid bound)
    (hle : bound ≤ upper) : e.Valid upper := by
  induction e with
  | input i => exact h.trans_le hle
  | constant b => trivial
  | negate a ih => exact ih h
  | xor a b ia ib | and a b ia ib => exact ⟨ia h.1, ib h.2⟩



/-- Postorder compilation retains each intermediate result on a fresh wire. -/
def compile (start : ℕ) : _root_.InfoLossLAR.WorstCase.BooleanExpr → List _root_.InfoLossLAR.WorstCase.BooleanOp × ℕ
  | .input i => ([], i)
  | .constant b => ([.constant b], start)
  | .negate a =>
      let ca := a.compile start
      (ca.1 ++ [.negate ca.2], start + ca.1.length)
  | .xor a b =>
      let ca := a.compile start
      let cb := b.compile (start + ca.1.length)
      (ca.1 ++ cb.1 ++ [.xor ca.2 cb.2], start + ca.1.length + cb.1.length)
  | .and a b =>
      let ca := a.compile start
      let cb := b.compile (start + ca.1.length)
      (ca.1 ++ cb.1 ++ [.and ca.2 cb.2], start + ca.1.length + cb.1.length)

@[simp] theorem compile_length (e : _root_.InfoLossLAR.WorstCase.BooleanExpr) (start : ℕ) :
    (e.compile start).1.length = e.size := by
  induction e generalizing start <;> simp_all [_root_.InfoLossLAR.WorstCase.BooleanExpr.compile, _root_.InfoLossLAR.WorstCase.BooleanExpr.size, Nat.add_assoc]

theorem compile_valid (e : _root_.InfoLossLAR.WorstCase.BooleanExpr) (start : ℕ) (hv : e.Valid start) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid start (e.compile start).1 ∧ (e.compile start).2 < start + e.size := by
  induction e generalizing start with
  | input i => exact ⟨trivial, by simpa only [_root_.InfoLossLAR.WorstCase.BooleanExpr.compile, _root_.InfoLossLAR.WorstCase.BooleanExpr.size, _root_.InfoLossLAR.WorstCase.BooleanExpr.Valid, Nat.add_zero] using hv⟩
  | constant b => exact ⟨⟨by simp [_root_.InfoLossLAR.WorstCase.BooleanOp.Valid, _root_.InfoLossLAR.WorstCase.BooleanOp.sources], trivial⟩, by simp [_root_.InfoLossLAR.WorstCase.BooleanExpr.compile, _root_.InfoLossLAR.WorstCase.BooleanExpr.size]⟩
  | negate a ih =>
    obtain ⟨ha, hout⟩ := ih start hv
    simp only [_root_.InfoLossLAR.WorstCase.BooleanExpr.compile, _root_.InfoLossLAR.WorstCase.BooleanExpr.compile_length, _root_.InfoLossLAR.WorstCase.BooleanExpr.size]
    constructor
    · apply (_root_.InfoLossLAR.WorstCase.BooleanProgram.valid_append _ _ _).2
      exact ⟨ha, ⟨by simpa [_root_.InfoLossLAR.WorstCase.BooleanOp.Valid, _root_.InfoLossLAR.WorstCase.BooleanOp.sources] using hout, trivial⟩⟩
    · omega
  | xor a b ia ib | and a b ia ib =>
    obtain ⟨ha, hoa⟩ := ia start hv.1
    obtain ⟨hb, hob⟩ := ib (start + a.size) (b.valid_mono hv.2 (by omega))
    simp only [_root_.InfoLossLAR.WorstCase.BooleanExpr.compile, _root_.InfoLossLAR.WorstCase.BooleanExpr.compile_length, _root_.InfoLossLAR.WorstCase.BooleanExpr.size]
    constructor
    · apply (_root_.InfoLossLAR.WorstCase.BooleanProgram.valid_append _ _ _).2
      constructor
      · exact (_root_.InfoLossLAR.WorstCase.BooleanProgram.valid_append _ _ _).2 ⟨ha, by simpa only [_root_.InfoLossLAR.WorstCase.BooleanExpr.compile_length] using hb⟩
      · simp only [List.length_append, _root_.InfoLossLAR.WorstCase.BooleanExpr.compile_length]
        constructor
        · simp only [_root_.InfoLossLAR.WorstCase.BooleanOp.Valid, _root_.InfoLossLAR.WorstCase.BooleanOp.sources, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp]
          exact ⟨by omega, by omega⟩
        · trivial
    · omega







def or (a b : _root_.InfoLossLAR.WorstCase.BooleanExpr) : _root_.InfoLossLAR.WorstCase.BooleanExpr := .negate (.and (.negate a) (.negate b))
def select (c a b : _root_.InfoLossLAR.WorstCase.BooleanExpr) : _root_.InfoLossLAR.WorstCase.BooleanExpr := _root_.InfoLossLAR.WorstCase.BooleanExpr.or (.and c a) (.and (.negate c) b)

@[simp] theorem eval_or (a b : _root_.InfoLossLAR.WorstCase.BooleanExpr) (s : ℕ → Bool) :
    (_root_.InfoLossLAR.WorstCase.BooleanExpr.or a b).eval s = (a.eval s || b.eval s) := by
  cases ha : a.eval s <;> cases hb : b.eval s <;> simp [_root_.InfoLossLAR.WorstCase.BooleanExpr.or, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval, ha, hb]

@[simp] theorem eval_select (c a b : _root_.InfoLossLAR.WorstCase.BooleanExpr) (s : ℕ → Bool) :
    (_root_.InfoLossLAR.WorstCase.BooleanExpr.select c a b).eval s = if c.eval s then a.eval s else b.eval s := by
  cases hc : c.eval s <;> cases ha : a.eval s <;> cases hb : b.eval s <;>
    simp [_root_.InfoLossLAR.WorstCase.BooleanExpr.select, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval_or, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval, hc, ha, hb]

end BooleanExpr
end InfoLossLAR.WorstCase

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase
namespace BooleanExpr

def any : List _root_.InfoLossLAR.WorstCase.BooleanExpr → _root_.InfoLossLAR.WorstCase.BooleanExpr
  | [] => .constant false
  | a :: rest => _root_.InfoLossLAR.WorstCase.BooleanExpr.or a (any rest)

@[simp] theorem eval_any_true (es : List _root_.InfoLossLAR.WorstCase.BooleanExpr) (s : ℕ → Bool) :
    (_root_.InfoLossLAR.WorstCase.BooleanExpr.any es).eval s = true ↔ ∃ e ∈ es, e.eval s = true := by
  induction es with
  | nil => simp [_root_.InfoLossLAR.WorstCase.BooleanExpr.any, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval]
  | cons e es ih => simp [_root_.InfoLossLAR.WorstCase.BooleanExpr.any, _root_.InfoLossLAR.WorstCase.BooleanExpr.eval_or, ih]

theorem valid_any {bound : ℕ} (es : List _root_.InfoLossLAR.WorstCase.BooleanExpr)
    (h : ∀ e ∈ es, e.Valid bound) : (_root_.InfoLossLAR.WorstCase.BooleanExpr.any es).Valid bound := by
  induction es with
  | nil => trivial
  | cons e es ih =>
    exact ⟨h e (by simp), ih (fun a ha => h a (by simp [ha]))⟩

/-- A fixed finite truth table is a disjunction of selected one-hot input wires. -/
noncomputable def lookup {α : Type} [Fintype α]
    (table : α → Bool) (inputs : α → _root_.InfoLossLAR.WorstCase.BooleanExpr) : _root_.InfoLossLAR.WorstCase.BooleanExpr :=
  _root_.InfoLossLAR.WorstCase.BooleanExpr.any ((Finset.univ.toList.filter table).map inputs)



theorem valid_lookup {α : Type} [Fintype α] {bound : ℕ}
    (table : α → Bool) (inputs : α → _root_.InfoLossLAR.WorstCase.BooleanExpr)
    (h : ∀ a, (inputs a).Valid bound) : (_root_.InfoLossLAR.WorstCase.BooleanExpr.lookup table inputs).Valid bound := by
  apply _root_.InfoLossLAR.WorstCase.BooleanExpr.valid_any
  intro e he
  obtain ⟨a, _, rfl⟩ := List.mem_map.1 he
  exact h a

/-- Compile several outputs without duplicating the expressions from previous simulation steps. -/
def compileMany (start : ℕ) : List _root_.InfoLossLAR.WorstCase.BooleanExpr → List _root_.InfoLossLAR.WorstCase.BooleanOp × List ℕ
  | [] => ([], [])
  | e :: rest =>
      let first := e.compile start
      let tail := compileMany (start + first.1.length) rest
      (first.1 ++ tail.1, first.2 :: tail.2)

@[simp] theorem compileMany_length (start : ℕ) (es : List _root_.InfoLossLAR.WorstCase.BooleanExpr) :
    (_root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany start es).1.length = (es.map _root_.InfoLossLAR.WorstCase.BooleanExpr.size).sum := by
  induction es generalizing start with
  | nil => rfl
  | cons e es ih => simp only [_root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany, List.length_append, _root_.InfoLossLAR.WorstCase.BooleanExpr.compile_length, ih,
      List.map_cons, List.sum_cons]

@[simp] theorem compileMany_outputs_length (start : ℕ) (es : List _root_.InfoLossLAR.WorstCase.BooleanExpr) :
    (_root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany start es).2.length = es.length := by
  induction es generalizing start with
  | nil => rfl
  | cons e es ih => simp only [_root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany, List.length_cons, ih]

theorem compileMany_valid (start : ℕ) (es : List _root_.InfoLossLAR.WorstCase.BooleanExpr)
    (h : ∀ e ∈ es, e.Valid start) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid start (_root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany start es).1 ∧
      ∀ i ∈ (_root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany start es).2, i < start + (es.map _root_.InfoLossLAR.WorstCase.BooleanExpr.size).sum := by
  induction es generalizing start with
  | nil => exact ⟨trivial, by simp [_root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany]⟩
  | cons e es ih =>
    obtain ⟨he, hout⟩ := e.compile_valid start (h e (by simp))
    obtain ⟨ht, houts⟩ := ih (start + e.size)
      (fun a ha => a.valid_mono (h a (by simp [ha])) (Nat.le_add_right _ _))
    simp only [_root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany, _root_.InfoLossLAR.WorstCase.BooleanExpr.compile_length]
    constructor
    · exact (_root_.InfoLossLAR.WorstCase.BooleanProgram.valid_append _ _ _).2 ⟨he, by simpa only [_root_.InfoLossLAR.WorstCase.BooleanExpr.compile_length] using ht⟩
    · intro i hi
      simp only [List.mem_cons] at hi
      simp only [List.map_cons, List.sum_cons]
      rcases hi with rfl | hi
      · omega
      · have hh := houts i hi
        omega



/-- A finite multiplexer, with one selected branch, on one-hot control bits. -/
noncomputable def multiplex {α : Type} [Fintype α]
    (control payload : α → _root_.InfoLossLAR.WorstCase.BooleanExpr) : _root_.InfoLossLAR.WorstCase.BooleanExpr :=
  _root_.InfoLossLAR.WorstCase.BooleanExpr.any (Finset.univ.toList.map (fun a => .and (control a) (payload a)))



theorem valid_multiplex {α : Type} [Fintype α] {bound : ℕ}
    (control payload : α → _root_.InfoLossLAR.WorstCase.BooleanExpr)
    (hc : ∀ a, (control a).Valid bound) (hp : ∀ a, (payload a).Valid bound) :
    (_root_.InfoLossLAR.WorstCase.BooleanExpr.multiplex control payload).Valid bound := by
  apply _root_.InfoLossLAR.WorstCase.BooleanExpr.valid_any
  intro e he
  obtain ⟨a, _, rfl⟩ := List.mem_map.1 he
  exact ⟨hc a, hp a⟩

end BooleanExpr
end InfoLossLAR.WorstCase

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace InfoLossLAR.WorstCase.BooleanExpr

@[simp] theorem size_or (a b : _root_.InfoLossLAR.WorstCase.BooleanExpr) : (_root_.InfoLossLAR.WorstCase.BooleanExpr.or a b).size = a.size + b.size + 4 := by
  simp only [_root_.InfoLossLAR.WorstCase.BooleanExpr.or, _root_.InfoLossLAR.WorstCase.BooleanExpr.size]; omega

@[simp] theorem size_select (c a b : _root_.InfoLossLAR.WorstCase.BooleanExpr) :
    (_root_.InfoLossLAR.WorstCase.BooleanExpr.select c a b).size = 2 * c.size + a.size + b.size + 7 := by
  simp only [_root_.InfoLossLAR.WorstCase.BooleanExpr.select, _root_.InfoLossLAR.WorstCase.BooleanExpr.size_or, _root_.InfoLossLAR.WorstCase.BooleanExpr.size]; omega

theorem valid_select {bound : ℕ} (c a b : _root_.InfoLossLAR.WorstCase.BooleanExpr)
    (hc : c.Valid bound) (ha : a.Valid bound) (hb : b.Valid bound) :
    (_root_.InfoLossLAR.WorstCase.BooleanExpr.select c a b).Valid bound := ⟨⟨hc, ha⟩, ⟨hc, hb⟩⟩







end InfoLossLAR.WorstCase.BooleanExpr

end

section

















































namespace Integration9_9
end Integration9_9
namespace Integration9_9.TM2OutputLength
end Integration9_9.TM2OutputLength
namespace Integration9_9.TM2OutputLength.pushBound
end Integration9_9.TM2OutputLength.pushBound
namespace Integration9_9.TM2OutputLength.pushBound.match_1
end Integration9_9.TM2OutputLength.pushBound.match_1



set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean
open Turing
variable {K Λ σ : Type} [DecidableEq K] [DecidableEq Λ] [DecidableEq σ] [Fintype σ]

/-- One-hot finite control and fixed-capacity Boolean stacks. -/
structure Symbolic (K Λ σ : Type) (width : ℕ) where
  label : Option Λ → _root_.InfoLossLAR.WorstCase.BooleanExpr
  state : σ → _root_.InfoLossLAR.WorstCase.BooleanExpr
  stack : K → Fin width → Option Bool → _root_.InfoLossLAR.WorstCase.BooleanExpr

abbrev Configuration (K Λ σ : Type) := TM2.Cfg (fun _ : K => Bool) Λ σ

structure Encodes {width : ℕ} (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width)
    (cfg : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ) (bits : ℕ → Bool) : Prop where
  label : ∀ l, (sym.label l).eval bits = decide (l = cfg.l)
  state : ∀ v, (sym.state v).eval bits = decide (v = cfg.var)
  stack : ∀ k i b, (sym.stack k i b).eval bits = decide (b = (cfg.stk k)[i.val]?)

namespace Symbolic
variable {width : ℕ}

noncomputable def load (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (f : σ → σ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width :=
  {sym with state v := _root_.InfoLossLAR.WorstCase.BooleanExpr.lookup (fun a => decide (v = f a)) sym.state}

noncomputable def push (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (k : K) (f : σ → Bool) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width :=
  {sym with stack j i b := if j = k then
    if hz : i.val = 0 then _root_.InfoLossLAR.WorstCase.BooleanExpr.lookup (fun a => decide (b = some (f a))) sym.state
    else sym.stack k ⟨i.val - 1, by omega⟩ b
    else sym.stack j i b}

noncomputable def read (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (hw : 0 < width)
    (k : K) (f : σ → Option Bool → σ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width :=
  {sym with
    state v := _root_.InfoLossLAR.WorstCase.BooleanExpr.lookup (fun a : σ × Option Bool => decide (v = f a.1 a.2))
      (fun a => .and (sym.state a.1) (sym.stack k ⟨0, hw⟩ a.2))}

def pop (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (k : K) : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width :=
  {sym with stack j i b := if j = k then
    if h : i.val + 1 < width then sym.stack k ⟨i.val + 1, h⟩ b
    else .constant (decide (b = none))
    else sym.stack j i b}

noncomputable def jump (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (f : σ → Λ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width :=
  {sym with label l := _root_.InfoLossLAR.WorstCase.BooleanExpr.lookup (fun a => decide (l = some (f a))) sym.state}

def halt (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width :=
  {sym with label l := .constant (decide (l = none))}

def select (condition : _root_.InfoLossLAR.WorstCase.BooleanExpr) (a b : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width where
  label l := _root_.InfoLossLAR.WorstCase.BooleanExpr.select condition (a.label l) (b.label l)
  state v := _root_.InfoLossLAR.WorstCase.BooleanExpr.select condition (a.state v) (b.state v)
  stack k i x := _root_.InfoLossLAR.WorstCase.BooleanExpr.select condition (a.stack k i x) (b.stack k i x)















end Symbolic
end InfoLossLAR.WorstCase.TM2Boolean

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean
open Turing
open Integration9_9.TM2OutputLength
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]
variable {width : ℕ}

/-- Every finite TM2 statement is translated to explicit Boolean formulas. -/
noncomputable def auxiliary (hw : 0 < width) :
    TM2.Stmt (fun _ : K => Bool) Λ σ → _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width → _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width
  | .push k f q, sym => auxiliary hw q (sym.push k f)
  | .peek k f q, sym => auxiliary hw q (sym.read hw k f)
  | .pop k f q, sym => auxiliary hw q ((sym.read hw k f).pop k)
  | .load f q, sym => auxiliary hw q (sym.load f)
  | .branch f q r, sym =>
      _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.select (_root_.InfoLossLAR.WorstCase.BooleanExpr.lookup f sym.state) (auxiliary hw q sym) (auxiliary hw r sym)
  | .goto f, sym => sym.jump f
  | .halt, sym => sym.halt



noncomputable def multiplex {α : Type} [Fintype α]
    (control : α → _root_.InfoLossLAR.WorstCase.BooleanExpr) (choices : α → _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width where
  label l := _root_.InfoLossLAR.WorstCase.BooleanExpr.multiplex control (fun a => (choices a).label l)
  state v := _root_.InfoLossLAR.WorstCase.BooleanExpr.multiplex control (fun a => (choices a).state v)
  stack k i b := _root_.InfoLossLAR.WorstCase.BooleanExpr.multiplex control (fun a => (choices a).stack k i b)



/-- A halted configuration stays fixed, allowing a time-bounded circuit to run exactly its budget. -/
def stickyStep (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (cfg : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ :=
  cfg.l.elim cfg (fun l => TM2.stepAux (program l) cfg.var cfg.stk)

noncomputable def transition (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width :=
  _root_.InfoLossLAR.WorstCase.TM2Boolean.multiplex sym.label (fun l => l.elim sym (fun l => _root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliary hw (program l) sym))



end InfoLossLAR.WorstCase.TM2Boolean

end

section




















































set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean
open Turing
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]
variable {width : ℕ}

namespace Symbolic

structure Valid (bound : ℕ) (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) : Prop where
  label : ∀ l, (sym.label l).Valid bound
  state : ∀ v, (sym.state v).Valid bound
  stack : ∀ k i b, (sym.stack k i b).Valid bound

theorem load_valid (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound) (f : σ → σ) :
    (sym.load f).Valid bound := ⟨h.label, fun _ => _root_.InfoLossLAR.WorstCase.BooleanExpr.valid_lookup _ _ h.state, h.stack⟩

theorem push_valid (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound) (k : K) (f : σ → Bool) :
    (sym.push k f).Valid bound := by
  refine ⟨h.label, h.state, ?_⟩
  intro j i b
  dsimp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.push]
  split_ifs
  · exact _root_.InfoLossLAR.WorstCase.BooleanExpr.valid_lookup _ _ h.state
  · exact h.stack _ _ _
  · exact h.stack _ _ _

theorem read_valid (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound)
    (hw : 0 < width) (k : K) (f : σ → Option Bool → σ) : (sym.read hw k f).Valid bound := by
  refine ⟨h.label, ?_, h.stack⟩
  intro v
  apply _root_.InfoLossLAR.WorstCase.BooleanExpr.valid_lookup
  intro a
  exact ⟨h.state a.1, h.stack _ _ _⟩

theorem pop_valid (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound) (k : K) :
    (sym.pop k).Valid bound := by
  refine ⟨h.label, h.state, ?_⟩
  intro j i b
  dsimp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.pop]
  split_ifs
  · exact h.stack _ _ _
  · trivial
  · exact h.stack _ _ _

theorem jump_valid (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound) (f : σ → Λ) :
    (sym.jump f).Valid bound := ⟨fun _ => _root_.InfoLossLAR.WorstCase.BooleanExpr.valid_lookup _ _ h.state, h.state, h.stack⟩

theorem halt_valid (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound) :
    sym.halt.Valid bound := ⟨fun _ => trivial, h.state, h.stack⟩

theorem select_valid (condition : _root_.InfoLossLAR.WorstCase.BooleanExpr) (a b : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) {bound : ℕ}
    (hc : condition.Valid bound) (ha : a.Valid bound) (hb : b.Valid bound) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.select condition a b).Valid bound :=
  ⟨fun l => _root_.InfoLossLAR.WorstCase.BooleanExpr.valid_select _ _ _ hc (ha.label l) (hb.label l),
    fun v => _root_.InfoLossLAR.WorstCase.BooleanExpr.valid_select _ _ _ hc (ha.state v) (hb.state v),
    fun k i b => _root_.InfoLossLAR.WorstCase.BooleanExpr.valid_select _ _ _ hc (ha.stack k i b) (hb.stack k i b)⟩
end Symbolic

theorem auxiliary_valid (hw : 0 < width) (q : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliary hw q sym).Valid bound := by
  induction q generalizing sym with
  | push k f q ih => exact ih _ (sym.push_valid h k f)
  | peek k f q ih => exact ih _ (sym.read_valid h hw k f)
  | pop k f q ih => exact ih _ ((sym.read hw k f).pop_valid (sym.read_valid h hw k f) k)
  | load f q ih => exact ih _ (sym.load_valid h f)
  | branch f q r iq ir =>
    exact _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.select_valid _ _ _ (_root_.InfoLossLAR.WorstCase.BooleanExpr.valid_lookup f sym.state h.state) (iq _ h) (ir _ h)
  | goto f => exact sym.jump_valid h f
  | halt => exact sym.halt_valid h

theorem transition_valid (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.transition hw program sym).Valid bound := by
  have hx : ∀ l : Option Λ, (l.elim sym (fun l => _root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliary hw (program l) sym)).Valid bound := by
    intro l
    cases l with
    | none => exact h
    | some l => exact _root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliary_valid hw (program l) sym h
  constructor
  · intro l
    exact _root_.InfoLossLAR.WorstCase.BooleanExpr.valid_multiplex sym.label _ h.label (fun a => (hx a).label l)
  · intro v
    exact _root_.InfoLossLAR.WorstCase.BooleanExpr.valid_multiplex sym.label _ h.label (fun a => (hx a).state v)
  · intro k i b
    exact _root_.InfoLossLAR.WorstCase.BooleanExpr.valid_multiplex sym.label _ h.label (fun a => (hx a).stack k i b)

/-- Every component of a fixed-capacity machine configuration has an explicit slot. -/
abbrev Slot (K Λ σ : Type) (width : ℕ) := Option Λ ⊕ (σ ⊕ (K × Fin width × Option Bool))

/-- The order varies with capacity only through canonical sum/product indices.
The finite permutations for stack names and control states are fixed once for the machine. -/
noncomputable def slotEquiv (K Λ σ : Type) [Fintype K] [Fintype Λ] [Fintype σ] (width : ℕ) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width ≃ Fin (Fintype.card (_root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width)) :=
  let cells := (Equiv.prodCongr (Equiv.refl (Fin width)) (Fintype.equivFin (Option Bool))).trans finProdFinEquiv
  let stacksEq := (Equiv.prodCongr (Fintype.equivFin K) cells).trans finProdFinEquiv
  let tail := (Equiv.sumCongr (Fintype.equivFin σ) stacksEq).trans finSumFinEquiv
  let all := (Equiv.sumCongr (Fintype.equivFin (Option Λ)) tail).trans finSumFinEquiv
  all.trans (finCongr (by simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Slot, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]))

namespace Symbolic

def get (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) : _root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width → _root_.InfoLossLAR.WorstCase.BooleanExpr
  | .inl l => sym.label l
  | .inr (.inl v) => sym.state v
  | .inr (.inr (k, i, b)) => sym.stack k i b

def ofSlots (f : _root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width → _root_.InfoLossLAR.WorstCase.BooleanExpr) : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width where
  label l := f (.inl l)
  state v := f (.inr (.inl v))
  stack k i b := f (.inr (.inr (k, i, b)))

@[simp] theorem get_ofSlots (f : _root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width → _root_.InfoLossLAR.WorstCase.BooleanExpr) (i : _root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.ofSlots f).get i = f i := by
  rcases i with l | v | ⟨k, i, b⟩ <;> rfl

theorem get_valid (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound)
    (i : _root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width) : (sym.get i).Valid bound := by
  rcases i with l | v | ⟨k, i, b⟩
  · exact h.label l
  · exact h.state v
  · exact h.stack k i b

noncomputable def formulas (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) : List _root_.InfoLossLAR.WorstCase.BooleanExpr :=
  List.ofFn (fun i : Fin (Fintype.card (_root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width)) => sym.get ((_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ width).symm i))

@[simp] theorem formulas_length (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) :
    sym.formulas.length = Fintype.card (_root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width) := List.length_ofFn

noncomputable def compiled (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (start : ℕ) : List _root_.InfoLossLAR.WorstCase.BooleanOp × List ℕ :=
  _root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany start sym.formulas

noncomputable def output (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (start : ℕ) (i : _root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width) : ℕ :=
  (sym.compiled start).2[(_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ width i).val]'(by
    simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.compiled, _root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany_outputs_length, _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.formulas_length]
    exact (_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ width i).isLt)

noncomputable def rebound (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (start : ℕ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width :=
  _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.ofSlots (fun i => .input (sym.output start i))

theorem formulas_valid (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) {bound : ℕ} (h : sym.Valid bound) :
    ∀ e ∈ sym.formulas, e.Valid bound := by
  intro e he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
  exact sym.get_valid h _

theorem compiled_valid (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (start : ℕ) (h : sym.Valid start) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid start (sym.compiled start).1 :=
  (_root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany_valid start sym.formulas (sym.formulas_valid h)).1

theorem output_lt (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (start : ℕ) (h : sym.Valid start)
    (i : _root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width) : sym.output start i < start + (sym.compiled start).1.length := by
  have hb := (_root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany_valid start sym.formulas (sym.formulas_valid h)).2
    (sym.output start i) (List.getElem_mem _)
  simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.compiled, _root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany_length] using hb

theorem rebound_valid (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (start : ℕ) (h : sym.Valid start) :
    (sym.rebound start).Valid (start + (sym.compiled start).1.length) :=
  ⟨fun _ => sym.output_lt start h _, fun _ => sym.output_lt start h _,
    fun _ _ _ => sym.output_lt start h _⟩





end Symbolic
end InfoLossLAR.WorstCase.TM2Boolean

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean
open Turing StateTransition
open Integration9_9.TM2OutputLength
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]
variable {width : ℕ}

noncomputable def compileRun (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) :
    ℕ → ℕ → _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width → List _root_.InfoLossLAR.WorstCase.BooleanOp × _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width
  | 0, _, sym => ([], sym)
  | ticks + 1, start, sym =>
      let formulas := _root_.InfoLossLAR.WorstCase.TM2Boolean.transition hw program sym
      let first := formulas.compiled start
      let rest := compileRun hw program ticks (start + first.1.length) (formulas.rebound start)
      (first.1 ++ rest.1, rest.2)

theorem compileRun_valid (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (ticks start : ℕ)
    (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (h : sym.Valid start) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid start (_root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun hw program ticks start sym).1 ∧
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun hw program ticks start sym).2.Valid
        (start + (_root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun hw program ticks start sym).1.length) := by
  induction ticks generalizing start sym with
  | zero => exact ⟨trivial, by simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun, List.length_nil, Nat.add_zero] using h⟩
  | succ ticks ih =>
    have ht := _root_.InfoLossLAR.WorstCase.TM2Boolean.transition_valid hw program sym h
    have hf := (_root_.InfoLossLAR.WorstCase.TM2Boolean.transition hw program sym).compiled_valid start ht
    have hr := (_root_.InfoLossLAR.WorstCase.TM2Boolean.transition hw program sym).rebound_valid start ht
    obtain ⟨hc, hlast⟩ := ih _ _ hr
    constructor
    · exact (_root_.InfoLossLAR.WorstCase.BooleanProgram.valid_append _ _ _).2 ⟨hf, hc⟩
    · simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun, List.length_append, Nat.add_assoc] using hlast















end InfoLossLAR.WorstCase.TM2Boolean

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean
open Turing
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]
variable {width : ℕ}

namespace Symbolic
structure Bounded (bound : ℕ) (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) : Prop where
  label : ∀ l, (sym.label l).size ≤ bound
  state : ∀ v, (sym.state v).size ≤ bound
  stack : ∀ k i b, (sym.stack k i b).size ≤ bound



def lookupBound (σ : Type) [Fintype σ] (bound : ℕ) : ℕ :=
  (bound + 4) * Fintype.card σ + 1

def readBound (σ : Type) [Fintype σ] (bound : ℕ) : ℕ :=
  (2 * bound + 5) * Fintype.card (σ × Option Bool) + 1

def operationBound (σ : Type) [Fintype σ] (bound : ℕ) : ℕ :=
  bound + _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.lookupBound σ bound + _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.readBound σ bound





















@[simp] theorem rebound_bounded_zero (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) (start : ℕ) :
    (sym.rebound start).Bounded 0 := ⟨fun _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl⟩


end Symbolic

/-- A constant-size formula bound for each fixed machine statement. -/
def auxiliaryBound : TM2.Stmt (fun _ : K => Bool) Λ σ → ℕ → ℕ
  | .push _ _ q, b => auxiliaryBound q (_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.operationBound σ b)
  | .peek _ _ q, b => auxiliaryBound q (_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.operationBound σ b)
  | .pop _ _ q, b => auxiliaryBound q (_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.operationBound σ b)
  | .load _ q, b => auxiliaryBound q (_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.operationBound σ b)
  | .branch _ q r, b => 2 * _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.lookupBound σ b + auxiliaryBound q b + auxiliaryBound r b + 7
  | .goto _, b => _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.operationBound σ b
  | .halt, b => b + 1



noncomputable def transitionBound (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (bound : ℕ) : ℕ :=
  (bound + (bound + Finset.univ.sup (fun l => _root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliaryBound (program l) bound)) + 5) *
    Fintype.card (Option Λ) + 1





end InfoLossLAR.WorstCase.TM2Boolean

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean
open Turing
open Integration9_9.TM2OutputLength
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

/-- Actual input bits give a one-hot nonempty Boolean stack cell. -/
def inputCell (wire : ℕ) : Option Bool → _root_.InfoLossLAR.WorstCase.BooleanExpr
  | none => .constant false
  | some false => .negate (.input wire)
  | some true => .input wire



def initial (input : K) (main : Λ) (initialState : σ) (length width : ℕ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width where
  label l := .constant (decide (l = some main))
  state v := .constant (decide (v = initialState))
  stack k i b := if k = input ∧ i.val < length then _root_.InfoLossLAR.WorstCase.TM2Boolean.inputCell i.val b
    else .constant (decide (b = none))

def initialConfiguration (input : K) (main : Λ) (initialState : σ) (word : List Bool) : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ :=
  ⟨some main, initialState, fun k => if k = input then word else []⟩

theorem initial_valid (input : K) (main : Λ) (initialState : σ) (length width : ℕ) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.initial input main initialState length width).Valid length := by
  refine ⟨fun _ => trivial, fun _ => trivial, ?_⟩
  intro k i b
  dsimp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.initial]
  split_ifs with h
  · cases b with
    | none => trivial
    | some b => cases b <;> exact h.2
  · trivial







@[simp] theorem slot_count (width : ℕ) :
    Fintype.card (_root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width) = Fintype.card Λ + 1 + Fintype.card σ +
      Fintype.card K * width * 3 := by
  simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Slot, Fintype.card_sum, Fintype.card_option, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool]
  ring

end InfoLossLAR.WorstCase.TM2Boolean

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean
open Turing
open Integration9_9.TM2OutputLength
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]
variable {width : ℕ}

def configurationBit (cfg : _root_.InfoLossLAR.WorstCase.TM2Boolean.Configuration K Λ σ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width → Bool
  | .inl l => decide (l = cfg.l)
  | .inr (.inl v) => decide (v = cfg.var)
  | .inr (.inr (k, i, b)) => decide (b = (cfg.stk k)[i.val]?)





/-- The compiled classical machine, together with every one-hot output reference. -/
structure MachineProgram (K Λ σ : Type) (width : ℕ) where
  ops : List _root_.InfoLossLAR.WorstCase.BooleanOp
  output : _root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width → ℕ

noncomputable def machineProgram (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks length : ℕ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.MachineProgram K Λ σ width :=
  let init := _root_.InfoLossLAR.WorstCase.TM2Boolean.initial input main initialState length width
  let first := init.compiled length
  let rest := _root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun hw program ticks (length + first.1.length) (init.rebound length)
  let lastStart := length + first.1.length + rest.1.length
  { ops := first.1 ++ rest.1 ++ (rest.2.compiled lastStart).1
    output := rest.2.output lastStart }

theorem machineProgram_valid (hw : 0 < width)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (ticks length : ℕ) :
    _root_.InfoLossLAR.WorstCase.BooleanProgram.Valid length (_root_.InfoLossLAR.WorstCase.TM2Boolean.machineProgram hw program input main initialState ticks length).ops ∧
      ∀ i, (_root_.InfoLossLAR.WorstCase.TM2Boolean.machineProgram hw program input main initialState ticks length).output i <
        length + (_root_.InfoLossLAR.WorstCase.TM2Boolean.machineProgram hw program input main initialState ticks length).ops.length := by
  let init := _root_.InfoLossLAR.WorstCase.TM2Boolean.initial input main initialState length width
  have hi : init.Valid length := _root_.InfoLossLAR.WorstCase.TM2Boolean.initial_valid input main initialState length width
  have hp := init.compiled_valid length hi
  have hr := _root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun_valid hw program ticks _ _ (init.rebound_valid length hi)
  constructor
  · apply (_root_.InfoLossLAR.WorstCase.BooleanProgram.valid_append _ _ _).2
    constructor
    · exact (_root_.InfoLossLAR.WorstCase.BooleanProgram.valid_append _ _ _).2 ⟨hp, hr.1⟩
    · simpa only [List.length_append, Nat.add_assoc] using
        (_root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun hw program ticks _ _).2.compiled_valid _ hr.2
  · intro i
    have hh := (_root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun hw program ticks _ _).2.output_lt _ hr.2 i
    simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.machineProgram, List.length_append, Nat.add_assoc, init] using hh





end InfoLossLAR.WorstCase.TM2Boolean

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

abbrev Token := ℕ × ℕ
abbrev Node := ℕ × (ℕ × ℕ)
/-- A unary fresh-address supply, an operand stack, and the emitted instruction list. -/
abbrev State := List Unit × (List ℕ × List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Node)

def node : _root_.InfoLossLAR.WorstCase.BooleanOp → _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Node
  | .constant false => (0, 0, 0)
  | .constant true => (1, 0, 0)
  | .copy a => (2, a, 0)
  | .negate a => (3, a, 0)
  | .xor a b => (4, a, b)
  | .and a b => (5, a, b)

def code : _root_.InfoLossLAR.WorstCase.BooleanExpr → List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Token
  | .input a => [(0, a)]
  | .constant false => [(1, 0)]
  | .constant true => [(2, 0)]
  | .negate a => code a ++ [(3, 0)]
  | .xor a b => code a ++ code b ++ [(4, 0)]
  | .and a b => code a ++ code b ++ [(5, 0)]

def emit (s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State) (instruction : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Node) (rest : List ℕ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State :=
  (s.1 ++ [()], s.1.length :: rest, s.2.2 ++ [instruction])

def step (s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State) (token : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Token) : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State :=
  if token.1 = 0 then (s.1, token.2 :: s.2.1, s.2.2)
  else if token.1 = 1 then _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.emit s (0, 0, 0) s.2.1
  else if token.1 = 2 then _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.emit s (1, 0, 0) s.2.1
  else if token.1 = 3 then _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.emit s (3, (s.2.1[0]?).getD 0, 0) s.2.1.tail
  else if token.1 = 4 then _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.emit s (4, (s.2.1[1]?).getD 0, (s.2.1[0]?).getD 0) s.2.1.tail.tail
  else _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.emit s (5, (s.2.1[1]?).getD 0, (s.2.1[0]?).getD 0) s.2.1.tail.tail





def run (tokens : List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Token) (s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State) : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State := tokens.foldl _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.step s

@[simp] theorem run_append (first second : List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Token) (s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run (first ++ second) s = _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run second (_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run first s) := List.foldl_append

/-- The literal stack transducer emits exactly the verified postorder Boolean compiler. -/
theorem run_code (e : _root_.InfoLossLAR.WorstCase.BooleanExpr) (slots : List Unit) (operands : List ℕ) (output : List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Node) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run (_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code e) (slots, operands, output) =
      (slots ++ List.replicate e.size (), (e.compile slots.length).2 :: operands,
        output ++ (e.compile slots.length).1.map _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node) := by
  induction e generalizing slots operands output with
  | input a => simp [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.step, _root_.InfoLossLAR.WorstCase.BooleanExpr.compile, _root_.InfoLossLAR.WorstCase.BooleanExpr.size]
  | constant b =>
    cases b <;> simp [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.step, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.emit, _root_.InfoLossLAR.WorstCase.BooleanExpr.compile, _root_.InfoLossLAR.WorstCase.BooleanExpr.size, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node]
  | negate a ih =>
    rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run_append, ih]
    simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run, List.foldl_cons, List.foldl_nil, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.step, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.emit, _root_.InfoLossLAR.WorstCase.BooleanExpr.compile,
      _root_.InfoLossLAR.WorstCase.BooleanExpr.size, _root_.InfoLossLAR.WorstCase.BooleanExpr.compile_length, List.length_append, List.length_replicate]
    simp [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node, List.map_append, List.replicate_add, List.append_assoc, -List.replicate_append_replicate]
  | xor a b ia ib | and a b ia ib =>
    rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run_append, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run_append, ia, ib]
    simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run, List.foldl_cons, List.foldl_nil, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.step, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.emit, _root_.InfoLossLAR.WorstCase.BooleanExpr.compile,
      _root_.InfoLossLAR.WorstCase.BooleanExpr.size, _root_.InfoLossLAR.WorstCase.BooleanExpr.compile_length, List.length_append, List.length_replicate]
    simp [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node, List.map_append, List.replicate_add, List.append_assoc, -List.replicate_append_replicate, Nat.add_assoc]





end InfoLossLAR.WorstCase.TM2Boolean.RPN

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open Polynomial

 def NodeBound (N : ℕ) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Node) : Prop :=
  x.1.bits.length ≤ N ∧ x.2.1.bits.length ≤ N ∧ x.2.2.bits.length ≤ N

 structure Bounded (N : ℕ) (s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State) : Prop where
  slots : s.1.length ≤ N
  operands : s.2.1.length ≤ N
  nodes : s.2.2.length ≤ N
  refs : ∀ x ∈ s.2.1, x.bits.length ≤ N
  code : ∀ x ∈ s.2.2, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.NodeBound N x

 

 

 

 

 

 

 

 

 

 

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end

section




















































set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.RPN
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

 def CodePoly {α : Type} [Coding α] (f : α → _root_.InfoLossLAR.WorstCase.BooleanExpr) : Prop :=
  Poly (fun a => _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code (f a))

namespace CodePoly
variable {α β : Type} [Coding α] [Coding β]

 

 

 

 

 

 

 

 

 

 

 

 
end CodePoly

 theorem run_codes (es : List _root_.InfoLossLAR.WorstCase.BooleanExpr) (slots : List Unit) (operands : List ℕ) (output : List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Node) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run (es.flatMap _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code) (slots, operands, output) =
      (slots ++ List.replicate (es.map _root_.InfoLossLAR.WorstCase.BooleanExpr.size).sum (),
        (_root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany slots.length es).2.reverse ++ operands,
        output ++ (_root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany slots.length es).1.map _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node) := by
  induction es generalizing slots operands output with
  | nil => simp [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run, _root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany]
  | cons e es ih =>
    simp only [List.flatMap_cons, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run_append, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run_code, ih]
    simp only [List.map_cons, List.sum_cons, _root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany,
      _root_.InfoLossLAR.WorstCase.BooleanExpr.compile_length, List.length_append, List.length_replicate]
    simp [List.map_append, List.replicate_add, List.append_assoc, -List.replicate_append_replicate]

 def compileTokens (tokens : List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Token) (slots : List Unit) : List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Node × List ℕ :=
  let result := _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run tokens (slots, [], [])
  (result.2.2, result.2.1.reverse)

 

 theorem compileTokens_codes (es : List _root_.InfoLossLAR.WorstCase.BooleanExpr) (slots : List Unit) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.compileTokens (es.flatMap _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code) slots =
      ((_root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany slots.length es).1.map _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node,
        (_root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany slots.length es).2) := by
  simp [_root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.compileTokens, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run_codes]

end InfoLossLAR.WorstCase.TM2Boolean.RPN

end

section




















































set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean
open Turing
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RPN
variable {K Λ σ α : Type} [DecidableEq K] [DecidableEq Λ] [DecidableEq σ] [Fintype σ]

/-- A symbolic configuration family with natural cell indices. Only the bounded
restriction is used semantically; the total family admits a single string algorithm. -/
structure CodeFamily (K Λ σ α : Type) where
  label : Option Λ → α → _root_.InfoLossLAR.WorstCase.BooleanExpr
  state : σ → α → _root_.InfoLossLAR.WorstCase.BooleanExpr
  stack : K → Option Bool → α × ℕ → _root_.InfoLossLAR.WorstCase.BooleanExpr

namespace CodeFamily

def restrict (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (a : α) (width : ℕ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width where
  label l := sym.label l a
  state v := sym.state v a
  stack k i b := sym.stack k b (a,i.val)

structure IsPoly [Coding α] (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) : Prop where
  label : ∀ l, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (sym.label l)
  state : ∀ v, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (sym.state v)
  stack : ∀ k b, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.CodePoly (sym.stack k b)

noncomputable def load (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (f : σ → σ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α :=
  {sym with state v a := _root_.InfoLossLAR.WorstCase.BooleanExpr.lookup (fun v' => decide (v = f v')) (fun v' => sym.state v' a)}

noncomputable def push (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (k : K) (f : σ → Bool) : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α :=
  {sym with stack j b x := if j = k then
    if x.2 = 0 then _root_.InfoLossLAR.WorstCase.BooleanExpr.lookup (fun v => decide (b = some (f v))) (fun v => sym.state v x.1)
    else sym.stack k b (x.1, x.2-1)
    else sym.stack j b x}

noncomputable def read (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (k : K) (f : σ → Option Bool → σ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α :=
  {sym with
    state v a := _root_.InfoLossLAR.WorstCase.BooleanExpr.lookup (fun u : σ × Option Bool => decide (v = f u.1 u.2))
      (fun u => .and (sym.state u.1 a) (sym.stack k u.2 (a,0)))}

def pop (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (width : α → ℕ) (k : K) : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α :=
  {sym with stack j b x := if j = k then
    if x.2 + 1 < width x.1 then sym.stack k b (x.1, x.2+1)
    else .constant (decide (b = none))
    else sym.stack j b x}

noncomputable def jump (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (f : σ → Λ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α :=
  {sym with label l a := _root_.InfoLossLAR.WorstCase.BooleanExpr.lookup (fun v => decide (l = some (f v))) (fun v => sym.state v a)}

def halt (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α :=
  {sym with label l _ := .constant (decide (l = none))}

def select (condition : α → _root_.InfoLossLAR.WorstCase.BooleanExpr) (a b : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α where
  label l x := _root_.InfoLossLAR.WorstCase.BooleanExpr.select (condition x) (a.label l x) (b.label l x)
  state v x := _root_.InfoLossLAR.WorstCase.BooleanExpr.select (condition x) (a.state v x) (b.state v x)
  stack k v x := _root_.InfoLossLAR.WorstCase.BooleanExpr.select (condition x.1) (a.stack k v x) (b.stack k v x)

theorem symbolic_ext {width : ℕ} {x y : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width}
    (hl : x.label = y.label) (hs : x.state = y.state) (ht : x.stack = y.stack) : x = y := by
  cases x; cases y; cases hl; cases hs; cases ht; rfl

theorem load_at (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (f : σ → σ) (a : α) (width : ℕ) :
    (sym.load f).restrict a width = (sym.restrict a width).load f := rfl

theorem push_at (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (k : K) (f : σ → Bool) (a : α) (width : ℕ) :
    (sym.push k f).restrict a width = (sym.restrict a width).push k f := rfl

theorem read_at (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (k : K) (f : σ → Option Bool → σ)
    (a : α) (width : ℕ) (hw : 0 < width) :
    (sym.read k f).restrict a width = (sym.restrict a width).read hw k f := rfl

theorem pop_at (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (width : α → ℕ) (k : K) (a : α) :
    (sym.pop width k).restrict a (width a) = (sym.restrict a (width a)).pop k := rfl





theorem select_at (condition : α → _root_.InfoLossLAR.WorstCase.BooleanExpr) (x y : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (a : α) (width : ℕ) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.select condition x y).restrict a width = _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.select (condition a) (x.restrict a width) (y.restrict a width) := rfl

variable [Coding α]















end CodeFamily
end InfoLossLAR.WorstCase.TM2Boolean

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeFamily
open Turing
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RPN
variable {K Λ σ α : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

noncomputable def auxiliaryCode (width : α → ℕ) :
    TM2.Stmt (fun _ : K => Bool) Λ σ → _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α → _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α
  | .push k f q, sym => auxiliaryCode width q (sym.push k f)
  | .peek k f q, sym => auxiliaryCode width q (sym.read k f)
  | .pop k f q, sym => auxiliaryCode width q ((sym.read k f).pop width k)
  | .load f q, sym => auxiliaryCode width q (sym.load f)
  | .branch f q r, sym =>
      _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.select (fun a => _root_.InfoLossLAR.WorstCase.BooleanExpr.lookup f (fun v => sym.state v a))
        (auxiliaryCode width q sym) (auxiliaryCode width r sym)
  | .goto f, sym => sym.jump f
  | .halt, sym => sym.halt

theorem auxiliaryCode_restrict (width : α → ℕ) (a : α) (hw : 0 < width a)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.auxiliaryCode width q sym).restrict a (width a) =
      _root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliary hw q (sym.restrict a (width a)) := by
  induction q generalizing sym with
  | push k f q ih => simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.auxiliaryCode, _root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliary, ih, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.push_at]
  | peek k f q ih => simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.auxiliaryCode, _root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliary, ih, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.read_at _ _ _ _ _ hw]
  | pop k f q ih => simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.auxiliaryCode, _root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliary, ih, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.pop_at, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.read_at _ _ _ _ _ hw]
  | load f q ih => simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.auxiliaryCode, _root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliary, ih, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.load_at]
  | branch f q r iq ir =>
    simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.auxiliaryCode, _root_.InfoLossLAR.WorstCase.TM2Boolean.auxiliary, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.select_at, iq, ir]
    rfl
  | goto f => rfl
  | halt => rfl

noncomputable def multiplexCode {ι : Type} [Fintype ι]
    (control : ι → α → _root_.InfoLossLAR.WorstCase.BooleanExpr) (choices : ι → _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α where
  label l a := _root_.InfoLossLAR.WorstCase.BooleanExpr.multiplex (fun i => control i a) (fun i => (choices i).label l a)
  state v a := _root_.InfoLossLAR.WorstCase.BooleanExpr.multiplex (fun i => control i a) (fun i => (choices i).state v a)
  stack k b a := _root_.InfoLossLAR.WorstCase.BooleanExpr.multiplex (fun i => control i a.1) (fun i => (choices i).stack k b a)

theorem multiplexCode_restrict {ι : Type} [Fintype ι]
    (control : ι → α → _root_.InfoLossLAR.WorstCase.BooleanExpr) (choices : ι → _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (a : α) (width : ℕ) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.multiplexCode control choices).restrict a width =
      _root_.InfoLossLAR.WorstCase.TM2Boolean.multiplex (fun i => control i a) (fun i => (choices i).restrict a width) := rfl

noncomputable def transitionCode (width : α → ℕ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α :=
  _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.multiplexCode sym.label (fun l => l.elim sym (fun l => _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.auxiliaryCode width (program l) sym))

theorem transitionCode_restrict (width : α → ℕ) (a : α) (hw : 0 < width a)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.transitionCode width program sym).restrict a (width a) =
      _root_.InfoLossLAR.WorstCase.TM2Boolean.transition hw program (sym.restrict a (width a)) := by
  rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.transitionCode, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.multiplexCode_restrict]
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.transition
  congr 1
  funext l
  cases l with
  | none => rfl
  | some l => exact _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.auxiliaryCode_restrict width a hw (program l) sym

variable [Coding α]







end InfoLossLAR.WorstCase.TM2Boolean.CodeFamily

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean

 def enumerate {α : Type} {n : ℕ} (e : α ≃ Fin n) : List α := List.ofFn e.symm

 theorem enumerate_cast {α : Type} {n m : ℕ} (e : α ≃ Fin n) (h : n=m) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (e.trans (finCongr h)) = _root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate e := by subst m; rfl

 theorem enumerate_sum {α β : Type} {m n : ℕ} (e : α ≃ Fin m) (f : β ≃ Fin n) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate ((Equiv.sumCongr e f).trans finSumFinEquiv) =
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate e).map Sum.inl ++ (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate f).map Sum.inr := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate
  rw [List.ofFn_add]
  simp only [Equiv.symm_trans, Equiv.sumCongr_symm, Equiv.trans_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, List.map_ofFn, Function.comp_def]
  congr 1
  apply congrArg List.ofFn
  funext i
  change Sum.map e.symm f.symm (finSumFinEquiv.symm (Fin.castAdd n i)) = Sum.inl (e.symm i)
  simp

 theorem enumerate_prod {α β : Type} {m n : ℕ} (e : α ≃ Fin m) (f : β ≃ Fin n) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate ((Equiv.prodCongr e f).trans finProdFinEquiv) =
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate e).flatMap (fun a => (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate f).map (fun b => (a,b))) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate
  rw [List.ofFn_mul]
  rw [List.flatMap_def, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  have hb : j.val+n*i.val < m*n := (finProdFinEquiv (i,j)).isLt
  have hb' : i.val*n+j.val < m*n := by simpa only [Nat.mul_comm, Nat.add_comm] using hb
  have he : (⟨i.val*n+j.val, hb'⟩ : Fin (m*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    change i.val*n+j.val = j.val+n*i.val
    ac_rfl
  rw [he]
  simp

 theorem enumerate_refl (n : ℕ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (Equiv.refl (Fin n)) = List.finRange n := by
  exact List.ofFn_id n

 variable {K Λ σ : Type} [Fintype K] [Fintype Λ] [Fintype σ]

 theorem enumerate_slots (width : ℕ) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ width) =
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (Fintype.equivFin (Option Λ))).map Sum.inl ++
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (Fintype.equivFin σ)).map (fun v => Sum.inr (Sum.inl v)) ++
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (Fintype.equivFin K)).flatMap (fun k =>
        (List.finRange width).flatMap (fun i =>
          (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (Fintype.equivFin (Option Bool))).map
            (fun b => Sum.inr (Sum.inr (k,i,b))))) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv
  rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate_cast, _root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate_sum, _root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate_sum]
  simp only [List.map_append, List.map_map, Function.comp_def, List.append_assoc,
    _root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate_prod, _root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate_refl, List.map_flatMap, List.flatMap_map]

 theorem Symbolic.formulas_enumerate {width : ℕ} (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) :
    sym.formulas = (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ width)).map sym.get := by
  simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.formulas, _root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate, List.map_ofFn, Function.comp_def]

 theorem Symbolic.formulas_slots {width : ℕ} (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width) :
    sym.formulas =
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (Fintype.equivFin (Option Λ))).map sym.label ++
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (Fintype.equivFin σ)).map sym.state ++
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (Fintype.equivFin K)).flatMap (fun k =>
        (List.finRange width).flatMap (fun i =>
          (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (Fintype.equivFin (Option Bool))).map (fun b => sym.stack k i b))) := by
  rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.formulas_enumerate, _root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate_slots]
  simp only [List.map_append, List.map_map, List.map_flatMap, Function.comp_def, _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.get]

end InfoLossLAR.WorstCase.TM2Boolean

end

section




















































set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RPN

 

 theorem finRange_values (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

namespace CodeFamily
variable {K Λ σ α : Type} [Fintype K] [Fintype Λ] [Fintype σ]

noncomputable def codes (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (width : α → List Unit) (a : α) : List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Token :=
  (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (Fintype.equivFin (Option Λ))).flatMap (fun l => _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code (sym.label l a)) ++
  (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (Fintype.equivFin σ)).flatMap (fun v => _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code (sym.state v a)) ++
  (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (Fintype.equivFin K)).flatMap (fun k =>
    (List.range (width a).length).flatMap (fun i =>
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.enumerate (Fintype.equivFin (Option Bool))).flatMap (fun b => _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code (sym.stack k b (a,i)))))

theorem codes_eq (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (width : α → List Unit) (a : α) :
    sym.codes width a = (sym.restrict a (width a).length).formulas.flatMap _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code := by
  rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.formulas_slots]
  simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.codes, List.flatMap_append, List.flatMap_map, List.flatMap_assoc, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.restrict]
  rw [← _root_.InfoLossLAR.WorstCase.TM2Boolean.finRange_values (width a).length]
  simp only [List.flatMap_map]

 

 noncomputable def compile (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (width : α → List Unit)
    (slots : α → List Unit) (a : α) : List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Node × List ℕ := _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.compileTokens (sym.codes width a) (slots a)

 

 theorem compile_eq (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α) (width slots : α → List Unit) (a : α) :
    sym.compile width slots a =
      (((sym.restrict a (width a).length).compiled (slots a).length).1.map _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node,
        ((sym.restrict a (width a).length).compiled (slots a).length).2) := by
  rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.compile, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.codes_eq, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.compileTokens_codes]
  rfl

end CodeFamily
end InfoLossLAR.WorstCase.TM2Boolean

end

section




















































set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RPN
variable {K Λ σ α : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

 theorem slot_label_index (width : ℕ) (l : Option Λ) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ width (.inl l)).val = (Fintype.equivFin (Option Λ) l).val := rfl

 theorem slot_state_index (width : ℕ) (v : σ) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ width (.inr (.inl v))).val =
      Fintype.card (Option Λ) + (Fintype.equivFin σ v).val := rfl

 theorem slot_stack_index (width : ℕ) (k : K) (i : Fin width) (b : Option Bool) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ width (.inr (.inr (k,i,b)))).val =
      Fintype.card (Option Λ) + (Fintype.card σ +
        ((Fintype.equivFin (Option Bool) b).val + Fintype.card (Option Bool)*i.val +
          (width*Fintype.card (Option Bool))*(Fintype.equivFin K k).val)) := rfl

namespace CodeFamily

 def initialCode (input : K) (main : Λ) (initialState : σ) (length : α → ℕ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α where
  label l _ := .constant (decide (l = some main))
  state v _ := .constant (decide (v = initialState))
  stack k b x := if k = input ∧ x.2 < length x.1 then _root_.InfoLossLAR.WorstCase.TM2Boolean.inputCell x.2 b
    else .constant (decide (b = none))

 theorem initialCode_restrict (input : K) (main : Λ) (initialState : σ)
    (length : α → ℕ) (a : α) (width : ℕ) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.initialCode input main initialState length).restrict a width =
      _root_.InfoLossLAR.WorstCase.TM2Boolean.initial input main initialState (length a) width := rfl

 

noncomputable def reboundCode (width : α → ℕ) (refs : α → List ℕ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ α where
  label l a := .input (((refs a)[(Fintype.equivFin (Option Λ) l).val]?).getD 0)
  state v a := .input (((refs a)[Fintype.card (Option Λ)+(Fintype.equivFin σ v).val]?).getD 0)
  stack k b x := .input (((refs x.1)[Fintype.card (Option Λ)+(Fintype.card σ+
    ((Fintype.equivFin (Option Bool) b).val+Fintype.card (Option Bool)*x.2+
      (width x.1*Fintype.card (Option Bool))*(Fintype.equivFin K k).val))]?).getD 0)

 

 theorem reboundCode_get (width : α → ℕ) (refs : α → List ℕ) (a : α) (i : _root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ (width a)) :
    ((_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.reboundCode width refs).restrict a (width a)).get i =
      .input (((refs a)[(_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ (width a) i).val]?).getD 0) := by
  rcases i with l | v | ⟨k,i,b⟩
  · rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.slot_label_index]; rfl
  · rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.slot_state_index]; rfl
  · rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.slot_stack_index]; rfl

 theorem reboundCode_restrict (width : α → ℕ) (refs : α → List ℕ) (a : α)
    (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ (width a)) (start : ℕ) (hr : refs a = (sym.compiled start).2) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.reboundCode width refs).restrict a (width a) = sym.rebound start := by
  have hi : ∀ i : _root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ (width a),
      ((_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.reboundCode width refs).restrict a (width a)).get i = (sym.rebound start).get i := by
    intro i
    rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.reboundCode_get, hr]
    have hlt : (_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ (width a) i).val < (sym.compiled start).2.length := by
      simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.compiled, _root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany_outputs_length, _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.formulas_length]
      exact (_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ (width a) i).isLt
    simp only [List.getElem?_eq_getElem hlt, Option.getD_some, _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.rebound,
      _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.get_ofSlots, _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.output]
  apply _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.symbolic_ext
  · funext l; exact hi (.inl l)
  · funext v; exact hi (.inr (.inl v))
  · funext k i b; exact hi (.inr (.inr (k,i,b)))

end CodeFamily
end InfoLossLAR.WorstCase.TM2Boolean

end

section

















































namespace InfoLossLAR
end InfoLossLAR
namespace InfoLossLAR.WorstCase
end InfoLossLAR.WorstCase
namespace InfoLossLAR.WorstCase.TM2Boolean
end InfoLossLAR.WorstCase.TM2Boolean
namespace InfoLossLAR.WorstCase.TM2Boolean.RPN
end InfoLossLAR.WorstCase.TM2Boolean.RPN


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
open Turing
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RPN
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

abbrev Input := List Unit × _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State

noncomputable def registers : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily K Λ σ _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input :=
  _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.reboundCode (fun x => x.1.length) (fun x => x.2.2.1)

 

 

 

noncomputable def tokens (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input → List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Token :=
  (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.transitionCode (fun x => x.1.length) program _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.registers).codes Prod.fst

 

noncomputable def step (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input) : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input :=
  if x.1.isEmpty then x else
    let result := _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokens program x) (x.2.1, [], x.2.2.2)
    (x.1, result.1, result.2.1.reverse, result.2.2)

 

 @[simp] theorem step_width (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.step program x).1 = x.1 := by unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.step; split <;> rfl

 theorem tokens_eq (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input) (hw : 0 < x.1.length) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokens program x = (_root_.InfoLossLAR.WorstCase.TM2Boolean.transition hw program (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.registers.restrict x x.1.length)).formulas.flatMap _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.code := by
  rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokens, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.codes_eq, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.transitionCode_restrict (fun x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input => x.1.length) x hw program _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.registers]

 noncomputable def tokenBound (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (width : ℕ) : ℕ :=
  (2*_root_.InfoLossLAR.WorstCase.TM2Boolean.transitionBound program 0+1) * Fintype.card (_root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width)

 

 

 

 theorem step_exact (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input)
    (hw : 0 < x.1.length) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.step program x =
      let sym := _root_.InfoLossLAR.WorstCase.TM2Boolean.transition hw program (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.registers.restrict x x.1.length)
      let result := sym.compiled x.2.1.length
      (x.1, x.2.1 ++ List.replicate result.1.length (), result.2, x.2.2.2 ++ result.1.map _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node) := by
  have he : x.1.isEmpty = false := List.isEmpty_eq_false_iff.mpr (List.length_pos_iff.mp hw)
  simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.step, he, Bool.false_eq_true, ↓reduceIte, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokens_eq program x hw, _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.run_codes,
    List.append_nil, List.reverse_reverse, _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.compiled, _root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany_length]

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
open Turing Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RPN
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

noncomputable def iterateCode (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (fuel : List Unit) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input) : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input :=
  fuel.foldl (fun y _ => _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.step program y) x

 @[simp] theorem iterateCode_width (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (fuel : List Unit) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.iterateCode program fuel x).1 = x.1 := by
  induction fuel generalizing x with
  | nil => rfl
  | cons u fuel ih => simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.iterateCode, List.foldl_cons, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.step_width] using ih (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.step program x)

 

noncomputable def tokenRate (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) : ℕ :=
  (2*_root_.InfoLossLAR.WorstCase.TM2Boolean.transitionBound program 0+1)*(Fintype.card Λ+1+Fintype.card σ+Fintype.card K*3)

 

noncomputable def loopBound (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) : Polynomial ℕ :=
  2*X+1+20*(X+3+X*C (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.tokenRate program)*(X+1)+1)^2

 

 

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
open Turing
open RPN
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

noncomputable def view (width : List Unit) (s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State) : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width.length :=
  _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.registers.restrict (width,s) width.length

 theorem view_rebound (width : List Unit) (s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State)
    (sym : _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic K Λ σ width.length) (start : ℕ) (hr : s.2.1 = (sym.compiled start).2) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.view width s = sym.rebound start := by
  have hh := _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.reboundCode_restrict (fun _ : Unit => width.length)
    (fun _ => s.2.1) () sym start hr
  exact hh

noncomputable def innerStep (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (width : List Unit) (s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State) : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State := (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.step program (width,s)).2

 theorem innerStep_spec (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (width : List Unit) (hw : 0 < width.length) (s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State) :
    let sym := _root_.InfoLossLAR.WorstCase.TM2Boolean.transition hw program (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.view width s)
    let result := sym.compiled s.1.length
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.innerStep program width s).1.length = s.1.length+result.1.length ∧
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.innerStep program width s).2.2 = s.2.2 ++ result.1.map _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node ∧
    _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.view width (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.innerStep program width s) = sym.rebound s.1.length := by
  have he := _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.step_exact program (width,s) hw
  have hs := congrArg Prod.snd he
  change _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.innerStep program width s = _ at hs
  dsimp only at hs ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]
    simp only [List.length_append, List.length_replicate, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.view]
  · rw [hs]
    rfl
  · apply _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.view_rebound
    rw [hs]
    rfl

noncomputable def runState (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (width : List Unit) : ℕ → _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State → _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State
  | 0, s => s
  | n+1, s => runState program width n (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.innerStep program width s)

 theorem iterateCode_eq_runState (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (fuel : List Unit) (width : List Unit) (s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.iterateCode program fuel (width,s) = (width, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.runState program width fuel.length s) := by
  induction fuel generalizing s with
  | nil => rfl
  | cons u fuel ih =>
    have he : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.step program (width,s) = (width, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.innerStep program width s) := by
      apply Prod.ext
      · exact _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.step_width program (width,s)
      · rfl
    change _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.iterateCode program fuel (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.step program (width,s)) = _
    rw [he, ih]
    rfl

 theorem runState_spec (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (width : List Unit) (hw : 0 < width.length) (n : ℕ) (s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State) :
    let result := _root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun hw program n s.1.length (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.view width s)
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.runState program width n s).1.length = s.1.length+result.1.length ∧
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.runState program width n s).2.2 = s.2.2 ++ result.1.map _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node ∧
    _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.view width (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.runState program width n s) = result.2 := by
  induction n generalizing s with
  | zero => simp [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.runState, _root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun]
  | succ n ih =>
    obtain ⟨hl, hc, hv⟩ := _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.innerStep_spec program width hw s
    have hh := ih (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.innerStep program width s)
    dsimp only at hl hc hv hh ⊢
    rw [hl, hv] at hh
    rcases hh with ⟨hl', hc', hv'⟩
    refine ⟨?_, ?_, hv'⟩
    · simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.runState, _root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun, List.length_append, Nat.add_assoc] using hl'
    · rw [hc] at hc'
      simpa only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.runState, _root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun, List.map_append, List.append_assoc] using hc'

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end

section


















































set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
open RPN
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

 theorem compileMany_inputs (start : ℕ) (refs : List ℕ) :
    _root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany start (refs.map BooleanExpr.input) = ([],refs) := by
  induction refs with
  | nil => rfl
  | cons i is ih => simpa only [List.map_cons, _root_.InfoLossLAR.WorstCase.BooleanExpr.compileMany, _root_.InfoLossLAR.WorstCase.BooleanExpr.compile,
      List.length_nil, Nat.add_zero, List.nil_append] using congrArg (fun p : List _root_.InfoLossLAR.WorstCase.BooleanOp × List ℕ => (p.1,i::p.2)) ih

 theorem view_formulas (width : List Unit) (s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.view (K := K) (Λ := Λ) (σ := σ) width s).formulas =
      (List.ofFn (fun i : Fin (Fintype.card (_root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width.length)) =>
        (s.2.1[i.val]?).getD 0)).map BooleanExpr.input := by
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change ((_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.reboundCode (fun x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input => x.1.length) (fun x => x.2.2.1)).restrict
    (width,s) width.length).get ((_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ width.length).symm i) = _
  rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.reboundCode_get]
  simp only [Equiv.apply_symm_apply, Function.comp_apply]

 theorem view_compiled (width : List Unit) (s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State) (start : ℕ) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.view (K := K) (Λ := Λ) (σ := σ) width s).compiled start =
      ([],List.ofFn (fun i : Fin (Fintype.card (_root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width.length)) =>
        (s.2.1[i.val]?).getD 0)) := by
  rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.compiled, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.view_formulas, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.compileMany_inputs]

 theorem view_output (width : List Unit) (s : _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.State) (start : ℕ) (i : _root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ width.length) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.view width s).output start i = (s.2.1[(_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ width.length i).val]?).getD 0 := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.Symbolic.output
  simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.view_compiled, List.getElem_ofFn]

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end

section




















































set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator
open Turing
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RPN
variable {K Λ σ : Type} [DecidableEq K] [Fintype K]
  [DecidableEq Λ] [Fintype Λ] [DecidableEq σ] [Fintype σ]

/-- Unary input length, stack capacity, and step budget. -/
abbrev Request := List Unit × (List Unit × List Unit)

noncomputable def initialResult (input : K) (main : Λ) (initialState : σ) : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Request → List _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.Node × List ℕ :=
  (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.initialCode input main initialState (fun x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Request => x.1.length)).compile
    (fun x => x.2.1) Prod.fst

 

 theorem initialResult_eq (input : K) (main : Λ) (initialState : σ) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Request) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialResult input main initialState x =
      (((_root_.InfoLossLAR.WorstCase.TM2Boolean.initial input main initialState x.1.length x.2.1.length).compiled x.1.length).1.map _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node,
        ((_root_.InfoLossLAR.WorstCase.TM2Boolean.initial input main initialState x.1.length x.2.1.length).compiled x.1.length).2) := by
  rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialResult, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.compile_eq, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeFamily.initialCode_restrict]

noncomputable def initialInput (input : K) (main : Λ) (initialState : σ) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Request) : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input :=
  let result := _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialResult input main initialState x
  (x.2.1, x.1 ++ result.1.map (fun _ => ()), result.2, result.1)

 

 @[simp] theorem initialInput_width (input : K) (main : Λ) (initialState : σ) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Request) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialInput input main initialState x).1 = x.2.1 := rfl

 theorem initialInput_spec (input : K) (main : Λ) (initialState : σ) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Request) :
    let sym := _root_.InfoLossLAR.WorstCase.TM2Boolean.initial input main initialState x.1.length x.2.1.length
    let result := sym.compiled x.1.length
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialInput input main initialState x).2.1.length = x.1.length+result.1.length ∧
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialInput input main initialState x).2.2.2 = result.1.map _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node ∧
    _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.view x.2.1 (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialInput input main initialState x).2 = sym.rebound x.1.length := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialInput, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialResult_eq, List.length_append, List.length_map]
  · simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialInput, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialResult_eq]
  · apply _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.view_rebound
    simp only [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialInput, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialResult_eq]

noncomputable def generate (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Request) : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Input :=
  _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.iterateCode program x.2.2 (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialInput input main initialState x)

 

 theorem generate_runState (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Request) :
    _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.generate program input main initialState x =
      (x.2.1,_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.runState program x.2.1 x.2.2.length (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialInput input main initialState x).2) := by
  unfold _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.generate
  have he : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialInput input main initialState x =
      (x.2.1,(_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialInput input main initialState x).2) := rfl
  rw [he, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.iterateCode_eq_runState]

 theorem generate_spec (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Request) (hw : 0 < x.2.1.length) :
    let first := (_root_.InfoLossLAR.WorstCase.TM2Boolean.initial input main initialState x.1.length x.2.1.length).compiled x.1.length
    let result := _root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun hw program x.2.2.length (x.1.length+first.1.length)
      ((_root_.InfoLossLAR.WorstCase.TM2Boolean.initial input main initialState x.1.length x.2.1.length).rebound x.1.length)
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.generate program input main initialState x).2.1.length = x.1.length+first.1.length+result.1.length ∧
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.generate program input main initialState x).2.2.2 = (first.1++result.1).map _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node ∧
    _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.view x.2.1 (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.generate program input main initialState x).2 = result.2 := by
  obtain ⟨hl,hc,hv⟩ := _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialInput_spec input main initialState x
  have hh := _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.runState_spec program x.2.1 hw x.2.2.length (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.initialInput input main initialState x).2
  dsimp only at hl hc hv hh ⊢
  rw [hl,hv] at hh
  rw [_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.generate_runState]
  rcases hh with ⟨hl',hc',hv'⟩
  refine ⟨hl',?_,hv'⟩
  rw [hc] at hc'
  simpa only [List.map_append] using hc'

 theorem generate_machineProgram (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (input : K) (main : Λ) (initialState : σ) (x : _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.Request) (hw : 0 < x.2.1.length) :
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.generate program input main initialState x).2.2.2 =
      (_root_.InfoLossLAR.WorstCase.TM2Boolean.machineProgram hw program input main initialState x.2.2.length x.1.length).ops.map _root_.InfoLossLAR.WorstCase.TM2Boolean.RPN.node ∧
    (_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.generate program input main initialState x).2.1.length =
      x.1.length+(_root_.InfoLossLAR.WorstCase.TM2Boolean.machineProgram hw program input main initialState x.2.2.length x.1.length).ops.length ∧
    ∀ i : _root_.InfoLossLAR.WorstCase.TM2Boolean.Slot K Λ σ x.2.1.length,
      ((_root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.generate program input main initialState x).2.2.1[(_root_.InfoLossLAR.WorstCase.TM2Boolean.slotEquiv K Λ σ x.2.1.length i).val]?).getD 0 =
        (_root_.InfoLossLAR.WorstCase.TM2Boolean.machineProgram hw program input main initialState x.2.2.length x.1.length).output i := by
  obtain ⟨hl,hc,hv⟩ := _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.generate_spec program input main initialState x hw
  let first := (_root_.InfoLossLAR.WorstCase.TM2Boolean.initial input main initialState x.1.length x.2.1.length).compiled x.1.length
  let result := _root_.InfoLossLAR.WorstCase.TM2Boolean.compileRun hw program x.2.2.length (x.1.length+first.1.length)
      ((_root_.InfoLossLAR.WorstCase.TM2Boolean.initial input main initialState x.1.length x.2.1.length).rebound x.1.length)
  let lastStart := x.1.length+first.1.length+result.1.length
  have hz : (result.2.compiled lastStart).1 = [] := by
    rw [← hv, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.view_compiled]
  have ho : (_root_.InfoLossLAR.WorstCase.TM2Boolean.machineProgram hw program input main initialState x.2.2.length x.1.length).ops = first.1++result.1 := by
    change first.1++result.1++(result.2.compiled lastStart).1 = _
    rw [hz, List.append_nil]
  refine ⟨?_, ?_, ?_⟩
  · rw [ho]; exact hc
  · rw [ho, List.length_append]
    simpa only [Nat.add_assoc] using hl
  · intro i
    change _ = result.2.output lastStart i
    rw [← hv, _root_.InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator.view_output]

end InfoLossLAR.WorstCase.TM2Boolean.CodeGenerator

end


