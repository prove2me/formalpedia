-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
-- name    : QMAPerfectCompleteness_Proof_RawCircuitEncoding
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:46:43.648986+00:00
-- url     : https://prove2.me/theorems/59ece227-8ad4-4a3b-a573-032c8caac5ae
-- title:
--   Executable unary circuit syntax and parsing
-- statement:
--   Defines natural-number gate tags, finite wire lists, circuit records and their unary encodings. Fixed arity tables drive validated parsers, and round-trip and erasure identities connect total raw compilers with canonical typed-verifier codes.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RawCircuitEncoding.lean, retained declaration span lines 9–118.

/- Generated from Solutions.RawCircuitEncoding by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding



/-! Executable circuit syntax and unary parsers. Exact complex matrices never occur in this
layer: the compiler reads a fixed natural-number arity table and emits gate/address lists. -/
namespace QMAPerfectCompleteness.Main.RawEncoding
open QAlgorithms.Complexity (Str encNat)
open Encoding

structure Instruction where
  gate : ℕ
  wires : List ℕ
  deriving DecidableEq, Repr

structure Circuit where
  proofQubits : ℕ
  ancillaQubits : ℕ
  output : ℕ
  gates : List Instruction
  deriving DecidableEq, Repr

def Instruction.encode (i : Instruction) : Str := encNat i.gate ++ i.wires.flatMap encNat

def Circuit.encode (V : Circuit) : Str := encNat V.proofQubits ++ encNat V.ancillaQubits ++
  encNat V.output ++ encNat V.gates.length ++ V.gates.flatMap Instruction.encode

def eraseInstr {G : GateSet} {n : ℕ} (i : Instr G n) : Instruction :=
  ⟨i.gate.val, List.ofFn fun a => (i.targets a).val⟩

def eraseVerifier {G : GateSet} (V : Verifier G) : Circuit :=
  ⟨V.proofQubits, V.ancillaQubits, V.output.val, V.gates.map eraseInstr⟩

@[simp] theorem eraseInstr_encode {G : GateSet} {n : ℕ} (i : Instr G n) :
    (eraseInstr i).encode = i.encode := by
  simp [eraseInstr, Instruction.encode, Instr.encode, List.flatMap_def, List.map_ofFn, Function.comp_def]

@[simp] theorem eraseVerifier_encode {G : GateSet} (V : Verifier G) :
    (eraseVerifier V).encode = V.encode := by
  simp [eraseVerifier, Circuit.encode, Verifier.encode, encodeGates, List.flatMap_map]

/-- A finite natural-number table completely determines the parser's allowed gate shapes. -/
def CorrectTable (table : List ℕ) (G : GateSet) : Prop :=
  ∀ g : Fin G.length, table[g.val]? = some (G.get g).arity

def hpTable : List ℕ := [1,2]
def g2Table : List ℕ := [1,2,3,2]
def htTable : List ℕ := [1,3]

@[simp] theorem hpTable_correct : CorrectTable hpTable gatesHP := by intro g; fin_cases g <;> rfl
@[simp] theorem g2Table_correct : CorrectTable g2Table gatesG2 := by intro g; fin_cases g <;> rfl
@[simp] theorem htTable_correct : CorrectTable htTable gatesHT := by intro g; fin_cases g <;> rfl

def parseInstruction (table : List ℕ) (n : ℕ) (s : Str) : Option (Instruction × Str) := do
  let (g, s') ← parseNat s
  let r ← table[g]?
  let (t, tail) ← parseWires n r s'
  if Function.Injective t then
    pure (⟨g, List.ofFn fun a => (t a).val⟩, tail)
  else none

@[simp] theorem parseInstruction_encode {G : GateSet} {n : ℕ} (table : List ℕ)
    (ht : CorrectTable table G) (i : Instr G n) (tail : Str) :
    parseInstruction table n (i.encode ++ tail) = some (eraseInstr i, tail) := by
  have hw := parseWires_encode (G.get i.gate).arity i.targets tail
  simp only [wireCode, List.get_eq_getElem] at hw
  simp [parseInstruction, Instr.encode, List.append_assoc, ht i.gate, hw,
    i.targets.injective, eraseInstr]

def parseGateBody (table : List ℕ) (n : ℕ) : ℕ → Str → Option (List Instruction × Str)
  | 0, s => some ([],s)
  | k+1, s => do
    let (i,s') ← parseInstruction table n s
    let (is,tail) ← parseGateBody table n k s'
    pure (i::is,tail)

@[simp] theorem parseGateBody_encode {G : GateSet} {n : ℕ} (table : List ℕ)
    (ht : CorrectTable table G) (gs : List (Instr G n)) (tail : Str) :
    parseGateBody table n gs.length (gs.flatMap Instr.encode ++ tail) =
      some (gs.map eraseInstr,tail) := by
  induction gs with
  | nil => rfl
  | cons i gs ih => simp [parseGateBody, List.append_assoc, parseInstruction_encode table ht, ih]

def parseCircuit (table : List ℕ) (s : Str) : Option (Circuit × Str) := do
  let (m,s') ← parseNat s
  let (a,s'') ← parseNat s'
  let (o,s''') ← parseNat s''
  let (g,s'''') ← parseNat s'''
  if o < m+a then
    let (gs,tail) ← parseGateBody table (m+a) g s''''
    pure (⟨m,a,o,gs⟩,tail)
  else none

@[simp] theorem parseCircuit_encode {G : GateSet} (table : List ℕ) (ht : CorrectTable table G)
    (V : Verifier G) (tail : Str) :
    parseCircuit table (V.encode ++ tail) = some (eraseVerifier V,tail) := by
  simp [parseCircuit, Verifier.encode, encodeGates, List.append_assoc,
    parseGateBody_encode table ht, V.output.isLt, eraseVerifier]

def decodeCircuit (table : List ℕ) (s : Str) : Option Circuit := do
  let (V,tail) ← parseCircuit table s
  if tail = [] then some V else none

@[simp] theorem decodeCircuit_encode {G : GateSet} (table : List ℕ) (ht : CorrectTable table G)
    (V : Verifier G) : decodeCircuit table V.encode = some (eraseVerifier V) := by
  have h := parseCircuit_encode table ht V []
  simp only [List.append_nil] at h
  simp [decodeCircuit,h]

/-- A total, executable compiler wrapper with an explicit fixed fallback code. -/
def compile (sourceTable : List ℕ) (transform : Circuit → Circuit) (fallback : Circuit) (s : Str) : Str :=
  ((decodeCircuit sourceTable s).map transform |>.getD fallback).encode

theorem compile_encode {G H : GateSet} (table : List ℕ) (ht : CorrectTable table G)
    (transform : Circuit → Circuit) (fallback : Circuit)
    (semantic : Verifier G → Verifier H)
    (htransform : ∀ V, transform (eraseVerifier V) = eraseVerifier (semantic V))
    (V : Verifier G) : compile table transform fallback V.encode = (semantic V).encode := by
  simp [compile, decodeCircuit_encode table ht, htransform]

end QMAPerfectCompleteness.Main.RawEncoding


