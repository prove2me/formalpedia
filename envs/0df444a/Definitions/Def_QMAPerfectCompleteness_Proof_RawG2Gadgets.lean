-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RawG2Gadgets
-- name    : QMAPerfectCompleteness_Proof_RawG2Gadgets
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:54:36.734883+00:00
-- url     : https://prove2.me/theorems/e17a3167-387d-4616-8563-796b53291452
-- title:
--   Raw G2 gates and clean control templates
-- statement:
--   Defines raw X, controlled-NOT, Toffoli and paired-Hadamard instructions, together with placement and compute-use-uncompute templates. The control layouts and erasure maps provide the executable counterpart of the typed reversible gate constructions.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RawG2Gadgets.lean, retained declaration span lines 11–114.

/- Generated from Solutions.RawG2Gadgets by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding



/-! Executable G₂ instruction templates. Matrices and circuit-proof data never occur here. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QMAPerfectCompleteness.Main.RawG2
open RawEncoding ReversibleGadgets ControlCircuits EqualityCircuits

def x (a : ℕ) : Instruction := ⟨0,[a]⟩
def cn (a b : ℕ) : Instruction := ⟨1,[a,b]⟩
def tof (a b c : ℕ) : Instruction := ⟨2,[a,b,c]⟩
def hh (a b : ℕ) : Instruction := ⟨3,[a,b]⟩

def place (f : ℕ → ℕ) (gs : List Instruction) : List Instruction :=
  gs.map fun i=>⟨i.gate,i.wires.map f⟩










inductive Command where
  | flip (target : ℕ)
  | copy (source target : ℕ)
  | conj (left right target : ℕ)
  deriving DecidableEq, Repr

def compileCommand : Command → Instruction
  | .flip t => x t
  | .copy a t => cn a t
  | .conj a b t => if a=b then cn a t else tof a b t

def eraseCommand {n : ℕ} : BooleanCircuits.Command n → Command
  | .flip t => .flip t.val
  | .copy a t _ => .copy a.val t.val
  | .conj a b t _ _ => .conj a.val b.val t.val

def compile (p : List Command) : List Instruction := p.map compileCommand





structure AndLayout (r : ℕ) where
  controls : Fin r → ℕ
  flags : Fin (r+1) → ℕ

def eraseAnd {r n : ℕ} (L : ControlCircuits.AndLayout r n) : AndLayout r :=
  ⟨fun j=>(L.controls j).val,fun j=>(L.flags j).val⟩

def andGates {r : ℕ} (L : AndLayout r) : List Instruction :=
  [x (L.flags 0)] ++ (List.finRange r).map (fun j=>tof (L.flags j.castSucc) (L.controls j) (L.flags j.succ))

def computeUseUncompute (a b : List Instruction) := a++b++a.reverse

def multiControlledX {r : ℕ} (L : AndLayout r) (target : ℕ) : List Instruction :=
  computeUseUncompute (andGates L) [cn (L.flags (Fin.last r)) target]





def normalizePrefix {r : ℕ} (L : AndLayout r) (p : Fin r → Bool) :
    (t : ℕ) → t≤r → List Instruction
  | 0,_ => []
  | t+1,ht => normalizePrefix L p t (by omega) ++
      if p ⟨t,by omega⟩ then [] else [x (L.controls ⟨t,by omega⟩)]

def normalize {r : ℕ} (L : AndLayout r) (p : Fin r → Bool) := normalizePrefix L p r le_rfl

def patternControlledX {r : ℕ} (L : AndLayout r) (p : Fin r → Bool) (target : ℕ) : List Instruction :=
  computeUseUncompute (normalize L p) (multiControlledX L target)







end QMAPerfectCompleteness.Main.RawG2


