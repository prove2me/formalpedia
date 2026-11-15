-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_ReverseCompiler
-- name    : QMAPerfectCompleteness_Proof_ReverseCompiler
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:53:21.626806+00:00
-- url     : https://prove2.me/theorems/de32c5b0-f850-4d5b-944d-8ce6abee7d77
-- title:
--   Exact Hadamard–Toffoli-to-HP verifier compiler
-- statement:
--   Defines the semantic, raw, and serialized compiler replacing each Toffoli by the literal seventeen-gate H/controlled-P synthesis and keeping Hadamards unchanged. No extra wires are introduced. Erasure and encoding identities ensure that the total executable code transformation agrees with the semantic verifier compiler on every valid input.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/ReverseCompiler.lean, lines 11–185.

/- Generated from Solutions.ReverseCompiler by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_HPToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding



/-! Exact HT-to-HP compilation without additional wires. Each Toffoli is replaced by
its literal seventeen-gate H/controlled-P synthesis. -/
open Matrix
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.ReverseCompiler
open HPToffoli ReversibleGadgets

noncomputable def compileInstr {n : ℕ} (i : Instr gatesHT n) : List (Instr gatesHP n) := by
  by_cases h0 : i.gate.val = 0
  · have hg : i.gate = (⟨0,by decide⟩ : Fin gatesHT.length) := Fin.ext h0
    let w : Fin (gatesHT.get i.gate).arity := ⟨0,by rw [hg]; decide⟩
    exact [hAt (i.targets w)]
  · have hg : i.gate = (⟨1,by decide⟩ : Fin gatesHT.length) := by
      apply Fin.ext
      change i.gate.val = 1
      have hi := i.gate.isLt
      change i.gate.val < 2 at hi
      omega
    let e : Fin 3 ↪ Fin n := (finCongr
      (show 3 = (gatesHT.get i.gate).arity by rw [hg]; rfl)).toEmbedding.trans i.targets
    exact toffoli.map (Instr.mapWires e)

noncomputable def compileGates {n : ℕ} (gs : List (Instr gatesHT n)) : List (Instr gatesHP n) :=
  gs.flatMap compileInstr

noncomputable def compileVerifier (V : Verifier gatesHT) : Verifier gatesHP where
  proofQubits := V.proofQubits
  ancillaQubits := V.ancillaQubits
  gates := compileGates V.gates
  output := V.output


lemma compileInstr_Toffoli {n : ℕ} (e : Fin 3 ↪ Fin n) :
    compileInstr (⟨⟨1,by decide⟩,e⟩ : Instr gatesHT n) = toffoli.map (Instr.mapWires e) := rfl























/-- Literal numerical gate/address table, independent of complex gate matrices. -/
def toffoliTags : List RawEncoding.Instruction :=
  [⟨0,[2]⟩,
   ⟨1,[0,2]⟩,⟨1,[0,2]⟩,⟨1,[0,2]⟩,
   ⟨1,[1,2]⟩,⟨1,[1,2]⟩,⟨1,[1,2]⟩,
   ⟨0,[1]⟩,⟨1,[0,1]⟩,⟨1,[0,1]⟩,⟨0,[1]⟩,
   ⟨1,[1,2]⟩,
   ⟨0,[1]⟩,⟨1,[0,1]⟩,⟨1,[0,1]⟩,⟨0,[1]⟩,
   ⟨0,[2]⟩]

def placeTags (f : ℕ → ℕ) (gs : List RawEncoding.Instruction) : List RawEncoding.Instruction :=
  gs.map fun i => ⟨i.gate,i.wires.map f⟩

def compileRawInstr : RawEncoding.Instruction → List RawEncoding.Instruction
  | ⟨0,[w]⟩ => [⟨0,[w]⟩]
  | ⟨1,[a,b,c]⟩ => placeTags (fun j => if j=0 then a else if j=1 then b else c) toffoliTags
  | _ => []

def compileRaw (V : RawEncoding.Circuit) : RawEncoding.Circuit :=
  ⟨V.proofQubits,V.ancillaQubits,V.output,V.gates.flatMap compileRawInstr⟩

lemma toffoli_erase : toffoli.map RawEncoding.eraseInstr = toffoliTags := rfl

lemma erase_mapGates {r n : ℕ} {G : GateSet} (e : Fin r ↪ Fin n) (f : ℕ → ℕ)
    (he : ∀ j, (e j).val = f j.val) (gs : List (Instr G r)) :
    (gs.map (Instr.mapWires e)).map RawEncoding.eraseInstr =
      placeTags f (gs.map RawEncoding.eraseInstr) := by
  simp only [placeTags,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro i _
  simp only [RawEncoding.eraseInstr,Instr.mapWires,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext a
  exact he (i.targets a)

theorem compileInstr_erase {n : ℕ} (i : Instr gatesHT n) :
    (compileInstr i).map RawEncoding.eraseInstr = compileRawInstr (RawEncoding.eraseInstr i) := by
  rcases i with ⟨g,t⟩
  fin_cases g
  · rfl
  · change Fin 3 ↪ Fin n at t
    rw [compileInstr_Toffoli,erase_mapGates t
      (fun j => if j=0 then (t 0).val else if j=1 then (t 1).val else (t 2).val)
      (by intro j; fin_cases j <;> rfl),toffoli_erase]
    rfl

theorem compileRaw_erase (V : Verifier gatesHT) :
    compileRaw (RawEncoding.eraseVerifier V) = RawEncoding.eraseVerifier (compileVerifier V) := by
  simp only [compileRaw,RawEncoding.eraseVerifier,compileVerifier,
    compileGates,List.flatMap_map,List.map_flatMap]
  congr 1
  apply List.flatMap_congr
  intro i _
  exact (compileInstr_erase i).symm

/-- A total executable compiler on the actual unary circuit serialization. -/
def executableCompile (s : List Bool) : List Bool :=
  RawEncoding.compile RawEncoding.htTable compileRaw ⟨0,1,0,[]⟩ s

theorem executableCompile_encode (V : Verifier gatesHT) :
    executableCompile V.encode = (compileVerifier V).encode := by
  exact RawEncoding.compile_encode RawEncoding.htTable RawEncoding.htTable_correct _ _ _ compileRaw_erase V

end QMAPerfectCompleteness.Main.ReverseCompiler


