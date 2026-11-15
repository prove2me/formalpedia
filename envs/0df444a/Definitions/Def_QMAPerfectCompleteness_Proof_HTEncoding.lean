-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_HTEncoding
-- name    : QMAPerfectCompleteness_Proof_HTEncoding
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:52:34.075192+00:00
-- url     : https://prove2.me/theorems/a10c1bc6-f124-40c1-9e79-a035bb730c61
-- title:
--   Executable encoding of the Hadamard–Toffoli compiler
-- statement:
--   Defines natural-number gate/address tables and the total raw and serialized G₂-to-HT compiler. Erasing finite wire indices from the semantic gadgets produces exactly these tables. On valid verifier encodings the executable compiler returns precisely the semantic compiled verifier code; malformed codes use a fixed fallback.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/HTEncoding.lean, lines 7–92.

/- Generated from Solutions.HTEncoding by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding



namespace QMAPerfectCompleteness.Main.HTCompiler
open HadamardToffoli

/-- Numeric instruction/address tables; invalid source tags are mapped to no instructions. -/
def quarterTags : List RawEncoding.Instruction :=
  [⟨0,[0]⟩,⟨0,[3]⟩,⟨1,[1,2,0]⟩,⟨0,[0]⟩,⟨0,[3]⟩,⟨1,[1,2,0]⟩]
def czTags : List RawEncoding.Instruction := quarterTags ++ quarterTags
def cnotTags : List RawEncoding.Instruction := [⟨0,[2]⟩] ++ czTags ++ [⟨0,[2]⟩]
def xTags : List RawEncoding.Instruction := [⟨0,[1]⟩] ++ cnotTags ++ czTags ++ cnotTags ++ [⟨0,[1]⟩]

def placeTags (e : ℕ → ℕ) (is : List RawEncoding.Instruction) : List RawEncoding.Instruction :=
  is.map fun i => ⟨i.gate,i.wires.map e⟩

def compileRawInstr (n : ℕ) : RawEncoding.Instruction → List RawEncoding.Instruction
  | ⟨0,[w]⟩ => placeTags (fun i => if i=0 then n+1 else if i=1 then w else if i=2 then n else n+2) xTags
  | ⟨1,[c,t]⟩ => placeTags (fun i => if i=0 then n else if i=1 then c else if i=2 then t else n+1) cnotTags
  | ⟨2,[a,b,c]⟩ => [⟨1,[a,b,c]⟩]
  | ⟨3,[a,b]⟩ => [⟨0,[a]⟩,⟨0,[b]⟩]
  | _ => []

def compileRaw (V : RawEncoding.Circuit) : RawEncoding.Circuit :=
  ⟨V.proofQubits,V.ancillaQubits+3,V.output,
    V.gates.flatMap (compileRawInstr (V.proofQubits+V.ancillaQubits))⟩



theorem controlledNot_erase : controlledNot.map RawEncoding.eraseInstr = cnotTags := by rfl
theorem bitFlipClean_erase : bitFlipClean.map RawEncoding.eraseInstr = xTags := by rfl

lemma erase_mapWires {r n : ℕ} {G : GateSet} (e : Fin r ↪ Fin n) (f : ℕ → ℕ)
    (he : ∀ j, (e j).val = f j.val) (i : Instr G r) :
    RawEncoding.eraseInstr (Instr.mapWires e i) =
      ⟨(RawEncoding.eraseInstr i).gate,(RawEncoding.eraseInstr i).wires.map f⟩ := by
  simp only [RawEncoding.eraseInstr, Instr.mapWires, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext a
  exact he (i.targets a)

lemma erase_mapGates {r n : ℕ} {G : GateSet} (e : Fin r ↪ Fin n) (f : ℕ → ℕ)
    (he : ∀ j, (e j).val = f j.val) (gs : List (Instr G r)) :
    (gs.map (Instr.mapWires e)).map RawEncoding.eraseInstr =
      placeTags f (gs.map RawEncoding.eraseInstr) := by
  simp only [placeTags, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i _
  exact erase_mapWires e f he i

theorem compileInstr_erase {n : ℕ} (i : Instr gatesG2 n) :
    (compileInstr i).map RawEncoding.eraseInstr = compileRawInstr n (RawEncoding.eraseInstr i) := by
  rcases i with ⟨g,t⟩
  fin_cases g
  · change Fin 1 ↪ Fin n at t
    change (bitFlipClean.map (Instr.mapWires (xPlacement (t 0)))).map RawEncoding.eraseInstr = _
    rw [erase_mapGates (xPlacement (t 0))
      (fun i => if i=0 then n+1 else if i=1 then (t 0).val else if i=2 then n else n+2)
      (by intro j; fin_cases j <;> rfl), bitFlipClean_erase]
    rfl
  · change Fin 2 ↪ Fin n at t
    change (controlledNot.map (Instr.mapWires (cnotPlacement t))).map RawEncoding.eraseInstr = _
    rw [erase_mapGates (cnotPlacement t)
      (fun i => if i=0 then n else if i=1 then (t 0).val else if i=2 then (t 1).val else n+1)
      (by intro j; fin_cases j <;> rfl), controlledNot_erase]
    rfl
  · rfl
  · rfl

theorem compileRaw_erase (V : Verifier gatesG2) :
    compileRaw (RawEncoding.eraseVerifier V) = RawEncoding.eraseVerifier (compileVerifier V) := by
  simp only [compileRaw, RawEncoding.eraseVerifier, compileVerifier, List.flatMap_map]
  congr 1
  have he : ∀ j : Fin (V.proofQubits+V.ancillaQubits+3),
      ((finCongr (Nat.add_assoc V.proofQubits V.ancillaQubits 3)).toEmbedding j).val = id j.val := by intro j; rfl
  rw [erase_mapGates _ id he]
  have hid (gs : List RawEncoding.Instruction) : placeTags id gs = gs := by
    simp [placeTags, List.map_id]
  rw [hid]
  simp only [compileGates, List.map_flatMap]
  apply List.flatMap_congr
  intro i _
  exact (compileInstr_erase i).symm

/-- Fully executable string compiler, including malformed-input fallback. -/
def executableCompile (s : List Bool) : List Bool :=
  RawEncoding.compile RawEncoding.g2Table compileRaw ⟨0,1,0,[]⟩ s

theorem executableCompile_encode (V : Verifier gatesG2) :
    executableCompile V.encode = (compileVerifier V).encode := by
  exact RawEncoding.compile_encode RawEncoding.g2Table RawEncoding.g2Table_correct _ _ _ compileRaw_erase V

end QMAPerfectCompleteness.Main.HTCompiler


