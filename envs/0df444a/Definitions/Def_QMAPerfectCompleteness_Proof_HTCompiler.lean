-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_HTCompiler
-- name    : QMAPerfectCompleteness_Proof_HTCompiler
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:51:27.85025+00:00
-- url     : https://prove2.me/theorems/3a1cd952-d676-4d04-b3aa-535885e94be0
-- title:
--   Exact G₂-to-Hadamard–Toffoli verifier construction
-- statement:
--   Defines the instruction and verifier compiler from G₂ to Hadamard and Toffoli gates. Three shared clean ancillary wires support the X and CNOT gadgets, paired Hadamards are expanded directly, and source proof wires remain unchanged. Explicit injective placements keep all gadget wires distinct.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/HTCompiler.lean, lines 10–84.

/- Generated from Solutions.HTCompiler by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding



/-! Literal constant-overhead G₂-to-HT compilation. Three global clean ancillary wires suffice
for the finite X/CNOT gadgets; the semantic clean-workspace proof is developed separately. -/
namespace QMAPerfectCompleteness.Main.HTCompiler
open HadamardToffoli

def dataEmbedding (n : ℕ) : Fin n ↪ Fin (n+3) :=
  ⟨Fin.castAdd 3, by intro i j h; exact Fin.ext (congrArg (fun w : Fin (n+3) => w.val) h)⟩



def xPlacement {n : ℕ} (w : Fin n) : Fin 4 ↪ Fin (n+3) :=
  ⟨fun j => ⟨(![n+1,w.val,n,n+2] : Fin 4 → ℕ) j, by
      have hw := w.isLt
      fin_cases j <;> simp <;> omega⟩, by
    intro i j hij
    have hw := w.isLt
    have he : (![n+1,w.val,n,n+2] : Fin 4 → ℕ) i =
        (![n+1,w.val,n,n+2] : Fin 4 → ℕ) j := congrArg Fin.val hij
    fin_cases i <;> fin_cases j <;> simp_all <;> omega⟩

def cnotPlacement {n : ℕ} (e : Fin 2 ↪ Fin n) : Fin 4 ↪ Fin (n+3) :=
  ⟨fun j => ⟨(![n,(e 0).val,(e 1).val,n+1] : Fin 4 → ℕ) j, by
      have h0 := (e 0).isLt
      have h1 := (e 1).isLt
      fin_cases j <;> simp <;> omega⟩, by
    intro i j hij
    have h0 := (e 0).isLt
    have h1 := (e 1).isLt
    have hne : (e 0).val ≠ (e 1).val := by intro h; have := e.injective (Fin.ext h); simp at this
    have he : (![n,(e 0).val,(e 1).val,n+1] : Fin 4 → ℕ) i =
        (![n,(e 0).val,(e 1).val,n+1] : Fin 4 → ℕ) j := congrArg Fin.val hij
    fin_cases i <;> fin_cases j <;> simp_all <;> omega⟩

noncomputable def compileInstr {n : ℕ} (i : Instr gatesG2 n) : List (Instr gatesHT (n+3)) := by
  by_cases h0 : i.gate.val = 0
  · have hg : i.gate = (⟨0,by decide⟩ : Fin gatesG2.length) := Fin.ext h0
    let w : Fin (gatesG2.get i.gate).arity := ⟨0,by rw [hg]; decide⟩
    exact bitFlipClean.map (Instr.mapWires (xPlacement (i.targets w)))
  · by_cases h1 : i.gate.val = 1
    · have hg : i.gate = (⟨1,by decide⟩ : Fin gatesG2.length) := Fin.ext h1
      let e : Fin 2 ↪ Fin n := (finCongr
        (show 2 = (gatesG2.get i.gate).arity by rw [hg]; rfl)).toEmbedding.trans i.targets
      exact controlledNot.map (Instr.mapWires (cnotPlacement e))
    · by_cases h2 : i.gate.val = 2
      · have hg : i.gate = (⟨2,by decide⟩ : Fin gatesG2.length) := Fin.ext h2
        let e : Fin 3 ↪ Fin n := (finCongr
          (show 3 = (gatesG2.get i.gate).arity by rw [hg]; rfl)).toEmbedding.trans i.targets
        exact [tAt (e.trans (dataEmbedding n))]
      · have hg : i.gate = (⟨3,by decide⟩ : Fin gatesG2.length) := by
          apply Fin.ext
          change i.gate.val = 3
          have hi := i.gate.isLt
          change i.gate.val < 4 at hi
          omega
        let e : Fin 2 ↪ Fin n := (finCongr
          (show 2 = (gatesG2.get i.gate).arity by rw [hg]; rfl)).toEmbedding.trans i.targets
        exact [hAt (dataEmbedding n (e 0)),hAt (dataEmbedding n (e 1))]

noncomputable def compileGates {n : ℕ} (gs : List (Instr gatesG2 n)) : List (Instr gatesHT (n+3)) :=
  gs.flatMap compileInstr





noncomputable def compileVerifier (V : Verifier gatesG2) : Verifier gatesHT where
  proofQubits := V.proofQubits
  ancillaQubits := V.ancillaQubits + 3
  gates := (compileGates V.gates).map (Instr.mapWires
    (finCongr (Nat.add_assoc V.proofQubits V.ancillaQubits 3)).toEmbedding)
  output := ⟨V.output.val, by have := V.output.isLt; omega⟩





end QMAPerfectCompleteness.Main.HTCompiler


