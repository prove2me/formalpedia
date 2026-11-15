-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_DyadicCompiler
-- name    : QMAPerfectCompleteness_Proof_DyadicCompiler
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:49:08.416445+00:00
-- url     : https://prove2.me/theorems/73b17879-693b-4d92-b311-31dde891a731
-- title:
--   Exact circuit construction for the real simulation
-- statement:
--   Defines the HP-to-G₂ instruction and verifier compiler of Lemma 3.1. Source wire addresses are shifted to make room for a simulation bit in the proof and an ignored ancillary bit. Literal paired-Hadamard and controlled-phase gadgets implement each source instruction; explicit register equivalences identify the compiled matrix with its real simulation and the ignored wire.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/DyadicCompiler.lean, lines 10–627.

/- Generated from Solutions.DyadicCompiler by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding



open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.DyadicCompiler
open GateCompilation

/-- The real-simulation proof wire is 0, source wire w is w+1, ignored wire d is n+1. -/
def dataWire {n : ℕ} (w : Fin n) : Fin (n + 2) := ⟨w.val + 1, by omega⟩
def simulationWire (n : ℕ) : Fin (n + 2) := ⟨0, by omega⟩
def ignoredWire (n : ℕ) : Fin (n + 2) := ⟨n + 1, by omega⟩

def hadamardPlacement {n : ℕ} (w : Fin n) : Fin 2 ↪ Fin (n + 2) :=
  ⟨![dataWire w, ignoredWire n], by
    intro i j hij
    have hw := w.isLt
    fin_cases i <;> fin_cases j <;> simp_all [dataWire, ignoredWire, Fin.mk.injEq] <;> omega⟩

def phasePlacement {n : ℕ} (e : Fin 2 ↪ Fin n) : Fin 4 ↪ Fin (n + 2) :=
  ⟨![simulationWire n, dataWire (e 0), dataWire (e 1), ignoredWire n], by
    intro i j hij
    have h0 := (e 0).isLt
    have h1 := (e 1).isLt
    have hne : (e 0).val ≠ (e 1).val := by
      intro h
      have hh := e.injective (Fin.ext h)
      exact (by decide : (0 : Fin 2) ≠ 1) hh
    fin_cases i <;> fin_cases j <;>
      simp_all [simulationWire, dataWire, ignoredWire, Fin.mk.injEq,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] <;> omega⟩

/-- Compile one source gate exactly using the concrete gadgets of Lemma 3.1. -/
noncomputable def compileInstr {n : ℕ} (i : Instr gatesHP n) : List (Instr gatesG2 (n + 2)) := by
  by_cases h : i.gate.val = 0
  · have hg : i.gate = (⟨0, by decide⟩ : Fin gatesHP.length) := Fin.ext h
    let w : Fin (gatesHP.get i.gate).arity := ⟨0, by rw [hg]; decide⟩
    exact [⟨⟨3, by decide⟩, hadamardPlacement (i.targets w)⟩]
  · have hg : i.gate = (⟨1, by decide⟩ : Fin gatesHP.length) := by
      apply Fin.ext
      change i.gate.val = 1
      have hlt := i.gate.isLt
      change i.gate.val < 2 at hlt
      omega
    let e : Fin 2 ↪ Fin n := (finCongr
      (show 2 = (gatesHP.get i.gate).arity by rw [hg]; rfl)).toEmbedding.trans i.targets
    exact realControlledPhaseCircuit.map (Instr.mapWires (phasePlacement e))

noncomputable def compileGates {n : ℕ} (gs : List (Instr gatesHP n)) :
    List (Instr gatesG2 (n + 2)) := gs.flatMap compileInstr

def tags {G : GateSet} {n : ℕ} (i : Instr G n) : ℕ × List ℕ :=
  (i.gate.val, List.ofFn fun a => (i.targets a).val)

/-- Fully computable instruction translation for a future concrete string/TM compiler.
Malformed tags and malformed wire lists map to an empty list. -/
def compileTags (n : ℕ) : ℕ × List ℕ → List (ℕ × List ℕ)
  | (0,[w]) => [(3,[w+1,n+1])]
  | (1,[a,b]) => [(3,[0,n+1]),(2,[a+1,b+1,0]),(3,[0,n+1]),(2,[a+1,b+1,0])]
  | _ => []







/-- The new c wire is part of Merlin's proof, while d is a verifier ancilla, as in the paper. -/
noncomputable def compileVerifier (V : Verifier gatesHP) : Verifier gatesG2 where
  proofQubits := V.proofQubits + 1
  ancillaQubits := V.ancillaQubits + 1
  gates := (compileGates V.gates).map (Instr.mapWires
    (finCongr (show V.proofQubits + V.ancillaQubits + 2 =
      (V.proofQubits + 1) + (V.ancillaQubits + 1) by omega)).toEmbedding)
  output := ⟨V.output.val + 1, by have := V.output.isLt; omega⟩













/-- The executable numeric table is exactly the semantic instruction translation. -/
theorem compileInstr_tags {n : ℕ} (i : Instr gatesHP n) :
    (compileInstr i).map tags = compileTags n (tags i) := by
  rcases i with ⟨g,e⟩
  fin_cases g <;> rfl





/-- Separate the simulation proof bit, all original wires, and the ignored final wire. -/
def splitWires (n : ℕ) : Basis (n + 2) ≃ (Bool × Basis n) × Bool where
  toFun x := ((x 0, Fin.init (Fin.tail x)), x (Fin.last (n + 1)))
  invFun x := Fin.cons x.1.1 (Fin.snoc x.1.2 x.2)
  left_inv x := by
    change Fin.cons (x 0) (Fin.snoc (Fin.init (Fin.tail x)) ((Fin.tail x) (Fin.last n))) = x
    rw [Fin.snoc_init_self, Fin.cons_self_tail]
  right_inv x := by
    rcases x with ⟨⟨c,p⟩,d⟩
    simp [Fin.tail_cons, Fin.init_snoc, Fin.cons_last, Fin.snoc_last]





noncomputable def complexRealRep {ι κ : Type*} (A : Matrix ι κ ℂ) :
    Matrix (Bool × ι) (Bool × κ) ℂ := (RealSimulation.realRep A).map Complex.ofReal





/-- Matrix-level compiler semantics: complex real simulation tensored with the ignored wire. -/
noncomputable def simulationMatrix {n : ℕ} (A : Matrix (Basis n) (Basis n) ℂ)
    (D : Matrix Bool Bool ℂ) : Matrix (Basis (n + 2)) (Basis (n + 2)) ℂ :=
  (complexRealRep A ⊗ₖ D).submatrix (splitWires n) (splitWires n)




















noncomputable def bitHadamard : Matrix Bool Bool ℂ := Matrix.of fun y x =>
  if y && x then -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else ((Real.sqrt 2 : ℝ) : ℂ)⁻¹





























def compiledWireEquiv (V : Verifier gatesHP) :
    Fin (V.proofQubits + V.ancillaQubits + 2) ≃
      Fin ((V.proofQubits + 1) + (V.ancillaQubits + 1)) := finCongr (by omega)

def compiledBasis (V : Verifier gatesHP) :
    Basis ((V.proofQubits + 1) + (V.ancillaQubits + 1)) ≃
      Basis (V.proofQubits + V.ancillaQubits + 2) :=
  Equiv.arrowCongr (compiledWireEquiv V).symm (Equiv.refl Bool)





def wireLayout (V : Verifier gatesHP) : (compileVerifier V).Wire ≃ (Bool × V.Wire) × Bool :=
  (compiledBasis V).trans (splitWires (V.proofQubits + V.ancillaQubits))

def proofLayout (m : ℕ) : Basis (m + 1) ≃ (Bool × Basis m) × Unit where
  toFun p := ((p 0, Fin.tail p), ())
  invFun p := Fin.cons p.1.1 p.1.2
  left_inv p := Fin.cons_self_tail p
  right_inv p := by rcases p with ⟨⟨c,p⟩,u⟩; cases u; simp



noncomputable def ignoredZero : Matrix Bool Unit ℂ := Matrix.of fun d _ => if d = false then 1 else 0













def singletonBit : Bool ≃ Basis 1 where
  toFun b := fun _ => b
  invFun p := p 0
  left_inv b := rfl
  right_inv p := by funext i; fin_cases i; rfl







def splitProof (m : ℕ) : Basis (m + 1) ≃ Bool × Basis m where
  toFun p := (p 0, Fin.tail p)
  invFun p := Fin.cons p.1 p.2
  left_inv p := Fin.cons_self_tail p
  right_inv p := by rcases p with ⟨c,p⟩; simp



end QMAPerfectCompleteness.Main.DyadicCompiler


