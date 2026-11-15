-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
-- name    : QMAPerfectCompleteness_Proof_RepetitionCircuit
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:51:49.44081+00:00
-- url     : https://prove2.me/theorems/34987619-b912-47b0-8b0c-6d0c112b1133
-- title:
--   Register coordinates for physical verifier repetition
-- statement:
--   Defines the equivalence grouping physical wires into verifier-copy registers and prefix-AND flags, the corresponding grouped proof basis, and the generic tensor matrices acting on the copies. An explicit clean-AND layout and input embedding connect the literal repetition gate list with the tensor-power acceptance operator.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RepetitionCircuit.lean, lines 13–569.

/- Generated from Solutions.RepetitionCircuit by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof



open Matrix
open scoped Kronecker ComplexOrder

set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.Repetition.CircuitProof
open Circuit ReversibleGadgets VerifierAnalysis


lemma copyEmbedding_proof (V : Verifier gatesG2) (n : ℕ) (j : Fin n) (p : Fin V.proofQubits) :
    copyEmbedding V n j (Fin.castAdd V.ancillaQubits p) =
      Fin.castAdd (ancillaCount V n) (copyIndex n V.proofQubits j p) := by
  simp [copyEmbedding, Function.Embedding.trans_apply, Function.Embedding.coe_sumMap]

lemma copyEmbedding_ancilla (V : Verifier gatesG2) (n : ℕ) (j : Fin n) (a : Fin V.ancillaQubits) :
    copyEmbedding V n j (Fin.natAdd V.proofQubits a) =
      Fin.natAdd (proofCount V n) (Fin.castAdd (n+1) (copyIndex n V.ancillaQubits j a)) := by
  simp [copyEmbedding, Function.Embedding.trans_apply, Function.Embedding.coe_sumMap]

@[simp] lemma decode_copyIndex (n d : ℕ) (j : Fin n) (p : Fin d) :
    finProdFinEquiv.symm (copyIndex n d j p) = (j,p) := by
  change finProdFinEquiv.symm (finProdFinEquiv (j,p)) = (j,p)
  exact Equiv.symm_apply_apply _ _

@[simp] lemma encode_copyIndex (n d : ℕ) (p : Fin (n*d)) :
    copyIndex n d (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 = p := by
  change finProdFinEquiv (finProdFinEquiv.symm p) = p
  exact Equiv.apply_symm_apply _ _

@[simp] lemma copyIndex_divNat (n d : ℕ) (j : Fin n) (p : Fin d) :
    (copyIndex n d j p).divNat = j := congrArg Prod.fst (decode_copyIndex n d j p)

@[simp] lemma copyIndex_modNat (n d : ℕ) (j : Fin n) (p : Fin d) :
    (copyIndex n d j p).modNat = p := congrArg Prod.snd (decode_copyIndex n d j p)

@[simp] lemma copyIndex_divModNat (n d : ℕ) (p : Fin (n*d)) :
    copyIndex n d p.divNat p.modNat = p := encode_copyIndex n d p

/-- Decode a physical wire as a wire of one copy or a prefix-AND flag. -/
def decodeWire (V : Verifier gatesG2) (n : ℕ) :
    Fin (wireCount V n) → (Fin n × Fin (V.proofQubits+V.ancillaQubits)) ⊕ Fin (n+1) :=
  Fin.addCases
    (fun p => Sum.inl ((finProdFinEquiv.symm p).1,
      Fin.castAdd V.ancillaQubits (finProdFinEquiv.symm p).2))
    (Fin.addCases
      (fun a => Sum.inl ((finProdFinEquiv.symm a).1,
        Fin.natAdd V.proofQubits (finProdFinEquiv.symm a).2))
      Sum.inr)

def encodeWire (V : Verifier gatesG2) (n : ℕ) :
    (Fin n × Fin (V.proofQubits+V.ancillaQubits)) ⊕ Fin (n+1) → Fin (wireCount V n)
  | Sum.inl (j,w) => copyEmbedding V n j w
  | Sum.inr k => flagWire V n k

lemma decode_encode_wire (V : Verifier gatesG2) (n : ℕ) :
    Function.LeftInverse (decodeWire V n) (encodeWire V n) := by
  rintro (⟨j,w⟩|k)
  · refine Fin.addCases (fun p => ?_) (fun a => ?_) w
    · simp [encodeWire, copyEmbedding_proof, decodeWire]
    · simp [encodeWire, copyEmbedding_ancilla, decodeWire]
  · simp [encodeWire, decodeWire, flagWire]

lemma encode_decode_wire (V : Verifier gatesG2) (n : ℕ) :
    Function.RightInverse (decodeWire V n) (encodeWire V n) := by
  intro w
  refine Fin.addCases (fun p => ?_) (fun a => ?_) w
  · simp [decodeWire, encodeWire, copyEmbedding_proof]
  · refine Fin.addCases (fun a => ?_) (fun k => ?_) a
    · simp [decodeWire, encodeWire, copyEmbedding_ancilla]
    · simp [decodeWire, encodeWire, flagWire]



@[simp] lemma decodeWire_copy (V : Verifier gatesG2) (n : ℕ) (j : Fin n)
    (w : Fin (V.proofQubits+V.ancillaQubits)) :
    decodeWire V n (copyEmbedding V n j w) = Sum.inl (j,w) :=
  decode_encode_wire V n (Sum.inl (j,w))

@[simp] lemma decodeWire_flag (V : Verifier gatesG2) (n : ℕ) (k : Fin (n+1)) :
    decodeWire V n (flagWire V n k) = Sum.inr k := decode_encode_wire V n (Sum.inr k)

/-- Group the physical basis into copy registers and AND flags. -/
def basisEquiv (V : Verifier gatesG2) (n : ℕ) :
    Basis (wireCount V n) ≃ (Fin n → V.Wire) × Basis (n+1) where
  toFun x := (fun j => x ∘ copyEmbedding V n j, x ∘ flagWire V n)
  invFun x w := match decodeWire V n w with
    | Sum.inl (j,v) => x.1 j v
    | Sum.inr k => x.2 k
  left_inv x := by
    funext w
    have he := encode_decode_wire V n w
    dsimp [encodeWire] at he
    cases hd : decodeWire V n w with
    | inl jv =>
      obtain ⟨j,v⟩ := jv
      simp only [hd] at he
      simpa only [hd, Function.comp_apply] using congrArg x he
    | inr k =>
      simp only [hd] at he
      simpa only [hd, Function.comp_apply] using congrArg x he
  right_inv x := by
    apply Prod.ext
    · funext j w
      simp [decodeWire_copy]
    · funext k
      simp [decodeWire_flag]









/-! Generic finite tensor matrices on function-indexed copy registers. -/

noncomputable abbrev piMatrix {J α : Type*} [Fintype J] (M : J → Matrix α α ℂ) :
    Matrix (J → α) (J → α) ℂ := fun y x => ∏ j, M j (y j) (x j)







/-- A family of copy matrices, with all flag wires untouched. -/
noncomputable def liftCopies (V : Verifier gatesG2) (n : ℕ)
    (M : Fin n → Matrix V.Wire V.Wire ℂ) :
    Matrix (Basis (wireCount V n)) (Basis (wireCount V n)) ℂ :=
  (piMatrix M ⊗ₖ (1 : Matrix (Basis (n+1)) (Basis (n+1)) ℂ)).submatrix
    (basisEquiv V n) (basisEquiv V n)







noncomputable def copyProduct (V : Verifier gatesG2) {n : ℕ} (js : List (Fin n))
    (k : Fin n) : Matrix V.Wire V.Wire ℂ :=
  (js.reverse.map fun j => if k = j then V.unitary else 1).prod







/-- Group the contiguous physical proof bits into the separate copies' proof registers. -/
def proofEquiv (V : Verifier gatesG2) (n : ℕ) :
    Basis (proofCount V n) ≃ (Fin n → V.Proof) where
  toFun p j k := p (copyIndex n V.proofQubits j k)
  invFun p r := p r.divNat r.modNat
  left_inv p := by
    funext r
    simp
  right_inv p := by
    funext j k
    simp















/-- The generic clean-AND circuit instantiated on the repeated verifier outputs. -/
def andLayout (V : Verifier gatesG2) (n : ℕ) :
    ControlCircuits.AndLayout n (wireCount V n) where
  controls := ⟨fun j => copyEmbedding V n j V.output, by
    intro j k h
    have hh := congrArg (decodeWire V n) h
    simp only [decodeWire_copy, Sum.inl.injEq, Prod.mk.injEq] at hh
    exact hh.1⟩
  flags := ⟨flagWire V n, flagWire_injective V n⟩
  disjoint j k := (flagWire_ne_copy V n k j V.output).symm

noncomputable def andSuffix (V : Verifier gatesG2) (n : ℕ) : List (Instr gatesG2 (wireCount V n)) :=
  [initializeFlag V n] ++ (List.finRange n).map (Circuit.andStep V n)









noncomputable def parallelInput (V : Verifier gatesG2) (n : ℕ) :
    Matrix ((Circuit.verifier V n).Wire) ((Circuit.verifier V n).Proof) ℂ :=
  (show Matrix (Circuit.verifier V n).Wire (Circuit.verifier V n).Wire ℂ from
    circuitMatrix (parallelGates V n)) * (Circuit.verifier V n).ancillaZero













universe u

/-- Relate recursive tensor bases to copy-indexed function registers. -/
def tensorIndexEquiv (α : Type u) : (n : ℕ) → RepeatedIndex α n ≃ (Fin n → α)
  | 0 =>
    { toFun := fun _ j => Fin.elim0 j
      invFun := fun _ => PUnit.unit
      left_inv := fun x => Subsingleton.elim _ _
      right_inv := by intro f; funext j; exact Fin.elim0 j }
  | n+1 =>
    { toFun := fun x => Fin.cons x.1 (tensorIndexEquiv α n x.2)
      invFun := fun f => (f 0, (tensorIndexEquiv α n).symm (fun j => f j.succ))
      left_inv := by
        rintro ⟨a,x⟩
        apply Prod.ext
        · rfl
        · simpa only [Fin.cons_succ] using (tensorIndexEquiv α n).symm_apply_apply x
      right_inv := by
        intro f
        funext j
        refine Fin.cases ?_ (fun k => ?_) j
        · simp
        · simp }



def proofTensorEquiv (V : Verifier gatesG2) (n : ℕ) :
    (Circuit.verifier V n).Proof ≃ RepeatedIndex V.Proof n :=
  (proofEquiv V n).trans (tensorIndexEquiv V.Proof n).symm













end QMAPerfectCompleteness.Main.Repetition.CircuitProof


