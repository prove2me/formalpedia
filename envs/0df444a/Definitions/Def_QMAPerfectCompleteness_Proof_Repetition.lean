-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
-- name    : QMAPerfectCompleteness_Proof_Repetition
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:47:09.951695+00:00
-- url     : https://prove2.me/theorems/ec91d9ce-08e3-41d8-a2f1-d6986952b1cc
-- title:
--   Tensor acceptance and the literal AND-repetition verifier
-- statement:
--   Defines recursively indexed tensor powers of acceptance matrices, together with the physical G₂ verifier that runs n disjoint copies and computes the conjunction of their output bits. Proof bits stay contiguous, each copy receives its own ancillas, and n+1 flags implement the prefix-AND chain. The full proof space permits entanglement across copies.
-- source:
--   Auxiliary construction in the formalization of Grewal–Rudolph, QMA has perfect completeness (paper manuscript ~/research/qma1z/main.tex). Source commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/Repetition.lean, lines 10–287.

/- Generated from Solutions.Repetition by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof



open Matrix
open scoped Kronecker ComplexOrder
namespace QMAPerfectCompleteness.Main.Repetition
open VerifierAnalysis DiagonalProof CyclicProof

universe u

/-- A recursive tensor-product basis; no restriction to product states is imposed on this space. -/
abbrev RepeatedIndex (ι : Type u) : ℕ → Type u
  | 0 => PUnit
  | n+1 => ι × RepeatedIndex ι n

instance repeatedFintype {ι : Type u} [Fintype ι] (n : ℕ) : Fintype (RepeatedIndex ι n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => letI := ih; exact inferInstanceAs (Fintype (ι × RepeatedIndex ι n))

instance repeatedDecidableEq {ι : Type u} [DecidableEq ι] (n : ℕ) :
    DecidableEq (RepeatedIndex ι n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ n ih => letI := ih; exact inferInstanceAs (DecidableEq (ι × RepeatedIndex ι n))

/-- Repeated acceptance requires all n copies to accept, giving the tensor power of E. -/
def tensorPower {ι : Type u} [DecidableEq ι] (E : Matrix ι ι ℂ) :
    (n : ℕ) → Matrix (RepeatedIndex ι n) (RepeatedIndex ι n) ℂ
  | 0 => 1
  | n+1 => E ⊗ₖ tensorPower E n

variable {ι : Type u} [Fintype ι] [DecidableEq ι]



























/-! ## Concrete gate list for repetition

The proof wires of the copies come first; each copy's ancillas follow, then n+1 prefix-AND flags.
No certificate or proof measurements occur between the copies. The final flag is the output.
-/

namespace Circuit

/-- Insert one coordinate into a fixed copy of a product register. -/
def copyIndex (n d : ℕ) (j : Fin n) : Fin d ↪ Fin (n*d) :=
  ⟨fun k => finProdFinEquiv (j,k), fun a b h => (Prod.mk.inj (finProdFinEquiv.injective h)).2⟩

abbrev proofCount (V : Verifier gatesG2) (n : ℕ) := n * V.proofQubits
abbrev ancillaCount (V : Verifier gatesG2) (n : ℕ) := n * V.ancillaQubits + (n+1)
abbrev wireCount (V : Verifier gatesG2) (n : ℕ) := proofCount V n + ancillaCount V n

/-- Relocate a copy's proof wires and ancilla wires while keeping all proof wires contiguous. -/
def copyEmbedding (V : Verifier gatesG2) (n : ℕ) (j : Fin n) :
    Fin (V.proofQubits + V.ancillaQubits) ↪ Fin (wireCount V n) :=
  finSumFinEquiv.symm.toEmbedding.trans
    ((Function.Embedding.sumMap (copyIndex n V.proofQubits j)
      ((copyIndex n V.ancillaQubits j).trans (Fin.castAddEmb (n+1)))).trans
        finSumFinEquiv.toEmbedding)

/-- The k-th prefix-AND flag, with flag zero initialized to one. -/
def flagWire (V : Verifier gatesG2) (n : ℕ) (k : Fin (n+1)) : Fin (wireCount V n) :=
  Fin.natAdd (proofCount V n) (Fin.natAdd (n * V.ancillaQubits) k)

lemma copyEmbedding_before_flags (V : Verifier gatesG2) (n : ℕ) (j : Fin n)
    (w : Fin (V.proofQubits + V.ancillaQubits)) :
    (copyEmbedding V n j w : ℕ) < n * V.proofQubits + n * V.ancillaQubits := by
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective w
  cases x with
  | inl p =>
    have hp := (copyIndex n V.proofQubits j p).2
    simpa [copyEmbedding, Function.Embedding.trans_apply, Function.Embedding.coe_sumMap,
      proofCount, ancillaCount, wireCount] using lt_of_lt_of_le hp (Nat.le_add_right _ _)
  | inr a =>
    have ha := (copyIndex n V.ancillaQubits j a).2
    simp only [copyEmbedding, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Equiv.symm_apply_apply, finSumFinEquiv_symm_apply_natAdd, Function.Embedding.coe_sumMap, Sum.map_inr,
      finSumFinEquiv_apply_right, Fin.val_natAdd, Fin.castAddEmb_apply, Fin.val_castAdd]
    exact Nat.add_lt_add_left ha _

lemma flagWire_ne_copy (V : Verifier gatesG2) (n : ℕ) (k : Fin (n+1)) (j : Fin n)
    (w : Fin (V.proofQubits + V.ancillaQubits)) : flagWire V n k ≠ copyEmbedding V n j w := by
  intro h
  have heq := congrArg Fin.val h
  have hlt := copyEmbedding_before_flags V n j w
  simp only [flagWire, Fin.val_natAdd, proofCount] at heq
  omega

lemma flagWire_injective (V : Verifier gatesG2) (n : ℕ) : Function.Injective (flagWire V n) := by
  intro a b h
  apply Fin.ext
  have heq := congrArg Fin.val h
  simp only [flagWire, Fin.val_natAdd] at heq
  omega

def initializeTarget (V : Verifier gatesG2) (n : ℕ) : Fin 1 ↪ Fin (wireCount V n) :=
  ⟨fun _ => flagWire V n 0, fun a b _ => Subsingleton.elim a b⟩

/-- Initialize the first prefix-AND flag to one using X. -/
noncomputable def initializeFlag (V : Verifier gatesG2) (n : ℕ) : Instr gatesG2 (wireCount V n) :=
  ⟨⟨0, by decide⟩, initializeTarget V n⟩

/-- Three distinct wires for each prefix-AND Toffoli. -/
def andTargets (V : Verifier gatesG2) (n : ℕ) (j : Fin n) : Fin 3 ↪ Fin (wireCount V n) :=
  ⟨fun k => ![flagWire V n j.castSucc,
      copyEmbedding V n j V.output, flagWire V n j.succ] k, by
    intro a b hab
    have hprev := flagWire_ne_copy V n j.castSucc j V.output
    have hnext := flagWire_ne_copy V n j.succ j V.output
    have hflags : flagWire V n j.castSucc ≠ flagWire V n j.succ := by
      intro h
      have heq := congrArg Fin.val (flagWire_injective V n h)
      simp at heq
    fin_cases a <;> fin_cases b <;> simp_all⟩

/-- One Toffoli computes the next prefix-AND from the previous flag and a copy's output. -/
noncomputable def andStep (V : Verifier gatesG2) (n : ℕ) (j : Fin n) : Instr gatesG2 (wireCount V n) :=
  ⟨⟨2, by decide⟩, andTargets V n j⟩

/-- Run each verifier copy once, leaving its output wire in place. -/
noncomputable def parallelGates (V : Verifier gatesG2) (n : ℕ) : List (Instr gatesG2 (wireCount V n)) :=
  (List.finRange n).flatMap fun j => V.gates.map (Instr.mapWires (copyEmbedding V n j))

/-- A concrete verifier over G₂: run the copies and then compute their output conjunction. -/
noncomputable def verifier (V : Verifier gatesG2) (n : ℕ) : Verifier gatesG2 :=
  { proofQubits := proofCount V n
    ancillaQubits := ancillaCount V n
    gates := parallelGates V n ++ [initializeFlag V n] ++ (List.finRange n).map (andStep V n)
    output := flagWire V n (Fin.last n) }

lemma parallelGates_length (V : Verifier gatesG2) (n : ℕ) :
    (parallelGates V n).length = n * V.gates.length := by
  simp [parallelGates, List.length_flatMap]

/-- A fixed n costs only a linear increase in gates; the AND chain has exactly n Toffolis. -/
lemma verifier_gate_count (V : Verifier gatesG2) (n : ℕ) :
    (verifier V n).gates.length = n * V.gates.length + 1 + n := by
  simp [verifier, parallelGates_length]
  omega

end Circuit

end QMAPerfectCompleteness.Main.Repetition


