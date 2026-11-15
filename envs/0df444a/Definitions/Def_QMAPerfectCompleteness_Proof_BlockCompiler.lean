-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
-- name    : QMAPerfectCompleteness_Proof_BlockCompiler
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:55:53.873194+00:00
-- url     : https://prove2.me/theorems/5ef2aa79-de0d-44ec-8bf4-17a5d1936820
-- title:
--   Block-circuit layouts and clean classical programs
-- statement:
--   Defines the index, clock, verifier, flag, predicate-tag and shared-scratch registers surrounding the original verifier. A clean program consists of a literal gate list, a deterministic basis action, and a preserved cleanliness invariant; composition and reversal support the clock test, controlled flag update and modular shift used by the paper circuit.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/BlockCompiler.lean, lines 10–911.

/- Generated from Solutions.BlockCompiler by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets



/-! Concrete paper block-compiler scaffolds. Circuit data depend only on layout and certificate. -/

open Matrix
namespace QMAPerfectCompleteness.Main.BlockCompiler
open ReversibleGadgets ControlCircuits EqualityCircuits ComparisonCircuits ClockCircuits

/-- All classical data used by the surrounding circuit, with no verifier gate list. -/
structure Layout where
  proof : ℕ
  ancilla : ℕ
  index : ℕ
  output : Fin (proof + ancilla)

/-- A classical subcircuit with a specified clean-workspace invariant. -/
structure CleanProgram (n : ℕ) (Clean : Basis n → Prop) where
  gates : List (Instr gatesG2 n)
  action : Basis n → Basis n
  sound : ∀ y x, Clean x → circuitMatrix gates y x = if y = action x then 1 else 0
  preserves : ∀ x, Clean x → Clean (action x)

namespace CleanProgram

noncomputable def append {n : ℕ} {Clean : Basis n → Prop}
    (P Q : CleanProgram n Clean) : CleanProgram n Clean where
  gates := P.gates ++ Q.gates
  action := Q.action ∘ P.action
  sound y x hx := by
    rw [BlockProof.circuitMatrix_append, Matrix.mul_apply]
    simp_rw [P.sound _ x hx]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact Q.sound y (P.action x) (P.preserves x hx)
  preserves x hx := Q.preserves (P.action x) (P.preserves x hx)

/-- A clean involutive basis action is implemented by the reversed literal gate list as well.
The proof uses actual circuit unitarity, so it also rules out leakage from dirty output rows. -/
noncomputable def reverseOfInvolution {n : ℕ} {Clean : Basis n → Prop}
    (P : CleanProgram n Clean) (hi : Function.Involutive P.action) : CleanProgram n Clean where
  gates := P.gates.reverse
  action := P.action
  sound y x hx := by
    have hu : (circuitMatrix P.gates)ᴴ * circuitMatrix P.gates = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp (CircuitProof.circuit_unitary P.gates)
    have he := congrArg (fun M : Matrix (Basis n) (Basis n) ℂ => M y (P.action x)) hu
    rw [Matrix.mul_apply] at he
    have hc : ∀ z, circuitMatrix P.gates z (P.action x) = if z = x then 1 else 0 := by
      intro z
      rw [P.sound z (P.action x) (P.preserves x hx), hi x]
    simp_rw [hc] at he
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at he
    simpa only [BlockProof.circuitMatrix_reverse_g2, Matrix.one_apply] using he
  preserves := P.preserves

end CleanProgram

namespace Layout

abbrev clock (D : Layout) : ℕ := clockQubits D.proof

abbrev scale (D : Layout) : ℕ := D.index + D.clock + D.proof

abbrev body (D : Layout) : ℕ := D.index + D.clock + (D.proof + D.ancilla) + 1

abbrev work (D : Layout) : ℕ := D.scale + 15

abbrev total (D : Layout) : ℕ := D.body + D.work

def indexWire (D : Layout) (i : Fin D.index) : Fin D.total :=
  ⟨i, by have := i.isLt; dsimp [total, body, work, scale, clock]; omega⟩

def clockWire (D : Layout) (i : Fin D.clock) : Fin D.total :=
  ⟨D.index + i, by have := i.isLt; dsimp [total, body, work, scale]; omega⟩

def verifierWire (D : Layout) (i : Fin (D.proof + D.ancilla)) : Fin D.total :=
  ⟨D.index + D.clock + i, by have := i.isLt; dsimp [total, body, work, scale]; omega⟩

def flagWire (D : Layout) : Fin D.total :=
  ⟨D.index + D.clock + (D.proof + D.ancilla), by dsimp [total, body, work, scale]; omega⟩

/-- Persistent predicate tags 0..10, before the shared scratch flags. -/
def tagWire (D : Layout) (i : Fin 11) : Fin D.total :=
  ⟨D.body + i, by have := i.isLt; dsimp [total, work, scale]; omega⟩

/-- Every predicate gadget reuses an initially-zero prefix of these scratch flags. -/
def scratchWire (D : Layout) (i : Fin (D.scale+4)) : Fin D.total :=
  ⟨D.body + (11+i), by have := i.isLt; dsimp [total, work]; omega⟩



def clockEmbedding (D : Layout) : Fin D.clock ↪ Fin D.total :=
  ⟨D.clockWire, by intro i j h; apply Fin.ext; have hv := congrArg Fin.val h; dsimp [clockWire] at hv; omega⟩



def scratchEmbedding (D : Layout) (s : ℕ) (hs : s ≤ D.scale+4) : Fin s ↪ Fin D.total :=
  ⟨fun i => D.scratchWire ⟨i, Nat.lt_of_lt_of_le i.isLt hs⟩,
    by intro i j h; apply Fin.ext; have hv := congrArg Fin.val h; dsimp [scratchWire] at hv; omega⟩

lemma body_ne_scratch (D : Layout) (w : Fin D.total) (hw : (w : ℕ) < D.body)
    (i : Fin (D.scale+4)) : w ≠ D.scratchWire i := by
  intro h
  have hv := congrArg Fin.val h
  change (w : ℕ) = D.body + (11+i) at hv
  omega

lemma tag_ne_scratch (D : Layout) (i : Fin 11) (j : Fin (D.scale+4)) :
    D.tagWire i ≠ D.scratchWire j := by
  intro h
  have hv := congrArg Fin.val h
  change D.body + (i : ℕ) = D.body + (11+j) at hv
  have := i.isLt
  omega



def clockLayout (D : Layout) : AndLayout D.clock D.total where
  controls := D.clockEmbedding
  flags := D.scratchEmbedding (D.clock+1) (by dsimp [scale]; omega)
  disjoint i j := D.body_ne_scratch _ (by
    have := i.isLt; change D.index + (i : ℕ) < D.body; dsimp [body]; omega) _





lemma clock_ne_tag (D : Layout) (i : Fin D.clock) (j : Fin 11) : D.clockWire i ≠ D.tagWire j := by
  intro h
  have hv := congrArg Fin.val h
  change D.index + (i : ℕ) = D.body + (j : ℕ) at hv
  have := i.isLt
  dsimp [body] at hv
  omega



def incrementLayout (D : Layout) : AndLayout (D.clock+1) D.total where
  controls := ⟨Fin.cases (D.tagWire 5) D.clockWire, by
    intro i j h
    revert h
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases (fun _ => rfl) (fun b => ?_) j
      intro h
      exact ((D.clock_ne_tag b 5).symm h).elim
    · refine Fin.cases ?_ (fun b => ?_) j
      · intro h
        exact ((D.clock_ne_tag a 5) h).elim
      · intro h
        exact congrArg Fin.succ (D.clockEmbedding.injective h)⟩
  flags := D.scratchEmbedding (D.clock+2) (by dsimp [scale]; omega)
  disjoint i j := by
    refine Fin.cases ?_ (fun a => ?_) i
    · exact D.tag_ne_scratch 5 _
    · exact D.body_ne_scratch _ (by
        have := a.isLt; change D.index + (a : ℕ) < D.body; dsimp [body]; omega) _







def tagToFlag (D : Layout) (a : Fin 11) : Fin 2 ↪ Fin D.total :=
  ⟨![D.tagWire a,D.flagWire], by
    intro i j h
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals have hv := congrArg Fin.val h
    all_goals dsimp [tagWire, flagWire, body] at hv
    all_goals omega⟩

def phaseTargets (D : Layout) : Fin 2 ↪ Fin D.total :=
  ⟨![D.tagWire 5,D.tagWire 9], by
    intro i j h
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals have hv := congrArg Fin.val h
    all_goals dsimp [tagWire] at hv
    all_goals omega⟩

/-- Range tag, clock predicate, verifier output, rejection flag, and one scratch wire. -/
def forwardFlagTargets (D : Layout) : Fin 5 ↪ Fin D.total :=
  ⟨![D.tagWire 3,D.tagWire 6,D.verifierWire D.output,D.flagWire,D.tagWire 10], by
    intro i j h
    have ho := D.output.isLt
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals have hv := congrArg Fin.val h
    all_goals dsimp [tagWire, verifierWire, flagWire, body] at hv
    all_goals omega⟩













noncomputable def clockBelowGates (D : Layout) : List (Instr gatesG2 D.total) :=
  compareNatGates D.clockLayout (ell D.proof) (D.tagWire 6) (fun i => D.tag_ne_scratch 6 _)





/-- The sole operation between V and V†; its clock predicate is uncomputed before returning. -/
noncomputable def mid (D : Layout) : List (Instr gatesG2 D.total) :=
  D.clockBelowGates ++ tripleControlledXAt D.forwardFlagTargets ++ D.clockBelowGates.reverse























/-- Only the shared flags are required to be clean for the predicate programs. -/
def ScratchClean (D : Layout) (x : Basis D.total) : Prop :=
  ∀ i : Fin (D.scale+4), x (D.scratchWire i) = false

theorem scratchClean_update_tag (D : Layout) (x : Basis D.total) (hx : D.ScratchClean x)
    (tag : Fin 11) (b : Bool) : D.ScratchClean (Function.update x (D.tagWire tag) b) := by
  intro i
  rw [Function.update_of_ne (D.tag_ne_scratch tag i).symm]
  exact hx i

theorem tagWire_injective (D : Layout) : Function.Injective D.tagWire := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [tagWire] at hv
  omega

abbrev indexValue (D : Layout) (x : Basis D.total) : ℕ := BlockCircuit.bitsValue x D.indexWire























/-- Intended persistent tag values, in the literal physical tag order. -/
def rangeTruth (a b j : ℕ) : Fin 6 → Bool :=
  ![decide (j<a),decide (j<3*a),decide (j<3*a+b),
    (!decide (j<a) && decide (j<3*a)),
    (!decide (j<3*a) && decide (j<3*a+b)),
    (!decide (j<a) && decide (j<3*a+b))]

















/-- The shared scratch bank and dedicated triple-control scratch are initially zero. -/
def MidClean (D : Layout) (x : Basis D.total) : Prop :=
  D.ScratchClean x ∧ x (D.tagWire 10) = false

lemma flag_ne_tag (D : Layout) (j : Fin 11) : D.flagWire ≠ D.tagWire j := by
  intro h
  have hv := congrArg Fin.val h
  change D.index+D.clock+(D.proof+D.ancilla) = D.body+(j : ℕ) at hv
  dsimp [body] at hv
  omega

lemma flag_ne_scratch (D : Layout) (j : Fin (D.scale+4)) :
    D.flagWire ≠ D.scratchWire j :=
  D.body_ne_scratch _ (by change D.index+D.clock+(D.proof+D.ancilla) < D.body; simp [body]) j

abbrev clockValue (D : Layout) (x : Basis D.total) : ℕ := BlockCircuit.bitsValue x D.clockWire

lemma clockValue_update_tag (D : Layout) (x : Basis D.total) (j : Fin 11) (v : Bool) :
    D.clockValue (Function.update x (D.tagWire j) v) = D.clockValue x := by
  unfold clockValue BlockCircuit.bitsValue
  apply Finset.sum_congr rfl
  intro i _
  rw [Function.update_of_ne (D.clock_ne_tag i j)]





def clockBelowAction (D : Layout) (x : Basis D.total) : Basis D.total :=
  Function.update x (D.tagWire 6)
    (xor (x (D.tagWire 6)) (decide (D.clockValue x < ell D.proof)))

noncomputable def clockBelowProgram (D : Layout) : CleanProgram D.total D.MidClean where
  gates := D.clockBelowGates
  action := D.clockBelowAction
  sound y x hx := compareNatGates_matrix_bitsValue D.clockLayout (ell D.proof) (D.tagWire 6)
    (fun i => (D.clock_ne_tag i 6).symm) (fun i => D.tag_ne_scratch 6 _) y x (fun i => hx.1 _)
  preserves x hx := by
    constructor
    · exact D.scratchClean_update_tag x hx.1 6 _
    · change Function.update x (D.tagWire 6) _ (D.tagWire 10) = false
      rw [Function.update_of_ne ((D.tagWire_injective).ne (by decide : (10 : Fin 11) ≠ 6))]
      exact hx.2

theorem clockBelowAction_involutive (D : Layout) : Function.Involutive D.clockBelowAction := by
  intro x
  simp only [clockBelowAction, D.clockValue_update_tag, Function.update_self, Function.update_idem]
  simp



def forwardFlagAction (D : Layout) (x : Basis D.total) : Basis D.total :=
  Function.update x D.flagWire
    (xor (x D.flagWire) ((x (D.tagWire 3) && x (D.tagWire 6)) && x (D.verifierWire D.output)))

noncomputable def forwardFlagProgram (D : Layout) : CleanProgram D.total D.MidClean where
  gates := tripleControlledXAt D.forwardFlagTargets
  action := D.forwardFlagAction
  sound y x hx := by
    exact tripleControlledXAt_matrix D.forwardFlagTargets y x hx.2
  preserves x hx := by
    constructor
    · intro i
      change Function.update x D.flagWire _ (D.scratchWire i) = false
      rw [Function.update_of_ne (D.flag_ne_scratch i).symm]
      exact hx.1 i
    · change Function.update x D.flagWire _ (D.tagWire 10) = false
      rw [Function.update_of_ne (D.flag_ne_tag 10).symm]
      exact hx.2

noncomputable def midProgram (D : Layout) : CleanProgram D.total D.MidClean :=
  (D.clockBelowProgram.append D.forwardFlagProgram).append
    (D.clockBelowProgram.reverseOfInvolution D.clockBelowAction_involutive)

noncomputable abbrev midAction (D : Layout) : Basis D.total → Basis D.total := D.midProgram.action









































/-- The controlled shift restores the entire shared scratch bank. -/
noncomputable def incrementProgram (D : Layout) : CleanProgram D.total D.ScratchClean where
  gates := controlledIncrementGates D.incrementLayout
  action := controlledIncrementAction D.incrementLayout
  sound y x hx := controlledIncrementGates_matrix D.incrementLayout y x (fun i => hx _)
  preserves x hx := by
    intro j
    rw [controlledIncrementAction_outside]
    · exact hx j
    · intro i
      refine Fin.cases ?_ (fun a => ?_) i
      · exact (D.tag_ne_scratch 5 j).symm
      · exact (D.body_ne_scratch (D.clockWire a) (by
          have := a.isLt
          change D.index+(a : ℕ) < D.body
          dsimp [body]
          omega) j).symm



/-- The identity index branch flips the output flag exactly when ltA is set. -/
noncomputable def identityFlagProgram (D : Layout) : CleanProgram D.total D.ScratchClean where
  gates := [cnotAt (D.tagToFlag 0)]
  action := fun x => Function.update x D.flagWire (xor (x D.flagWire) (x (D.tagWire 0)))
  sound y x _ := by
    simp only [circuitMatrix, Matrix.one_mul, cnotAt_matrix]
    rfl
  preserves x hx := by
    intro j
    change Function.update x D.flagWire _ (D.scratchWire j) = false
    rw [Function.update_of_ne (D.flag_ne_scratch j).symm]
    exact hx j























end Layout

/-- The layout data extracted from a verifier; no gate is exposed to scaffold construction. -/
abbrev layoutOf (V : Verifier gatesG2) : Layout :=
  ⟨V.proofQubits,V.ancillaQubits,indexQubits V,V.output⟩









end QMAPerfectCompleteness.Main.BlockCompiler


