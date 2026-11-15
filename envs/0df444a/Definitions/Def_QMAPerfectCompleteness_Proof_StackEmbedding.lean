-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_StackEmbedding
-- name    : QMAPerfectCompleteness_Proof_StackEmbedding
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:56:36.857632+00:00
-- url     : https://prove2.me/theorems/cd8a3d24-7d59-490f-921f-11710f29be94
-- title:
--   Framed embedding of finite stack programs
-- statement:
--   Defines how a finite stack subprogram is placed in a larger shared register bank. The lifted execution preserves every spectator stack and transports the subprogram execution bound.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/StackEmbedding.lean, retained declaration span lines 9–100.

/- Generated from Solutions.StackEmbedding by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Proof_BinaryComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_StructuredStackCode
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion



/-! Embed a finite stack subprogram in a larger shared workspace, preserving other stacks. -/
open Turing StateTransition
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Uniformity.StructuredStack.Code
variable {K L : Type} [DecidableEq K] [DecidableEq L]

noncomputable def liftStacks (i : K ↪ L) (S : K → List Bool) (T : L → List Bool) (l : L) : List Bool := by
  classical
  exact if h : ∃ k, i k=l then S (Classical.choose h) else T l

@[simp] lemma liftStacks_get (i : K ↪ L) (S : K → List Bool) (T : L → List Bool) (k : K) :
    liftStacks i S T (i k)=S k := by
  rw [liftStacks,dif_pos ⟨k,rfl⟩]
  congr 1
  exact i.injective (Classical.choose_spec (show ∃ j,i j=i k from ⟨k,rfl⟩))

lemma liftStacks_update (i : K ↪ L) (S : K → List Bool) (T : L → List Bool)
    (k : K) (s : List Bool) :
    liftStacks i (Function.update S k s) T = Function.update (liftStacks i S T) (i k) s := by
  classical
  funext l
  by_cases h : ∃ j,i j=l
  · obtain ⟨j,rfl⟩ := h
    by_cases hj : j=k <;> simp [hj,EmbeddingLike.apply_eq_iff_eq]
  · have hl : l ≠ i k := fun he=>h ⟨k,he.symm⟩
    simp [liftStacks,h,hl]

noncomputable def embedStmt (i : K ↪ L) {A : Type} :
    TM2.Stmt (fun _ : K=>Bool) A (Option Bool) → TM2.Stmt (fun _ : L=>Bool) A (Option Bool)
  | .push k f q => .push (i k) f (embedStmt i q)
  | .pop k f q => .pop (i k) f (embedStmt i q)
  | .peek k f q => .peek (i k) f (embedStmt i q)
  | .load f q => .load f (embedStmt i q)
  | .branch f q r => .branch f (embedStmt i q) (embedStmt i r)
  | .goto f => .goto f
  | .halt => .halt

noncomputable def embed (i : K ↪ L) (P : Code K) : Code L where
  Label := P.Label
  main := P.main
  program l := embedStmt i (P.program l)

noncomputable def liftCfg (i : K ↪ L) {A : Type} (T : L → List Bool)
    (c : TM2.Cfg (fun _ : K=>Bool) A (Option Bool)) :
    TM2.Cfg (fun _ : L=>Bool) A (Option Bool) :=
  ⟨c.l,c.var,liftStacks i c.stk T⟩

lemma embedStmt_stepAux (i : K ↪ L) {A : Type}
    (q : TM2.Stmt (fun _ : K=>Bool) A (Option Bool)) (v : Option Bool)
    (S : K → List Bool) (T : L → List Bool) :
    TM2.stepAux (embedStmt i q) v (liftStacks i S T) = liftCfg i T (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => simpa [embedStmt,TM2.stepAux,liftStacks_update] using ih v (Function.update S k (f v::S k))
  | pop k f q ih => simpa [embedStmt,TM2.stepAux,liftStacks_update] using ih (f v (S k).head?) (Function.update S k (S k).tail)
  | peek k f q ih => simpa [embedStmt,TM2.stepAux] using ih (f v (S k).head?) S
  | load f q ih => exact ih (f v) S
  | branch f q r iq ir => cases hf : f v <;> simp [embedStmt,TM2.stepAux,hf,iq,ir]
  | goto f => rfl
  | halt => rfl

lemma embed_step (i : K ↪ L) (P : Code K) (T : L → List Bool)
    (c c' : P.Cfg) (h : P.step c=some c') :
    (P.embed i).step (liftCfg i T c)=some (liftCfg i T c') := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [step,TM2.step] at h
  | some l =>
    change some (TM2.stepAux (P.program l) v S)=some c' at h
    have hh := Option.some.inj h
    subst c'
    change some (TM2.stepAux (embedStmt i (P.program l)) v (liftStacks i S T))=_
    rw [embedStmt_stepAux]

/-- Executions of a subprogram preserve the entire ambient stack frame. -/
theorem embed_exec (i : K ↪ L) (P : Code K) (T : L → List Bool)
    {d e : Data K} {m : ℕ} (h : P.Exec d e m) :
    (P.embed i).Exec (d.1,liftStacks i d.2 T) (e.1,liftStacks i e.2 T) m := by
  obtain ⟨h⟩ := h
  have hs := successful_iterate_simulation P.step (P.embed i).step
    (liftCfg i T) (embed_step i P T) h.steps (P.start d) (P.halt e) h.evals_in_steps
  exact ⟨{ steps := h.steps, evals_in_steps := hs, steps_le_m := h.steps_le_m }⟩

@[simp] lemma liftStacks_project (i : K ↪ L) (S : L → List Bool) :
    liftStacks i (S ∘ i) S=S := by
  classical
  funext l
  by_cases h : ∃ k,i k=l
  · obtain ⟨k,rfl⟩ := h
    simp
  · simp [liftStacks,h]

/-- Apply a subprogram with a single output register inside an arbitrary ambient frame. -/
theorem embed_exec_update (i : K ↪ L) (P : Code K) (S : L → List Bool)
    (v w : Option Bool) (k : K) (s : List Bool) (m : ℕ)
    (h : P.Exec (v,S ∘ i) (w,Function.update (S ∘ i) k s) m) :
    (P.embed i).Exec (v,S) (w,Function.update S (i k) s) m := by
  have hh := embed_exec i P S h
  simpa only [liftStacks_update,liftStacks_project] using hh

end QMAPerfectCompleteness.Uniformity.StructuredStack.Code


