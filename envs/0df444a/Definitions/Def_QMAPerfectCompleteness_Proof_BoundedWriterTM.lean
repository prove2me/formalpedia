-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_BoundedWriterTM
-- name    : QMAPerfectCompleteness_Proof_BoundedWriterTM
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:06:34.476146+00:00
-- url     : https://prove2.me/theorems/95e1f706-05bb-4e1d-97bd-177b1d43f885
-- title:
--   Finite writers for ascending and descending bounded loops
-- statement:
--   Given a unary evaluator for a bound $n$ and a writer body indexed by $j$, constructs finite-machine writers that traverse the indices from zero to $n-1$, or in reverse order. The index is an additional read-only input; loop counters and work stacks are cleared on return, and time and output bounds remain polynomial.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/BoundedWriterTM.lean, lines 13–249.

/- Generated from Solutions.BoundedWriterTM by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_CountedWriterLoops
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_StackEmbedding
import Definitions.Def_QMAPerfectCompleteness_Proof_StackTransfers
import Definitions.Def_QMAPerfectCompleteness_Proof_StreamWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_StructuredStackCode
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryEvaluator
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryStackOps
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion



/-! Bounded-loop writer compilation. The loop bound is computed by a finite unary evaluator;
the body is a finite writer with one additional read-only unary loop-index input. -/
open Turing StateTransition
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Uniformity.StructuredStack
open Code
namespace Writer
variable {I X A : Type} [DecidableEq I] [DecidableEq A]
variable {encode : X → I → List Bool} {valid : X → ℕ → Prop}

def indexedEncoding (encode : X → I → List Bool) : (X × ℕ) → (I ⊕ Unit) → List Bool
  | (x,j),.inl i => encode x i
  | (_,j),.inr () => unary j

abbrev evalEmb {n N : ℕ} (i : A ↪ I) (w : Fin n ↪ Fin N) :
    (A ⊕ Fin n) ↪ WriterStacks I N where
  toFun
    | .inl a => .inl (i a)
    | .inr j => .inr (.inr (w j))
  inj' := by intro x y h; cases x <;> cases y <;> simp_all [i.injective.eq_iff,w.injective.eq_iff]

/-- Place an indexed writer into an outer frame, interpreting its extra input as a counter. -/
abbrev indexedEmb {n N : ℕ} (index : Fin N) (w : Fin n ↪ Fin N)
    (h : ∀ j,w j ≠ index) : WriterStacks (I ⊕ Unit) n ↪ WriterStacks I N where
  toFun
    | .inl (.inl i) => .inl i
    | .inl (.inr ()) => .inr (.inr index)
    | .inr (.inl ()) => .inr (.inl ())
    | .inr (.inr j) => .inr (.inr (w j))
  inj' := by
    intro x y he
    rcases x with (i|u|w₁) <;> rcases y with (j|v|w₂)
    all_goals try (cases i <;> cases j <;> simp_all)
    all_goals try (cases i <;> simp_all)
    all_goals try (cases j <;> simp_all)
    all_goals simp_all [w.injective.eq_iff,h,Ne.symm]

lemma downWords_length (F : ℕ → List Bool) (n M : ℕ)
    (h : ∀ j<n,(F j).length≤M) : (downWords F n).length≤n*M := by
  induction n with
  | zero => simp [downWords]
  | succ n ih =>
    simp only [downWords,List.length_append,Nat.succ_mul]
    exact (Nat.add_le_add (h n (by omega)) (ih (by intro j hj; exact h j (by omega)))).trans (by omega)

/-- Execute n−1,…,0 using a finite unary evaluator and a finite indexed body writer. -/
noncomputable def forDown {n : (A → ℕ) → ℕ} (E : Evaluator A n)
    (read : A ↪ I) (values : X → A → ℕ)
    (hread : ∀ x a,encode x (read a)=unary (values x a))
    (hvalues : ∀ x B,valid x B → ∀ a,values x a≤B)
    {innerValid : (X × ℕ) → ℕ → Prop} {f : (X × ℕ) → List Bool}
    (W : Writer (I ⊕ Unit) (X × ℕ) (indexedEncoding encode) innerValid f)
    (R : Polynomial ℕ)
    (hvalid : ∀ x B,valid x B → ∀ j<n (values x),innerValid (x,j) (R.eval B)) :
    Writer I X encode valid (fun x=>downWords (fun j=>f (x,j)) (n (values x))) := by
  let total := E.slots+W.slots
  let ei : (A ⊕ Fin E.slots) ↪ WriterStacks I total :=
    evalEmb read (Evaluator.block E.slots 0 total (by omega))
  let counter : Fin total := Evaluator.block E.slots 0 total (by omega) E.result
  let wi : Fin W.slots ↪ Fin total := Evaluator.block W.slots E.slots total (by omega)
  have hwi : ∀ j,wi j ≠ counter := by
    intro j he
    have hh := congrArg Fin.val he
    have := E.result.isLt
    change E.slots+j.val=0+E.result.val at hh
    omega
  let bi := indexedEmb (I := I) counter wi hwi
  let body := W.code.embed bi
  let c : WriterStacks I total := .inr (.inr counter)
  let Q : Polynomial ℕ := Polynomial.C E.growth*(Polynomial.X+1)
  let T : Polynomial ℕ := W.time.comp R
  let program := Code.seq (E.code.embed ei) (Code.countDown c body)
  refine { slots := total, code := program, time := Polynomial.C E.cost*(Polynomial.X+1)+Q*(T+2)+1, size := Q*(W.size.comp R), length_bound := ?_, run := ?_ }
  · intro x B hx
    have hl := downWords_length (fun j=>f (x,j)) (n (values x)) (W.size.eval (R.eval B))
      (by intro j hj; exact W.length_bound (x,j) (R.eval B) (hvalid x B hx j hj))
    have hn := E.bound (values x) B (hvalues x B hx)
    have hm := Nat.mul_le_mul_right (W.size.eval (R.eval B)) hn
    simpa only [Q,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_comp] using hl.trans hm
  · intro x B hx S q hin hw
    let bound := n (values x)
    have he₀ := E.run (values x) B (hvalues x B hx) (S ∘ ei) q
      (by intro a; simpa [ei,evalEmb,hread] using hin (read a))
      (by intro w; exact hw _)
    have he := Code.embed_exec_update ei E.code S q none (.inr E.result) (unary bound) _ he₀
    have hepos : ei (.inr E.result)=c := by rfl
    rw [hepos] at he
    have hbody : ∀ j bits v,j<bound →
        body.Exec (v,downStore S c writerOutput j bits)
          (none,downStore S c writerOutput j ((f (x,j)).reverse++bits)) (T.eval B) := by
      intro j bits v hj
      let S₀ := downStore S c writerOutput j bits
      have hinput : ∀ a,(S₀ ∘ bi) (.inl a)=indexedEncoding encode (x,j) a := by
        intro a
        cases a with
        | inl a => simpa [S₀,downStore,c,bi,indexedEmb,indexedEncoding] using hin a
        | inr a => cases a; simp [S₀,downStore,c,bi,indexedEmb,indexedEncoding]
      have hwork : ∀ w,(S₀ ∘ bi) (.inr (.inr w))=[] := by
        intro w
        have hn : (wi w : Fin total) ≠ counter := hwi w
        simpa [S₀,downStore,c,bi,indexedEmb,hn] using hw (wi w)
      have hb := Code.embed_exec_update bi W.code S₀ v none writerOutput _ _
        (W.run (x,j) (R.eval B) (hvalid x B hx j hj) (S₀ ∘ bi) v hinput hwork)
      change body.Exec (v,S₀)
        (none,Function.update S₀ writerOutput ((f (x,j)).reverse++S₀ writerOutput))
        (W.time.eval (R.eval B)) at hb
      have hs : Function.update S₀ writerOutput ((f (x,j)).reverse++S₀ writerOutput) =
          downStore S c writerOutput j ((f (x,j)).reverse++bits) := by
        simp [S₀,downStore,bi,indexedEmb,writerOutput]
      rw [hs] at hb
      simpa only [T,Polynomial.eval_comp] using hb
    have hio : c ≠ (writerOutput : WriterStacks I total) := by simp [c,writerOutput]
    have hlo := Code.countDown_exec c writerOutput hio body S (fun j=>f (x,j))
      (T.eval B) bound hbody bound (S writerOutput) none le_rfl
    have hstart : downStore S c writerOutput bound (S writerOutput)=Function.update S c (unary bound) := by
      funext k
      by_cases hk : k=writerOutput <;> simp_all [downStore,hio,Ne.symm hio]
    rw [hstart] at hlo
    have hend : downStore S c writerOutput 0
        ((downWords (fun j=>f (x,j)) bound).reverse++S writerOutput) =
        Function.update S writerOutput ((downWords (fun j=>f (x,j)) bound).reverse++S writerOutput) := by
      funext k
      by_cases hk : k=c <;> by_cases ho : k=writerOutput <;> simp_all [downStore,c,hw]
    rw [hend] at hlo
    have hh := Code.seq_exec _ _ he hlo
    apply Code.exec_mono _ hh
    have hn := E.bound (values x) B (hvalues x B hx)
    simp only [Q,T,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
    dsimp [bound] at *
    nlinarith

lemma upWords_length (F : ℕ → List Bool) (n j M limit : ℕ)
    (h : ∀ k<limit,(F k).length≤M) (hj : j+n≤limit) : (upWords F j n).length≤n*M := by
  induction n generalizing j with
  | zero => simp [upWords]
  | succ n ih =>
    simp only [upWords,List.length_append,Nat.succ_mul]
    have ht := ih (j+1) (by omega)
    have hh := h j (by omega)
    omega

/-- Execute 0,…,n−1 with two unary counters; clear both counters on return. -/
noncomputable def forUp {n : (A → ℕ) → ℕ} (E : Evaluator A n)
    (read : A ↪ I) (values : X → A → ℕ)
    (hread : ∀ x a,encode x (read a)=unary (values x a))
    (hvalues : ∀ x B,valid x B → ∀ a,values x a≤B)
    {innerValid : (X × ℕ) → ℕ → Prop} {f : (X × ℕ) → List Bool}
    (W : Writer (I ⊕ Unit) (X × ℕ) (indexedEncoding encode) innerValid f)
    (R : Polynomial ℕ)
    (hvalid : ∀ x B,valid x B → ∀ j<n (values x),innerValid (x,j) (R.eval B)) :
    Writer I X encode valid (fun x=>upWords (fun j=>f (x,j)) 0 (n (values x))) := by
  let total := E.slots+W.slots+1
  let ework := Evaluator.block E.slots 0 total (by omega)
  let ei : (A ⊕ Fin E.slots) ↪ WriterStacks I total := evalEmb read ework
  let counter : Fin total := ework E.result
  let index : Fin total := ⟨total-1,by omega⟩
  let wi : Fin W.slots ↪ Fin total := Evaluator.block W.slots E.slots total (by omega)
  have hwi : ∀ j,wi j ≠ index := by
    intro j he
    have hh := congrArg Fin.val he
    have := j.isLt
    change E.slots+j.val=total-1 at hh
    dsimp [total] at hh
    omega
  let bi := indexedEmb (I := I) index wi hwi
  let body := W.code.embed bi
  let c : WriterStacks I total := .inr (.inr counter)
  let idx : WriterStacks I total := .inr (.inr index)
  have hci : c ≠ idx := by
    intro he
    have hh := congrArg (fun z : WriterStacks I total=>match z with |.inr (.inr j)=>j.val|_=>0) he
    have := E.result.isLt
    change 0+E.result.val=total-1 at hh
    dsimp [total] at hh
    omega
  have hco : c ≠ (writerOutput : WriterStacks I total) := by simp [c,writerOutput]
  have hio : idx ≠ (writerOutput : WriterStacks I total) := by simp [idx,writerOutput]
  let Q : Polynomial ℕ := Polynomial.C E.growth*(Polynomial.X+1)
  let T : Polynomial ℕ := W.time.comp R
  let program := Code.seq (E.code.embed ei) (Code.seq (Code.countUp c idx body) (Code.clear idx))
  refine { slots := total, code := program, time := Polynomial.C E.cost*(Polynomial.X+1)+Q*(T+5)+2, size := Q*(W.size.comp R), length_bound := ?_, run := ?_ }
  · intro x B hx
    have hl := upWords_length (fun j=>f (x,j)) (n (values x)) 0 (W.size.eval (R.eval B)) (n (values x))
      (by intro j hj; exact W.length_bound (x,j) (R.eval B) (hvalid x B hx j hj)) (by omega)
    have hn := E.bound (values x) B (hvalues x B hx)
    have hm := Nat.mul_le_mul_right (W.size.eval (R.eval B)) hn
    simpa only [Q,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_comp] using hl.trans hm
  · intro x B hx S q hin hw
    let bound := n (values x)
    have he₀ := E.run (values x) B (hvalues x B hx) (S ∘ ei) q
      (by intro a; simpa [ei,evalEmb,hread] using hin (read a)) (by intro w; exact hw _)
    have he := Code.embed_exec_update ei E.code S q none (.inr E.result) (unary bound) _ he₀
    have hepos : ei (.inr E.result)=c := by rfl
    rw [hepos] at he
    have hbody : ∀ j r bits v,j<bound →
        body.Exec (v,loopStore S c idx writerOutput r j bits)
          (none,loopStore S c idx writerOutput r j ((f (x,j)).reverse++bits)) (T.eval B) := by
      intro j r bits v hj
      let S₀ := loopStore S c idx writerOutput r j bits
      have hinput : ∀ a,(S₀ ∘ bi) (.inl a)=indexedEncoding encode (x,j) a := by
        intro a
        cases a with
        | inl a => simpa [S₀,loopStore,c,idx,bi,indexedEmb,indexedEncoding] using hin a
        | inr a => cases a; simp [S₀,loopStore,c,idx,bi,indexedEmb,indexedEncoding]
      have hwork : ∀ w,(S₀ ∘ bi) (.inr (.inr w))=[] := by
        intro w
        have hnc : wi w ≠ counter := by
          intro hh
          have hv := congrArg Fin.val hh
          have := E.result.isLt
          change E.slots+w.val=0+E.result.val at hv
          omega
        have hni := hwi w
        simpa [S₀,loopStore,c,idx,bi,indexedEmb,hnc,hni] using hw (wi w)
      have hb := Code.embed_exec_update bi W.code S₀ v none writerOutput _ _
        (W.run (x,j) (R.eval B) (hvalid x B hx j hj) (S₀ ∘ bi) v hinput hwork)
      change body.Exec (v,S₀)
        (none,Function.update S₀ writerOutput ((f (x,j)).reverse++S₀ writerOutput))
        (W.time.eval (R.eval B)) at hb
      have hs : Function.update S₀ writerOutput ((f (x,j)).reverse++S₀ writerOutput) =
          loopStore S c idx writerOutput r j ((f (x,j)).reverse++bits) := by
        simp [S₀,loopStore,writerOutput]
      rw [hs] at hb
      simpa only [T,Polynomial.eval_comp] using hb
    have hlo := Code.countUp_exec c idx writerOutput hci hco hio body S (fun j=>f (x,j))
      (T.eval B) bound hbody bound 0 (S writerOutput) none (by omega)
    have hstart : loopStore S c idx writerOutput bound 0 (S writerOutput)=Function.update S c (unary bound) := by
      funext k
      by_cases hc : k=c <;> by_cases hi : k=idx <;> by_cases ho : k=writerOutput <;>
        simp_all [loopStore,idx,hw]
    rw [hstart] at hlo
    simp only [Nat.zero_add] at hlo
    let finalBits := (upWords (fun j=>f (x,j)) 0 bound).reverse++S writerOutput
    let S₁ := loopStore S c idx writerOutput 0 bound finalBits
    have hclear := Code.clear_exec idx (unary bound) S₁ none (by simp [S₁,loopStore,hio])
    have hend : Function.update S₁ idx []=Function.update S writerOutput finalBits := by
      funext k
      by_cases hc : k=c <;> by_cases hi : k=idx <;> by_cases ho : k=writerOutput <;>
        simp_all [S₁,loopStore,c,idx,hw]
    rw [hend] at hclear
    simp only [unary,List.length_replicate] at hclear
    have hh := Code.seq_exec _ _ he (Code.seq_exec _ _ hlo hclear)
    apply Code.exec_mono _ hh
    have hn := E.bound (values x) B (hvalues x B hx)
    simp only [Q,T,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
    dsimp [bound] at *
    nlinarith

end Writer
end QMAPerfectCompleteness.Uniformity.StructuredStack


