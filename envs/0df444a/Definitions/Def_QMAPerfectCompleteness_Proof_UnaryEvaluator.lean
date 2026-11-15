-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_UnaryEvaluator
-- name    : QMAPerfectCompleteness_Proof_UnaryEvaluator
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:00:58.137659+00:00
-- url     : https://prove2.me/theorems/4d3180fb-6ef8-4cc4-9a7a-6c0fbb095cc5
-- title:
--   Linear-time unary arithmetic evaluators
-- statement:
--   Defines a finite evaluator interface and constructions for inputs, constants, addition, truncated subtraction, fixed scaling, halving and conditional choice. Embedded evaluation and field emission preserve read-only inputs, clear workspace and provide linear unary runtime and value bounds.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/UnaryEvaluator.lean, retained declaration span lines 11–354.

/- Generated from Solutions.UnaryEvaluator by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_StackEmbedding
import Definitions.Def_QMAPerfectCompleteness_Proof_StackTransfers
import Definitions.Def_QMAPerfectCompleteness_Proof_StructuredStackCode
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryStackOps
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion



/-! Finite, linear-time evaluators for the unary address arithmetic used in circuit recipes. -/
open Turing StateTransition
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Uniformity.StructuredStack
open Code
variable {A : Type} [DecidableEq A]

/-- Read-only unary inputs, a finite clean workspace, and one unary result register. -/
structure Evaluator (A : Type) [DecidableEq A] (f : (A → ℕ) → ℕ) where
  slots : ℕ
  result : Fin slots
  code : Code (A ⊕ Fin slots)
  cost : ℕ
  growth : ℕ
  bound : ∀ (v : A → ℕ) (B : ℕ), (∀ a,v a ≤ B) → f v ≤ growth*(B+1)
  run : ∀ (v : A → ℕ) (B : ℕ) (hv : ∀ a,v a ≤ B)
    (S : (A ⊕ Fin slots) → List Bool) (q : Option Bool)
    (hin : ∀ a,S (.inl a)=unary (v a)) (hwork : ∀ w,S (.inr w)=[]),
    code.Exec (q,S) (none,Function.update S (.inr result) (unary (f v))) (cost*(B+1))

namespace Evaluator

noncomputable def literal (n : ℕ) : Evaluator A (fun _=>n) where
  slots := 1
  result := 0
  code := Code.seq (Code.constant (.inr 0) n) (Code.load none)
  cost := 2
  growth := n+1
  bound v B hv := by nlinarith
  run v B hv S q hin hw := by
    have h₁ := Code.constant_exec (.inr (0 : Fin 1)) n q S
    have h₂ := Code.load_exec none (q,Function.update S (.inr (0 : Fin 1)) (unary n))
    have hh := Code.seq_exec _ _ (by simpa [hw] using h₁) h₂
    exact Code.exec_mono _ hh (by omega)

noncomputable def input (a : A) : Evaluator A (fun v=>v a) where
  slots := 2
  result := 0
  code := Code.copy (.inl a) (.inr 0) (.inr 1)
  cost := 6
  growth := 1
  bound v B hv := by simpa using (hv a).trans (Nat.le_succ B)
  run v B hv S q hin hw := by
    have hh := Code.copy_exec (.inl a) (.inr (0 : Fin 2)) (.inr (1 : Fin 2))
      (by simp) (by simp) (by simp) (unary (v a)) S q (hin a) (hw 1)
    apply Code.exec_mono _ (by simpa [hw,unary] using hh)
    simpa only [unary,List.length_replicate] using
      (show 4*(v a)+2 ≤ 6*(B+1) by have := hv a; omega)

abbrev leftEmb (n m : ℕ) : (A ⊕ Fin n) ↪ (A ⊕ Fin (n+m)) where
  toFun
    | .inl a => .inl a
    | .inr j => .inr (j.castAdd m)
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all [Fin.ext_iff]

abbrev rightEmb (n m : ℕ) : (A ⊕ Fin m) ↪ (A ⊕ Fin (n+m)) where
  toFun
    | .inl a => .inl a
    | .inr j => .inr (j.natAdd n)
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all [Fin.ext_iff]

lemma left_right_ne {n m : ℕ} (j : Fin n) (k : Fin m) :
    (Sum.inr (j.castAdd m) : A ⊕ Fin (n+m)) ≠ .inr (k.natAdd n) := by
  intro h
  have hh := congrArg (fun z : A ⊕ Fin (n+m)=>match z with |.inl _=>0|.inr z=>z.val) h
  have := j.isLt
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hh
  omega

noncomputable def binaryCode {f g : (A → ℕ) → ℕ} (E : Evaluator A f) (F : Evaluator A g) (add : Bool) :
    Code (A ⊕ Fin (E.slots+F.slots)) :=
  Code.seq (E.code.embed (leftEmb E.slots F.slots))
    (Code.seq (F.code.embed (rightEmb E.slots F.slots))
      (if add then Code.transfer (.inr (F.result.natAdd E.slots)) (.inr (E.result.castAdd F.slots))
       else Code.subtract (.inr (F.result.natAdd E.slots)) (.inr (E.result.castAdd F.slots))))

/-- Addition and truncated subtraction require only one pass through the second operand. -/
noncomputable def binary {f g : (A → ℕ) → ℕ} (E : Evaluator A f) (F : Evaluator A g) (add : Bool) :
    Evaluator A (fun v=>if add then f v+g v else f v-g v) where
  slots := E.slots+F.slots
  result := E.result.castAdd F.slots
  code := binaryCode E F add
  cost := E.cost+F.cost+2*F.growth+1
  growth := E.growth+F.growth
  bound v B hv := by
    have he := E.bound v B hv
    have hf := F.bound v B hv
    have hs := Nat.sub_le (f v) (g v)
    cases add <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> nlinarith
  run v B hv S q hin hw := by
    let e : A ⊕ Fin (E.slots+F.slots) := .inr (E.result.castAdd F.slots)
    let f' : A ⊕ Fin (E.slots+F.slots) := .inr (F.result.natAdd E.slots)
    have hef : e ≠ f' := left_right_ne E.result F.result
    let S₁ := Function.update S e (unary (f v))
    let S₂ := Function.update S₁ f' (unary (g v))
    have he₀ := E.run v B hv (S ∘ leftEmb E.slots F.slots) q
      (fun a=>hin a) (fun w=>hw (w.castAdd F.slots))
    have he := Code.embed_exec_update (leftEmb E.slots F.slots) E.code S q none
      (.inr E.result) (unary (f v)) (E.cost*(B+1)) he₀
    have hf₀ := F.run v B hv (S₁ ∘ rightEmb E.slots F.slots) none
      (by intro a; simpa [S₁,e] using hin a)
      (by
        intro w
        have hn := left_right_ne (A := A) E.result w
        simpa [S₁,e,rightEmb,Ne.symm hn] using hw (w.natAdd E.slots))
    have hf := Code.embed_exec_update (rightEmb E.slots F.slots) F.code S₁ none none
      (.inr F.result) (unary (g v)) (F.cost*(B+1)) hf₀
    have hfval : S₂ f'=unary (g v) := by simp [S₂]
    have heval : S₂ e=unary (f v) := by simp [S₂,S₁,hef]
    have hfinal : Function.update (Function.update S₂ f' []) e
        (unary (if add then f v+g v else f v-g v)) =
        Function.update S e (unary (if add then f v+g v else f v-g v)) := by
      funext k
      by_cases hke : k=e <;> by_cases hkf : k=f' <;>
        simp_all [S₂,S₁,e,f']
    have hop : (if add then Code.transfer f' e else Code.subtract f' e).Exec
        (none,S₂) (none,Function.update S e (unary (if add then f v+g v else f v-g v))) (2*g v+1) := by
      cases add with
      | false =>
        have hh := Code.subtract_exec f' e (Ne.symm hef) (g v) (f v) S₂ none hfval heval
        have hfina := hfinal
        simp only [Bool.false_eq_true,ite_false] at hfina
        rw [hfina] at hh
        exact hh
      | true =>
        have hh := Code.transfer_exec f' e (Ne.symm hef) (unary (g v)) S₂ none hfval
        have hsum : (unary (g v)).reverse++S₂ e=unary (f v+g v) := by
          rw [heval]
          simp only [unary,List.reverse_replicate,List.replicate_append_replicate]
          congr 1
          omega
        rw [hsum] at hh
        have hfina := hfinal
        simp only [ite_true] at hfina
        rw [hfina] at hh
        simpa only [ite_true,unary,List.length_replicate] using hh
    have hh := Code.seq_exec _ _ he (Code.seq_exec _ _ hf hop)
    apply Code.exec_mono _ hh
    have hg := F.bound v B hv
    nlinarith

/-- Unary halving consumes its operand and leaves a clean result register. -/
noncomputable def halving {f : (A → ℕ) → ℕ} (E : Evaluator A f) :
    Evaluator A (fun v=>f v/2) where
  slots := E.slots+1
  result := Fin.last E.slots
  code := Code.seq (E.code.embed (leftEmb E.slots 1))
    (Code.half (.inr (E.result.castAdd 1)) (.inr (Fin.last E.slots)))
  cost := E.cost+2*E.growth+1
  growth := E.growth
  bound v B hv := (Nat.div_le_self (f v) 2).trans (E.bound v B hv)
  run v B hv S q hin hw := by
    let e : A ⊕ Fin (E.slots+1) := .inr (E.result.castAdd 1)
    let z : A ⊕ Fin (E.slots+1) := .inr (Fin.last E.slots)
    have hez : e ≠ z := by
      have hh := left_right_ne (A := A) E.result (0 : Fin 1)
      exact hh
    let S₁ := Function.update S e (unary (f v))
    have he₀ := E.run v B hv (S ∘ leftEmb E.slots 1) q
      (fun a=>hin a) (fun w=>hw (w.castAdd 1))
    have he := Code.embed_exec_update (leftEmb E.slots 1) E.code S q none
      (.inr E.result) (unary (f v)) (E.cost*(B+1)) he₀
    have hh := Code.half_exec e z hez (f v) S₁ none (by simp [S₁])
    have hz : S₁ z=[] := by simp [S₁,Ne.symm hez,z,hw]
    rw [hz,List.append_nil] at hh
    have hfinal : Function.update (Function.update S₁ e []) z (unary (f v/2)) =
        Function.update S z (unary (f v/2)) := by
      funext k
      by_cases hke : k=e <;> by_cases hkz : k=z <;> simp_all [S₁,e,hw]
    rw [hfinal] at hh
    have htotal := Code.seq_exec _ _ he hh
    apply Code.exec_mono _ htotal
    have hb := E.bound v B hv
    nlinarith

/-- Changing only the presentation of a function leaves its evaluator unchanged. -/
noncomputable def cast {f g : (A → ℕ) → ℕ} (h : f=g) (E : Evaluator A f) : Evaluator A g := h ▸ E

noncomputable def scaling {f : (A → ℕ) → ℕ} (E : Evaluator A f) :
    (n : ℕ) → Evaluator A (fun v=>n*f v)
  | 0 => cast (by funext v; simp) (literal 0)
  | n+1 => cast (by funext v; simp [Nat.succ_mul,Nat.add_comm])
      (binary E (scaling E n) true)

abbrev slotsEmb {n N : ℕ} (i : Fin n ↪ Fin N) : (A ⊕ Fin n) ↪ (A ⊕ Fin N) where
  toFun := Sum.map id i
  inj' := by intro x y h; cases x <;> cases y <;> simp_all [i.injective.eq_iff]

abbrev block (n start N : ℕ) (h : start+n ≤ N) : Fin n ↪ Fin N where
  toFun j := ⟨start+j.val,by have := j.isLt; omega⟩
  inj' := by intro j k h; apply Fin.ext; have := congrArg Fin.val h; simp_all

theorem runIn {f : (A → ℕ) → ℕ} (E : Evaluator A f) {N : ℕ}
    (i : Fin E.slots ↪ Fin N) (v : A → ℕ) (B : ℕ) (hv : ∀ a,v a≤B)
    (S : (A ⊕ Fin N) → List Bool) (q : Option Bool)
    (hin : ∀ a,S (.inl a)=unary (v a)) (hw : ∀ w,S (.inr (i w))=[]) :
    (E.code.embed (slotsEmb i)).Exec (q,S)
      (none,Function.update S (.inr (i E.result)) (unary (f v))) (E.cost*(B+1)) := by
  exact Code.embed_exec_update (slotsEmb i) E.code S q none (.inr E.result) _ _
    (E.run v B hv (S ∘ slotsEmb i) q hin hw)

noncomputable def branchCode {f : (A → ℕ) → ℕ} (E : Evaluator A f) {N : ℕ}
    (i : Fin E.slots ↪ Fin N) (condition output : A ⊕ Fin N) : Code (A ⊕ Fin N) :=
  Code.seq (Code.clear condition) (Code.seq (E.code.embed (slotsEmb i))
    (Code.transfer (.inr (i E.result)) output))

/-- A chosen branch clears its predicate, evaluates its expression and transfers its result. -/
theorem branch_run {f : (A → ℕ) → ℕ} (E : Evaluator A f) {N : ℕ}
    (i : Fin E.slots ↪ Fin N) (condition output : A ⊕ Fin N)
    (hne : (.inr (i E.result) : A ⊕ Fin N) ≠ output)
    (v : A → ℕ) (B : ℕ) (hv : ∀ a,v a≤B)
    (S : (A ⊕ Fin N) → List Bool) (q : Option Bool) (n : ℕ)
    (hin : ∀ a,S (.inl a)=unary (v a)) (hw : ∀ w,S (.inr (i w))=[])
    (hc : S condition=[]) (ho : S output=[]) :
    (branchCode E i condition output).Exec (q,Function.update S condition (unary n))
      (none,Function.update S output (unary (f v)))
      ((2*n+1)+(E.cost*(B+1)+(2*f v+1))) := by
  let S₀ := Function.update S condition (unary n)
  have hclear := Code.clear_exec condition (unary n) S₀ q (by simp [S₀])
  have heq : Function.update S₀ condition []=S := by
    funext k
    by_cases hk : k=condition <;> simp_all [S₀]
  rw [heq] at hclear
  simp only [unary,List.length_replicate] at hclear
  have he := E.runIn i v B hv S none hin hw
  let S₁ := Function.update S (.inr (i E.result)) (unary (f v))
  have ht := Code.transfer_exec (.inr (i E.result)) output hne (unary (f v)) S₁ none (by simp [S₁])
  have ho₁ : S₁ output=[] := by simp [S₁,Ne.symm hne,ho]
  rw [ho₁,List.append_nil] at ht
  simp only [unary,List.reverse_replicate,List.length_replicate] at ht
  have heq₁ : Function.update (Function.update S₁ (.inr (i E.result)) []) output
      (List.replicate (f v) true)=Function.update S output (unary (f v)) := by
    funext k
    by_cases hkg : k=.inr (i E.result) <;> by_cases hko : k=output <;>
      simp_all [S₁,hw,unary]
  rw [heq₁] at ht
  exact Code.seq_exec _ _ hclear (Code.seq_exec _ _ he ht)

noncomputable def nonzero {f g h : (A → ℕ) → ℕ}
    (C : Evaluator A f) (Y : Evaluator A g) (N : Evaluator A h) :
    Evaluator A (fun v=>if f v=0 then h v else g v) := by
  let total := C.slots+Y.slots+N.slots+1
  let ic := block C.slots 0 total (by omega)
  let iy := block Y.slots C.slots total (by omega)
  let inn := block N.slots (C.slots+Y.slots) total (by omega)
  let z : Fin total := ⟨total-1,by omega⟩
  let c : A ⊕ Fin total := .inr (ic C.result)
  let out : A ⊕ Fin total := .inr z
  let program := Code.seq (C.code.embed (slotsEmb ic))
    (Code.ifPeek c Option.isSome (branchCode Y iy c out) (branchCode N inn c out))
  refine { slots := total, result := z, code := program, cost := C.cost+Y.cost+N.cost+2*C.growth+2*Y.growth+2*N.growth+4, growth := Y.growth+N.growth, bound := ?_, run := ?_ }
  · intro v B hv
    have hy := Y.bound v B hv
    have hn := N.bound v B hv
    split_ifs <;> nlinarith
  · intro v B hv S q hin hw
    have hc := C.runIn ic v B hv S q hin (fun w=>hw _)
    have hyne : (Sum.inr (iy Y.result) : A ⊕ Fin total) ≠ out := by
      intro hh
      have hval := congrArg (fun x : A ⊕ Fin total=>match x with |.inl _=>0|.inr j=>j.val) hh
      have := Y.result.isLt
      simp only [iy,block,out,z] at hval
      dsimp [total] at *
      omega
    have hnne : (Sum.inr (inn N.result) : A ⊕ Fin total) ≠ out := by
      intro hh
      have hval := congrArg (fun x : A ⊕ Fin total=>match x with |.inl _=>0|.inr j=>j.val) hh
      have := N.result.isLt
      simp only [inn,block,out,z] at hval
      dsimp [total] at *
      omega
    have hy := branch_run Y iy c out hyne v B hv S
      ((unary (f v)).head?) (f v) hin (fun w=>hw _) (hw _) (hw _)
    have hn := branch_run N inn c out hnne v B hv S
      ((unary (f v)).head?) (f v) hin (fun w=>hw _) (hw _) (hw _)
    have hcb := C.bound v B hv
    have hyb := Y.bound v B hv
    have hnb := N.bound v B hv
    by_cases hf : f v=0
    · have hguard : Option.isSome ((Function.update S c (unary (f v))) c).head?=false := by simp [hf]
      have hb := Code.ifPeek_false c Option.isSome (branchCode Y iy c out) (branchCode N inn c out)
        (d := (none,Function.update S c (unary (f v)))) hguard (by simpa using hn)
      have hh := Code.seq_exec _ _ hc hb
      apply Code.exec_mono _ (by simpa only [hf,ite_true] using hh)
      nlinarith
    · have hguard : Option.isSome ((Function.update S c (unary (f v))) c).head?=true := by
        cases hfv : f v with
        | zero => exact False.elim (hf hfv)
        | succ n => simp [hfv,unary,List.replicate_succ]
      have hb := Code.ifPeek_true c Option.isSome (branchCode Y iy c out) (branchCode N inn c out)
        (d := (none,Function.update S c (unary (f v)))) hguard (by simpa using hy)
      have hh := Code.seq_exec _ _ hc hb
      apply Code.exec_mono _ (by simpa only [hf,ite_false] using hh)
      nlinarith

/-- Conditional selection is compiled using unary subtraction and an actual stack branch. -/
noncomputable def lessThan {f g y n : (A → ℕ) → ℕ}
    (F : Evaluator A f) (G : Evaluator A g) (Y : Evaluator A y) (N : Evaluator A n) :
    Evaluator A (fun v=>if f v<g v then y v else n v) :=
  cast (by
    funext v
    simp only [Bool.false_eq_true,ite_false]
    by_cases hv : f v<g v
    · have hn : g v-f v ≠ 0 := by omega
      simp [hv,hn]
    · have hz : g v-f v=0 := by omega
      simp [hv,hz])
    (nonzero (binary G F false) Y N)

/-- Emit one unary field into a reversed output buffer, restoring every scratch register. -/
noncomputable def emitCode {K : Type} [DecidableEq K] {f : (A → ℕ) → ℕ}
    (E : Evaluator A f) (i : (A ⊕ Fin E.slots) ↪ K) (output : K) : Code K :=
  Code.seq (E.code.embed i)
    (Code.seq (Code.transfer (i (.inr E.result)) output) (Code.push output false))

theorem emitIn {K : Type} [DecidableEq K] {f : (A → ℕ) → ℕ}
    (E : Evaluator A f) (i : (A ⊕ Fin E.slots) ↪ K) (output : K)
    (hne : i (.inr E.result) ≠ output) (v : A → ℕ) (B : ℕ) (hv : ∀ a,v a≤B)
    (S : K → List Bool) (q : Option Bool)
    (hin : ∀ a,S (i (.inl a))=unary (v a)) (hw : ∀ w,S (i (.inr w))=[]) :
    (emitCode E i output).Exec (q,S)
      (none,Function.update S output ((QAlgorithms.Complexity.encNat (f v)).reverse++S output))
      ((E.cost+2*E.growth+2)*(B+1)) := by
  have he := Code.embed_exec_update i E.code S q none (.inr E.result) (unary (f v)) _
    (E.run v B hv (S ∘ i) q hin hw)
  let result := i (.inr E.result)
  let S₁ := Function.update S result (unary (f v))
  have ht := Code.transfer_exec result output hne (unary (f v)) S₁ none (by simp [S₁])
  have ho : S₁ output=S output := by simp [S₁,result,Ne.symm hne]
  rw [ho] at ht
  simp only [unary,List.reverse_replicate,List.length_replicate] at ht
  have hfinal : Function.update (Function.update S₁ result []) output
      (List.replicate (f v) true++S output) =
      Function.update S output (List.replicate (f v) true++S output) := by
    funext k
    by_cases hkr : k=result <;> by_cases hko : k=output <;> simp_all [S₁,result,hw]
  rw [hfinal] at ht
  have hp := Code.push_exec output false (none,Function.update S output (unary (f v)++S output))
  have hh := Code.seq_exec _ _ he (Code.seq_exec _ _ ht hp)
  have hs : Function.update (Function.update S output (unary (f v)++S output)) output
      (false::(Function.update S output (unary (f v)++S output)) output) =
      Function.update S output ((QAlgorithms.Complexity.encNat (f v)).reverse++S output) := by
    simp [QAlgorithms.Complexity.encNat,unary,List.reverse_append]
  rw [hs] at hh
  apply Code.exec_mono _ hh
  have hb := E.bound v B hv
  nlinarith

end Evaluator
end QMAPerfectCompleteness.Uniformity.StructuredStack


