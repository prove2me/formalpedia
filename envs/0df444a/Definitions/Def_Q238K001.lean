-- Prove2me | Definitions.Def_Q238K001
-- name    : Q238K001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:10:42.030258+00:00
-- url     : https://prove2.me/theorems/e247ece5-0e8b-49d3-8313-20edc461730b
-- title:
--   Definitions bundle Q238K001 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 206 declarations of OpenAI's Lean: 132 definitions, 1 inductive type or structure and 73 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BirdInteger.determinant`, `OAI.MetricKMedianRecovery.BirdInteger.freeze`, `OAI.MetricKMedianRecovery.BirdInteger.iterate`, `OAI.MetricKMedianRecovery.BirdRational.data`, `OAI.MetricKMedianRecovery.BirdRationalIteration.determinant`, `OAI.MetricKMedianRecovery.BirdRationalIteration.flat`, `OAI.MetricKMedianRecovery.BirdRationalIteration.iterate`, `OAI.MetricKMedianRecovery.BitMachine.BinaryActions.add`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.value`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.bound`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.coeffAbs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.coeffSum`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.height`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.heightSum`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.mword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.numAbs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.numAbsOp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.nword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.padRow`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.padRowOp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.paddedRows`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.prepared`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rest₁`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rest₂`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rowHeight`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rowHeightOp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rowHeights`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rows`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.factorial`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.height`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.mword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.nextDim`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.nword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.rest₁`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.rest₂`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.rest₃`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.dummy`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.indices`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.coeffs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.decisionInput` and 93 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_CopyComputes`, `KMedianRecovery_Encoding_Encode`, `KMedianRecovery_Encoding_Encode3`, `KMedianRecovery_Encoding_OptionEncode`, `KMedianRecovery_Encoding_PushWord`, `KMedianRecovery_Encoding_Reencode`, `KMedianRecovery_Machines_ActionMachine`, `KMedianRecovery_Machines_Program`, `KMedianRecovery_Machines_Program2`, `KMedianRecovery_Recovery_BoundOp`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_CommonDen`, `KMedianRecovery_Recovery_Copies`, `KMedianRecovery_Recovery_EvalTrans`, `KMedianRecovery_Recovery_FaceSelection`, `KMedianRecovery_Recovery_FrameStacks`, `KMedianRecovery_Recovery_Freeze`, `KMedianRecovery_Recovery_Fuel`, `KMedianRecovery_Recovery_Iterate`, `KMedianRecovery_Recovery_LeftNum`, `KMedianRecovery_Recovery_LengthPolynomial`, `KMedianRecovery_Recovery_Min`, `KMedianRecovery_Recovery_MulComputes`, `KMedianRecovery_Recovery_Op`, `KMedianRecovery_Recovery_Op2`, `KMedianRecovery_Recovery_Pack2`, `KMedianRecovery_Recovery_Pack3`, `KMedianRecovery_Recovery_Pack7`, `KMedianRecovery_Recovery_Pack9`, `KMedianRecovery_Recovery_ProcessOutputs`, `KMedianRecovery_Recovery_Rectangular`, `KMedianRecovery_Recovery_RowInput`, `KMedianRecovery_Recovery_Stack`, `KMedianRecovery_Recovery_StackLength`, `KMedianRecovery_Recovery_Step`, `KMedianRecovery_Recovery_Step2`, `KMedianRecovery_Recovery_StepThen`, `KMedianRecovery_Recovery_Value`, `KMedianRecovery_Recovery_Values`, `KMedianRecovery_Sampling_ExtractPrefix`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`.
--
--   **Imported by** (directly, in this split): the bundles `Q238K006`, `Q238K007`, `Q238K008`, `Q238K009`, `Q238K010`, `Q238K011`, `Q238K012`, `Q238K013`, `Q238K014` and `Q238K016`; the statement `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.indices_replicate_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery

section
-- module Solutions.Q238_KM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_Program
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

structure Program where
  K : Type
  [kDecidableEq : DecidableEq K]
  [kFinite : Fintype K]
  input : K
  output : K
  Label : Type
  [labelFinite : Fintype Label]
  main : Label
  State : Type
  [stateFinite : Fintype State]
  initial : State
  code : Label → TM2.Stmt (fun _ : K => Bool) Label State

attribute [instance] Program.kDecidableEq Program.kFinite Program.labelFinite Program.stateFinite

abbrev Program.machine (p : Program) : FinTM2 where
  K := p.K
  k₀ := p.input
  k₁ := p.output
  Γ _ := Bool
  Λ := p.Label
  main := p.main
  σ := p.State
  initialState := p.initial
  m := p.code

abbrev Stacks (K : Type) := K → List Bool

noncomputable def embedStacks {K L : Type} (e : K ↪ L) (s : Stacks K) : Stacks L := by
  classical
  exact fun l => if h : ∃ k, e k = l then s h.choose else []

lemma embedStacks_not_image {K L : Type} (e : K ↪ L) (s : Stacks K) (l : L)
    (h : ¬∃ k, e k = l) : embedStacks e s l = [] := by
  classical
  simp only [embedStacks,dite_eq_right h]

section Rename
variable {K L A B S T : Type} [DecidableEq K] [DecidableEq L]

def renameStmt (ek : K ↪ L) (el : A → B) (es : S → T) (rs : T → S)
    (ret : Option B) : TM2.Stmt (fun _ : K => Bool) A S → TM2.Stmt (fun _ : L => Bool) B T
  | .push k f q => .push (ek k) (fun t => f (rs t)) (renameStmt ek el es rs ret q)
  | .peek k f q => .peek (ek k) (fun t b => es (f (rs t) b)) (renameStmt ek el es rs ret q)
  | .pop k f q => .pop (ek k) (fun t b => es (f (rs t) b)) (renameStmt ek el es rs ret q)
  | .load f q => .load (fun t => es (f (rs t))) (renameStmt ek el es rs ret q)
  | .branch f q r => .branch (fun t => f (rs t))
      (renameStmt ek el es rs ret q) (renameStmt ek el es rs ret r)
  | .goto f => .goto (fun t => el (f (rs t)))
  | .halt => match ret with | none => .halt | some b => .goto (fun _ => b)

noncomputable def renameCfg (ek : K ↪ L) (el : A → B) (es : S → T)
    (ret : Option B) (c : TM2.Cfg (fun _ : K => Bool) A S) : TM2.Cfg (fun _ : L => Bool) B T :=
  ⟨c.l.elim ret (fun a => some (el a)), es c.var, embedStacks ek c.stk⟩

end Rename

lemma iterate_transfer {S T : Type} (f : S → Option S) (g : T → Option T) (e : S → T)
    (h : ∀ s s', f s = some s' → g (e s) = some (e s')) (n : ℕ) (s s' : S)
    (he : (fun x : Option S => x.bind f)^[n] (some s) = some s') :
    (fun x : Option T => x.bind g)^[n] (some (e s)) = some (e s') := by
  induction n generalizing s with
  | zero => simpa only [Function.iterate_zero_apply,Option.some.injEq] using congrArg e (Option.some.inj he)
  | succ n ih =>
    rw [Function.iterate_succ_apply] at he ⊢
    change (fun x : Option S => x.bind f)^[n] (f s) = some s' at he
    change (fun x : Option T => x.bind g)^[n] (g (e s)) = some (e s')
    cases hf : f s with
    | none =>
      rw [hf] at he
      have hn : (fun x : Option S => x.bind f)^[n] none = none :=
        Function.iterate_fixed rfl n
      rw [hn] at he
      contradiction
    | some t =>
      rw [h s t hf]
      exact ih t (by simpa only [hf] using he)

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Stack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

lemma embedStacks_empty {K L : Type} (e : K ↪ L) :
    embedStacks e (fun _ => []) = fun _ => [] := by
  classical
  funext l
  simp only [embedStacks]
  split <;> rfl

lemma initList_bool (p : Program) (bits : List Bool) :
    initList p.machine bits = ⟨some p.main,p.initial,Function.update (fun _ => []) p.input bits⟩ := by
  unfold initList
  congr 1
  funext k
  simp only [Program.machine,Function.update_apply]
  split <;> rfl

lemma haltList_bool (p : Program) (bits : List Bool) :
    haltList p.machine bits = ⟨none,p.initial,Function.update (fun _ => []) p.output bits⟩ := by
  unfold haltList
  congr 1
  funext k
  simp only [Program.machine,Function.update_apply]
  split <;> rfl

namespace Composition
variable (p q : Program)

abbrev Stack := p.K ⊕ {k : q.K // k ≠ q.input}

def leftStack : p.K ↪ Stack p q := ⟨Sum.inl,Sum.inl_injective⟩

end Composition
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_StackLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

section Length
variable {K A S : Type} [DecidableEq K] [Fintype K]

def stackLength (stk : Stacks K) : ℕ := ∑ k, (stk k).length

def pushBound : TM2.Stmt (fun _ : K => Bool) A S → ℕ
  | .push _ _ q => pushBound q + 1
  | .peek _ _ q => pushBound q
  | .pop _ _ q => pushBound q
  | .load _ q => pushBound q
  | .branch _ q r => max (pushBound q) (pushBound r)
  | .goto _ => 0
  | .halt => 0

lemma stackLength_pure (k : K) (bits : List Bool) :
    stackLength (Function.update (fun _ => []) k bits) = bits.length := by
  simp [stackLength,Function.update_apply,apply_ite]

lemma stackLength_update_le (stk : Stacks K) (k : K) (bits : List Bool) (d : ℕ)
    (h : bits.length ≤ (stk k).length+d) :
    stackLength (Function.update stk k bits) ≤ stackLength stk + d := by
  have he : (fun j => (Function.update stk k bits j).length) =
      Function.update (fun j => (stk j).length) k bits.length := by
    funext j
    simp only [Function.update_apply]
    split <;> rfl
  unfold stackLength
  rw [he,Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hs := Finset.sum_eq_add_sum_sdiff_singleton_of_mem (s := Finset.univ)
    (f := fun j => (stk j).length) (Finset.mem_univ k)
  omega

lemma stepAux_length (stmt : TM2.Stmt (fun _ : K => Bool) A S) (s : S) (stk : Stacks K) :
    stackLength (TM2.stepAux stmt s stk).stk ≤ stackLength stk + pushBound stmt := by
  induction stmt generalizing s stk with
  | push k f q ih =>
    apply (ih s (Function.update stk k (f s :: stk k))).trans
    have hl := stackLength_update_le stk k (f s :: stk k) 1 (by simp)
    change _ ≤ _ + (pushBound q+1)
    omega
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    apply (ih _ (Function.update stk k (stk k).tail)).trans
    have hl := stackLength_update_le stk k (stk k).tail 0 (by simp)
    change _ ≤ _ + pushBound q
    omega
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr =>
    simp only [TM2.stepAux,pushBound]
    cases hf : f s <;> simp only [Bool.cond_false,Bool.cond_true]
    · exact (ihr _ _).trans (Nat.add_le_add_left (le_max_right _ _) _)
    · exact (ihq _ _).trans (Nat.add_le_add_left (le_max_left _ _) _)
  | goto f => simp only [TM2.stepAux,pushBound,Nat.add_zero,le_refl]
  | halt => simp only [TM2.stepAux,pushBound,Nat.add_zero,le_refl]

end Length

lemma iterate_length {S : Type} (f : S → Option S) (len : S → ℕ) (c : ℕ)
    (h : ∀ s t, f s = some t → len t ≤ len s+c) (n : ℕ) (s t : S)
    (he : (fun x : Option S => x.bind f)^[n] (some s) = some t) :
    len t ≤ len s+n*c := by
  induction n generalizing s with
  | zero =>
    have ht : s = t := Option.some.inj he
    subst t
    omega
  | succ n ih =>
    rw [Function.iterate_succ_apply] at he
    change (fun x : Option S => x.bind f)^[n] (f s) = some t at he
    cases hf : f s with
    | none =>
      rw [hf,Function.iterate_fixed rfl n] at he
      contradiction
    | some u =>
      have hi := ih u (by simpa only [hf] using he)
      have hs := h s u hf
      simp only [Nat.succ_mul]
      omega

lemma polynomial_monotone (P : Polynomial ℕ) : Monotone (fun n => P.eval n) := by
  intro n m h
  simp only [Polynomial.eval_eq_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i))

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_StepThen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

noncomputable def step_then {S : Type} {f : S → Option S} {s t : S} {z : Option S} {n : ℕ}
    (h : f s = some t) (ht : EvalsToInTime f t z n) : EvalsToInTime f s z (n+1) := by
  refine ⟨⟨ht.steps+1,?_⟩,Nat.add_le_add_right ht.steps_le_m 1⟩
  rw [Function.iterate_succ_apply]
  change (fun x : Option S => x.bind f)^[ht.steps] (f s) = z
  rw [h]
  exact ht.evals_in_steps

noncomputable def time_mono {S : Type} {f : S → Option S} {s : S} {z : Option S} {m n : ℕ}
    (h : EvalsToInTime f s z m) (hm : m ≤ n) : EvalsToInTime f s z n :=
  ⟨h.toEvalsTo,h.steps_le_m.trans hm⟩

noncomputable def one_step {S : Type} {f : S → Option S} {s t : S}
    (h : f s = some t) : EvalsToInTime f s (some t) 1 :=
  ⟨⟨1,h⟩,le_rfl⟩

def discardPrefix : List Bool → List Bool
  | true :: _ :: bits => discardPrefix bits
  | true :: [] => []
  | false :: bits => bits
  | [] => []

lemma discardPrefix_pair (x y : List Bool) :
    discardPrefix (x.flatMap (fun b => [true,b]) ++ [false] ++ y) = y := by
  induction x with
  | nil => rfl
  | cons b x ih => simpa only [List.flatMap_cons,List.cons_append,List.nil_append,discardPrefix] using ih

def twoStacks (xs ys : List Bool) : Stacks Bool := fun k => cond k ys xs

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_ExtractPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

def extractPrefix : List Bool → List Bool
  | true :: b :: bits => b :: extractPrefix bits
  | _ => []

lemma extractPrefix_pair (x y : List Bool) :
    extractPrefix (x.flatMap (fun b => [true,b]) ++ [false] ++ y) = x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    simpa only [List.flatMap_cons,List.cons_append,List.nil_append,extractPrefix] using congrArg (List.cons b) ih

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FrameStacks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

def frameStacks {K L : Type} (s : Stacks K) (t : Stacks L) : Stacks (K⊕L) := Sum.elim s t

@[simp] lemma frameStacks_inl {K L : Type} (s : Stacks K) (t : Stacks L) (k : K) :
    frameStacks s t (.inl k)=s k := rfl

@[simp] lemma frameStacks_inr {K L : Type} (s : Stacks K) (t : Stacks L) (k : L) :
    frameStacks s t (.inr k)=t k := rfl

lemma frameStacks_update {K L : Type} [DecidableEq K] [DecidableEq L]
    (s : Stacks K) (t : Stacks L) (k : K) (xs : List Bool) :
    frameStacks (Function.update s k xs) t = Function.update (frameStacks s t) (.inl k) xs := by
  funext i
  cases i <;> simp [frameStacks,Function.update_apply]

lemma stepAux_frame {K L A B S T : Type} [DecidableEq K] [DecidableEq L]
    (el : A → B) (es : S → T) (rs : T → S) (h : ∀ s,rs (es s)=s)
    (ret : Option B) (q : TM2.Stmt (fun _ : K => Bool) A S)
    (s : S) (stk : Stacks K) (extra : Stacks L) :
    TM2.stepAux (renameStmt (Function.Embedding.inl) el es rs ret q) (es s)
      (frameStacks stk extra) =
    ⟨(TM2.stepAux q s stk).l.elim ret (fun a => some (el a)),
      es (TM2.stepAux q s stk).var,frameStacks (TM2.stepAux q s stk).stk extra⟩ := by
  induction q generalizing s stk with
  | push k f q ih =>
    simpa only [renameStmt,TM2.stepAux,h,Function.Embedding.inl_apply,frameStacks_inl,
      ←frameStacks_update] using ih s (Function.update stk k (f s::stk k))
  | peek k f q ih =>
    simpa only [renameStmt,TM2.stepAux,h,Function.Embedding.inl_apply,frameStacks_inl] using
      ih (f s (stk k).head?) stk
  | pop k f q ih =>
    simpa only [renameStmt,TM2.stepAux,h,Function.Embedding.inl_apply,frameStacks_inl,
      ←frameStacks_update] using ih (f s (stk k).head?) (Function.update stk k (stk k).tail)
  | load f q ih => simpa only [renameStmt,TM2.stepAux,h] using ih (f s) stk
  | branch f q r ihq ihr =>
    simp only [renameStmt,TM2.stepAux,h]
    cases f s <;> simp only [Bool.cond_false,Bool.cond_true]
    · exact ihr _ _
    · exact ihq _ _
  | goto f => simp only [renameStmt,TM2.stepAux,h,Option.elim_some]
  | halt => cases ret <;> rfl

lemma extractPrefix_length (bits : List Bool) : (extractPrefix bits).length≤bits.length := by
  induction bits using List.twoStepInduction with
  | nil => simp [extractPrefix]
  | singleton b => cases b <;> simp [extractPrefix]
  | cons_cons b c bits ih _ =>
    cases b <;> simp only [extractPrefix,List.length_cons,List.length_nil] <;> omega

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_EvalTrans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
noncomputable def eval_trans {S : Type} {f : S → Option S} {s t : S} {z : Option S} {m n : ℕ}
    (h1 : EvalsToInTime f s (some t) m) (h2 : EvalsToInTime f t z n) : EvalsToInTime f s z (n+m) := by
  refine ⟨⟨h2.steps+h1.steps,?_⟩,Nat.add_le_add h2.steps_le_m h1.steps_le_m⟩
  change (fun s : Option S => s.bind f)^[h2.steps+h1.steps] (some s) = z
  have e1 : (fun s : Option S => s.bind f)^[h1.steps] (some s) = some t := h1.evals_in_steps
  have e2 : (fun s : Option S => s.bind f)^[h2.steps] (some t) = z := h2.evals_in_steps
  rw [Function.iterate_add_apply,e1,e2]

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Reencode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

lemma pairBits_length (p : List Bool × List Bool) :
    (pairBits p).length = 2*p.1.length+1+p.2.length := by
  rcases p with ⟨x,y⟩
  induction x with
  | nil => simp [pairBits,Nat.add_comm]
  | cons b xs ih =>
    simp only [pairBits,List.flatMap_cons,List.cons_append,List.nil_append,List.length_cons] at ih ⊢
    omega

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

namespace BinaryArithmetic

def value : List Bool → ℕ
  | [] => 0
  | b::bs => b.toNat+2*value bs

lemma value_bits (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h,value,ih]
    cases b <;> simp [Nat.bit,Nat.add_comm]

end BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_Program2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

namespace While
variable (p : Program)

def next (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  if x.head? = some true then f x else x

end While

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_PushWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

def pushWord {K L S : Type} (k : K) : List Bool → TM2.Stmt (fun _ : K=>Bool) L S → TM2.Stmt (fun _ : K=>Bool) L S
  | [],c => c
  | b::bs,c => pushWord k bs (.push k (fun _=>b) c)

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing
namespace BinaryGCD
open BinaryArithmetic

def pack (active : Bool) (a b : List Bool) : List Bool := active::pairBits (a,b)
def first (x : List Bool) : List Bool := extractPrefix x.tail
def second (x : List Bool) : List Bool := discardPrefix x.tail
@[simp] lemma first_pack (c : Bool) (a b : List Bool) : first (pack c a b)=a :=
  extractPrefix_pair a b
@[simp] lemma second_pack (c : Bool) (a b : List Bool) : second (pack c a b)=b :=
  discardPrefix_pair a b
@[simp] lemma length_pack (c : Bool) (a b : List Bool) :
    (pack c a b).length=2*a.length+b.length+2 := by
  simp only [pack,List.length_cons,pairBits_length]
  omega

def measure (x : List Bool) : ℕ := (value (first x)).size+(value (second x)).size

@[simp] lemma measure_pack (c : Bool) (a b : List Bool) :
    measure (pack c a b)=(value a).size+(value b).size := by
  simp only [measure,first_pack,second_pack]

end BinaryGCD
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ProcessOutputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open BinaryArithmetic
namespace Signed

def encode (z : ℤ) : List Bool := decide (z<0)::z.natAbs.bits
def sign (x : List Bool) : Bool := x.head?.getD false
def mag (x : List Bool) : ℕ := value x.tail
def decode (x : List Bool) : ℤ := if sign x then -(mag x:ℤ) else (mag x:ℤ)

lemma encode_decode (z : ℤ) : decode (encode z)=z := by
  simp only [decode,sign,encode,List.head?_cons,Option.getD_some,mag,List.tail_cons,value_bits,
    decide_eq_true_eq]
  split_ifs with h
  · exact (Int.eq_neg_natAbs_of_nonpos (le_of_lt h)).symm
  · exact Int.natAbs_of_nonneg (le_of_not_gt h)

end Signed
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MulComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
namespace BinaryRational

def encode (x : ℚ) : List Bool := pairBits (Signed.encode x.num,x.den.bits)
def numerator (x : List Bool) : List Bool := extractPrefix x
def denominator (x : List Bool) : List Bool := discardPrefix x
def decode (x : List Bool) : ℚ := mkRat (Signed.decode (numerator x)) (value (denominator x))

end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeftNum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
@[simp] lemma extractPrefix_pairBits (x y : List Bool) : extractPrefix (pairBits (x,y))=x := extractPrefix_pair x y
@[simp] lemma discardPrefix_pairBits (x y : List Bool) : discardPrefix (pairBits (x,y))=y := discardPrefix_pair x y
@[simp] lemma Signed.sign_encode (z : ℤ) : Signed.sign (Signed.encode z)=decide (z<0) := rfl
namespace BinaryRational

@[simp] lemma numerator_encode (x : ℚ) : numerator (encode x)=Signed.encode x.num := extractPrefix_pair _ _
@[simp] lemma denominator_encode (x : ℚ) : denominator (encode x)=x.den.bits := discardPrefix_pair _ _
@[simp] lemma decode_pair (n : ℤ) (d : ℕ) : decode (pairBits (Signed.encode n,d.bits))=mkRat n d := by
  simp only [decode,numerator,denominator,extractPrefix_pairBits,discardPrefix_pairBits,
    Signed.encode_decode,value_bits]

def negWords (x : List Bool) : List Bool :=
  pairBits (Signed.encode (-Signed.decode (numerator x)),denominator x)

end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
namespace UnaryTake

def pack (a : Bool) (c d o : List Bool) : List Bool := a::pairBits (c,pairBits (d,o))
@[simp] lemma head_pack (a : Bool) (c d o : List Bool) : (pack a c d o).head?=some a := rfl
def counter (x : List Bool) := extractPrefix x.tail
def data (x : List Bool) := extractPrefix (discardPrefix x.tail)
def output (x : List Bool) := discardPrefix (discardPrefix x.tail)
@[simp] lemma counter_pack (a : Bool) (c d o : List Bool) : counter (pack a c d o)=c := by
  simp only [counter,pack,List.tail_cons,extractPrefix_pairBits]
@[simp] lemma data_pack (a : Bool) (c d o : List Bool) : data (pack a c d o)=d := by
  simp only [data,pack,List.tail_cons,extractPrefix_pairBits,discardPrefix_pairBits]
@[simp] lemma output_pack (a : Bool) (c d o : List Bool) : output (pack a c d o)=o := by
  simp only [output,pack,List.tail_cons,discardPrefix_pairBits]
def rank (x : List Bool) : ℕ := if x.head?=some true then (counter x).length+1 else 0

end UnaryTake
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open UnaryTake
namespace BoundedIteration

def run (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  (fun s=>(f s).take (extractPrefix (discardPrefix x)).length)^[(extractPrefix x).length]
    (discardPrefix (discardPrefix x))

end BoundedIteration
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open UnaryTake
namespace RepeatedAppend

def copies : ℕ → List Bool → List Bool
  | 0,_=>[]
  | n+1,d=>copies n d++d

end RepeatedAppend

namespace BoundedIteration

def polynomialRun (f : List Bool → List Bool) (Q R : Polynomial ℕ) (x : List Bool) : List Bool :=
  (fun s=>(f s).take (R.eval x.length))^[Q.eval x.length] x
end BoundedIteration
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open UnaryTake

namespace WordList

def cons (w ws : List Bool) : List Bool := true::pairBits (w,ws)
def encode : List (List Bool) → List Bool
  | []=>[]
  | w::ws=>cons w (encode ws)
def head (x : List Bool) : List Bool := extractPrefix x.tail
def tail (x : List Bool) : List Bool := discardPrefix x.tail
@[simp] lemma head_cons (w ws : List Bool) : head (cons w ws)=w := by
  simp only [head,cons,List.tail_cons,extractPrefix_pairBits]
@[simp] lemma tail_cons (w ws : List Bool) : tail (cons w ws)=ws := by
  simp only [tail,cons,List.tail_cons,discardPrefix_pairBits]

namespace ReverseMap

def step (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  if counter x=[] then pack false [] (data x) (output x)
  else pack true (WordList.tail (counter x)) (data x)
    (cons (f (pairBits (data x,head (counter x)))) (output x))

def next (f : List Bool → List Bool) := While.next (step f)

def run (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  let s := pack true (discardPrefix x) (extractPrefix x) []
  output ((next f)^[rank s] s)
end ReverseMap

def reverse (x : List Bool) : List Bool := ReverseMap.run discardPrefix (pairBits ([],x))
def mapWith (f : List Bool → List Bool) : List Bool → List Bool := reverse ∘ ReverseMap.run f

end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Step2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open BinaryArithmetic
namespace WordList.Lookup

def step (x : List Bool) : List Bool :=
  if value (extractPrefix x)=0 then x
  else pairBits ((value (extractPrefix x)-1).bits,WordList.tail (discardPrefix x))

def run (x : List Bool) : List Bool := WordList.head (discardPrefix (step^[x.length] x))
end WordList.Lookup
end
namespace WordList
namespace Fold

def pack (ws ctx a : List Bool) : List Bool := pairBits (ws,pairBits (ctx,a))
def items (x : List Bool) := extractPrefix x
def context (x : List Bool) := extractPrefix (discardPrefix x)
def accum (x : List Bool) := discardPrefix (discardPrefix x)
@[simp] lemma items_pack (ws ctx a : List Bool) : items (pack ws ctx a)=ws := by
  simp only [items,pack,extractPrefix_pairBits]
@[simp] lemma context_pack (ws ctx a : List Bool) : context (pack ws ctx a)=ctx := by
  simp only [context,pack,extractPrefix_pairBits,discardPrefix_pairBits]
@[simp] lemma accum_pack (ws ctx a : List Bool) : accum (pack ws ctx a)=a := by
  simp only [accum,pack,discardPrefix_pairBits]

def step (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  if items x=[] then x else pack (WordList.tail (items x)) (context x)
    (f (pairBits (context x,pairBits (WordList.head (items x),accum x))))

noncomputable def run (f : List Bool → List Bool) (R : Polynomial ℕ) : List Bool → List Bool :=
  accum ∘ BoundedIteration.polynomialRun (step f) Polynomial.X R
end Fold
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
namespace IntegerArray

def addOp (x : List Bool) : List Bool := Signed.encode
  (Signed.decode (extractPrefix (discardPrefix x))+Signed.decode (discardPrefix (discardPrefix x)))

noncomputable def sumWords (x : List Bool) : List Bool :=
  WordList.Fold.run addOp (4*Polynomial.X+4) (WordList.Fold.pack x [] (Signed.encode 0))
end IntegerArray
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open BinaryArithmetic
namespace WordList
namespace Indices

def op (x : List Bool) : List Bool :=
  let a := discardPrefix (discardPrefix x)
  pairBits ((value (extractPrefix a)+1).bits,cons (extractPrefix a) (discardPrefix a))

noncomputable def run (x : List Bool) : List Bool := reverse (discardPrefix
  (Fold.run op (20*(Polynomial.X+1)^2) (Fold.pack x [] (pairBits (Nat.bits 0,encode [])))))
end Indices
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
namespace UnaryResources
def inc (x : List Bool) : List Bool := (value x+1).bits
end UnaryResources
namespace WordList

def repeatWords (x : List Bool) : List Bool :=
  RepeatedAppend.copies (extractPrefix x).length (encode [discardPrefix x])
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Freeze
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BirdInteger
open Matrix Function
open scoped BigOperators

def freeze {R : Type*} {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  let ar := Array.ofFn (fun k : Fin (n*n) => A k.divNat k.modNat)
  Matrix.ofArray ar Array.size_ofFn

@[simp] lemma freeze_eq {R : Type*} {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : freeze A=A :=
  Matrix.ofArray_ofFn A

def iterate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : ℕ → Matrix (Fin n) (Fin n) ℤ
  | 0 => freeze A
  | t+1 => freeze (BirdDet.Spec.stepEntry A (iterate A t))

def determinant : {n : ℕ} → Matrix (Fin n) (Fin n) ℤ → ℤ
  | 0,_ => 1
  | k+1,A => (-1)^k * iterate A k 0 0

end MetricKMedianRecovery.BirdInteger

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CommonDen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BirdRational
open Matrix
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]

def data {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    (Fin n × Option (Fin n)) → ℚ := fun ⟨i,j⟩ => match j with
  | none => b i
  | some j => A i j

end MetricKMedianRecovery.BirdRational

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Iterate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BirdRationalIteration
open Matrix
open scoped BigOperators

def iterate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (t : ℕ) :=
  (BirdDet.Spec.stepEntry A)^[t] A

def flat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Fin n×Fin n → ℚ := fun p=>A p.1 p.2
def determinant : {n : ℕ} → Matrix (Fin n) (Fin n) ℚ → ℚ
  | 0, _ => 1
  | n+1, A => (-1)^n * iterate A n 0 0
end MetricKMedianRecovery.BirdRationalIteration

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_OptionEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
namespace WordList.Find

def context : List Bool → List Bool := extractPrefix
def item : List Bool → List Bool := extractPrefix ∘ discardPrefix
def accum : List Bool → List Bool := discardPrefix ∘ discardPrefix
end WordList.Find
end
open BinaryArithmetic
namespace BinaryRow
def coeff : List Bool → List Bool := extractPrefix ∘ discardPrefix
end BinaryRow
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open BinaryArithmetic
namespace BinaryEllipsoidInitial
open WordList

def dummy (u : List Bool) : List Bool := repeatWords (pairBits (u,[]))
noncomputable def indices : List Bool → List Bool := Indices.run ∘ dummy
end BinaryEllipsoidInitial
end
open BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
namespace NaturalArray
open WordList
def mulOp (x : List Bool) : List Bool :=
  (value (extractPrefix (discardPrefix x))*value (discardPrefix (discardPrefix x))).bits
noncomputable def productWords (x : List Bool) : List Bool :=
  Fold.run mulOp (4*Polynomial.X+4) (Fold.pack x [] (1:ℕ).bits)

def nextOp : List Bool → List Bool := UnaryResources.inc ∘ discardPrefix
noncomputable def factorialWords (u : List Bool) : List Bool :=
  productWords (mapWith nextOp (pairBits ([],BinaryEllipsoidInitial.indices u)))
end NaturalArray
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
namespace BinaryDecision
open UnaryResources NaturalArray

def nword : List Bool → List Bool := extractPrefix
def rest₁ : List Bool → List Bool := discardPrefix
def mword : List Bool → List Bool := extractPrefix ∘ rest₁
def rest₂ : List Bool → List Bool := discardPrefix ∘ rest₁
def rest₃ : List Bool → List Bool := discardPrefix ∘ rest₂
def height : List Bool → List Bool := extractPrefix ∘ rest₃

def nextDim (x : List Bool) : List Bool := nword x++[true]
noncomputable def factorial : List Bool → List Bool := factorialWords ∘ nextDim
end BinaryDecision
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundOp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open BinaryArithmetic
namespace NaturalArray
open WordList

def signedOp (x : List Bool) : List Bool := Signed.encode (value (discardPrefix x):ℤ)
noncomputable def sumWords (x : List Bool) : List Bool :=
  (IntegerArray.sumWords (mapWith signedOp (pairBits ([],x)))).tail
end NaturalArray
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundedDecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

namespace BinaryBoundedDecision
open BinaryArithmetic
open WordList

def nword : List Bool → List Bool := extractPrefix
def rest₁ : List Bool → List Bool := discardPrefix
def mword : List Bool → List Bool := extractPrefix ∘ rest₁
def rest₂ : List Bool → List Bool := discardPrefix ∘ rest₁
def bound : List Bool → List Bool := extractPrefix ∘ rest₂
def rows : List Bool → List Bool := discardPrefix ∘ rest₂

def numAbs (x : List Bool) : List Bool := (extractPrefix x).tail
def numAbsOp : List Bool → List Bool := numAbs ∘ discardPrefix
noncomputable def coeffAbs (x : List Bool) : List Bool := mapWith numAbsOp (pairBits ([],extractPrefix x))
noncomputable def coeffSum : List Bool → List Bool := NaturalArray.sumWords ∘ coeffAbs
noncomputable def rowHeight (x : List Bool) : List Bool :=
  (value (numAbs (discardPrefix x))+value (coeffSum x)).bits
noncomputable def rowHeightOp : List Bool → List Bool := rowHeight ∘ discardPrefix
noncomputable def rowHeights (x : List Bool) : List Bool := mapWith rowHeightOp (pairBits ([],rows x))
noncomputable def heightSum : List Bool → List Bool := NaturalArray.sumWords ∘ rowHeights
noncomputable def height (x : List Bool) : List Bool := (value (bound x)+1+value (heightSum x)).bits

def padRow (x : List Bool) : List Bool :=
  pairBits (extractPrefix x++WordList.encode [BinaryRational.encode 0,BinaryRational.encode 0],discardPrefix x)
noncomputable def padRowOp : List Bool → List Bool := padRow ∘ discardPrefix
noncomputable def paddedRows (x : List Bool) : List Bool := mapWith padRowOp (pairBits ([],rows x))
noncomputable def prepared (x : List Bool) : List Bool :=
  pairBits (nword x++[true,true],pairBits (mword x,pairBits (bound x,pairBits (height x,paddedRows x))))
end BinaryBoundedDecision
namespace BinaryRationalDecision
open BinaryArithmetic
open WordList

def first : List Bool → List Bool := extractPrefix
def rest₁ : List Bool → List Bool := discardPrefix
def rest₂ : List Bool → List Bool := discardPrefix ∘ rest₁
def bound : List Bool → List Bool := extractPrefix ∘ rest₂
def rows : List Bool → List Bool := discardPrefix ∘ rest₂
end BinaryRationalDecision

namespace WordList
namespace Count
noncomputable def op : List Bool → List Bool := List.cons true ∘ Fold.accum
noncomputable def run (x : List Bool) : List Bool := Fold.run op (4*Polynomial.X+4) (Fold.pack x [] [])
end Count
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FaceSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
namespace BinaryFace
open WordList
noncomputable def negEntry : List Bool → List Bool := BinaryRational.negWords ∘ discardPrefix
noncomputable def reverse (x : List Bool) : List Bool :=
  pairBits (mapWith negEntry (pairBits ([],extractPrefix x)),BinaryRational.negWords (discardPrefix x))
noncomputable def reverseOp : List Bool → List Bool := reverse ∘ discardPrefix
noncomputable def reverseRows (x : List Bool) : List Bool := mapWith reverseOp (pairBits ([],x))
noncomputable def proposed (x : List Bool) : List Bool := cons (Find.item x) (Find.accum x)
noncomputable def faceWords (x : List Bool) : List Bool :=
  BinaryRationalDecision.rows (Find.context x)++proposed x++reverseRows (proposed x)
noncomputable def decisionInput (x : List Bool) : List Bool :=
  pairBits (BinaryRationalDecision.first (Find.context x),pairBits (Count.run (faceWords x),
    pairBits (BinaryRationalDecision.bound (Find.context x),faceWords x)))
end BinaryFace
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Rectangular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open BinaryArithmetic Matrix
namespace BinaryExactSolve
open WordList BinaryRationalDecision
noncomputable def coeffs (x : List Bool) : List Bool := mapWith BinaryRow.coeff (pairBits ([],x))
end BinaryExactSolve
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Values
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
namespace BinaryOpeningPayment
open WordList

def field (k : ℕ) (x : List Bool) : List Bool := Lookup.run (pairBits (k.bits,x))

def itemField (k : ℕ) : List Bool → List Bool := field k ∘ extractPrefix
end BinaryOpeningPayment
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Op2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic
namespace BinaryOpeningEnumeration
open WordList BinaryOpeningPayment
noncomputable def clients : List Bool → List Bool := BinaryEllipsoidInitial.indices ∘ field 7
end BinaryOpeningEnumeration
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RowInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFirst
open BinaryArithmetic WordList
open BinaryOpeningPayment

def query (x : List Bool) : List Bool := encode [itemField 0 x,itemField 1 x,itemField 2 x,
  itemField 3 x,itemField 4 x,itemField 5 x,discardPrefix x,itemField 7 x,itemField 8 x]
end MetricKMedianRecovery.BitMachine.BinaryPhaseFirst

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Min
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open BinaryArithmetic WordList
namespace BinaryPhaseAdvance
open BinaryOpeningPayment

def sf (k : ℕ) : List Bool → List Bool := field k ∘ extractPrefix
end BinaryPhaseAdvance
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Fuel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseRun
open BinaryArithmetic WordList
noncomputable def fuel : List Bool → List Bool := Count.run ∘ BinaryPhaseAdvance.sf 8
end MetricKMedianRecovery.BitMachine.BinaryPhaseRun

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ActionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryActions
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def add (x : List Bool) : List Bool := encode [(2:ℕ).bits,extractPrefix x,discardPrefix x]
end MetricKMedianRecovery.BitMachine.BinaryActions

end OAI
end


