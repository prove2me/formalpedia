-- Prove2me | Definitions.Def_Q238L001
-- name    : Q238L001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:20:55.490402+00:00
-- url     : https://prove2.me/theorems/aa79548a-3cdd-4470-aa6f-84e9f5fb9f76
-- title:
--   Definitions bundle Q238L001 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 107 declarations of OpenAI's Lean: 39 definitions, 1 inductive type or structure and 67 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BirdRational.commonDen`, `OAI.MetricKMedianRecovery.BirdRational.data`, `OAI.MetricKMedianRecovery.BirdRational.integerVector`, `OAI.MetricKMedianRecovery.BirdRational.scaled`, `OAI.MetricKMedianRecovery.BirdRationalIteration.determinant`, `OAI.MetricKMedianRecovery.BirdRationalIteration.flat`, `OAI.MetricKMedianRecovery.BirdRationalIteration.integral`, `OAI.MetricKMedianRecovery.BirdRationalIteration.iterate`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.carryBit`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.normalize`, `OAI.MetricKMedianRecovery.BitMachine.BinaryArithmetic.value`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryGCD.second`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.denominator`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.encode`, `OAI.MetricKMedianRecovery.BitMachine.BoundedIteration.polynomialRun`, `OAI.MetricKMedianRecovery.BitMachine.Composition.Stack`, `OAI.MetricKMedianRecovery.BitMachine.Composition.leftStack`, `OAI.MetricKMedianRecovery.BitMachine.Program`, `OAI.MetricKMedianRecovery.BitMachine.Program.machine`, `OAI.MetricKMedianRecovery.BitMachine.RepeatedAppend.copies`, `OAI.MetricKMedianRecovery.BitMachine.Signed.encode`, `OAI.MetricKMedianRecovery.BitMachine.Signed.sign`, `OAI.MetricKMedianRecovery.BitMachine.Stacks`, `OAI.MetricKMedianRecovery.BitMachine.While.next`, `OAI.MetricKMedianRecovery.BitMachine.discardPrefix`, `OAI.MetricKMedianRecovery.BitMachine.embedStacks`, `OAI.MetricKMedianRecovery.BitMachine.eval_trans`, `OAI.MetricKMedianRecovery.BitMachine.frameStacks`, `OAI.MetricKMedianRecovery.BitMachine.one_step`, `OAI.MetricKMedianRecovery.BitMachine.pushBound`, `OAI.MetricKMedianRecovery.BitMachine.pushWord`, `OAI.MetricKMedianRecovery.BitMachine.renameCfg`, `OAI.MetricKMedianRecovery.BitMachine.renameStmt`, `OAI.MetricKMedianRecovery.BitMachine.stackLength`, `OAI.MetricKMedianRecovery.BitMachine.step_then`, `OAI.MetricKMedianRecovery.BitMachine.time_mono`, `OAI.MetricKMedianRecovery.BitMachine.twoStacks`, `OAI.MetricKMedianRecovery.Ellipsoid.rationalRootUpper`, `OAI.MetricKMedianRecovery.Ellipsoid.sqrtUpperFraction`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Encoding_PushWord`, `KMedianRecovery_Encoding_Reencode`, `KMedianRecovery_Machines_Program`, `KMedianRecovery_Machines_Program2`, `KMedianRecovery_Recovery_CommonDen`, `KMedianRecovery_Recovery_Copies`, `KMedianRecovery_Recovery_EvalTrans`, `KMedianRecovery_Recovery_FrameStacks`, `KMedianRecovery_Recovery_GridFloor`, `KMedianRecovery_Recovery_Iterate`, `KMedianRecovery_Recovery_LeftNum`, `KMedianRecovery_Recovery_MulComputes`, `KMedianRecovery_Recovery_Normalize`, `KMedianRecovery_Recovery_Pack2`, `KMedianRecovery_Recovery_ProcessOutputs`, `KMedianRecovery_Recovery_RealVector`, `KMedianRecovery_Recovery_Stack`, `KMedianRecovery_Recovery_StackLength`, `KMedianRecovery_Recovery_StepThen`, `KMedianRecovery_Recovery_Value`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`.
--
--   **Imported by** (directly, in this split): the bundles `Q238L006`, `Q238L007`, `Q238L008`, `Q238L009` and `Q238L012`; the statement `OAI.MetricKMedianRecovery.Ellipsoid.rationalRootUpper_bounds_s238r`; the proofs of `OAI.MetricKMedianRecovery.Categorical.Selected.greedyRun_good_s238r` and `OAI.MetricKMedianRecovery.Ellipsoid.rationalRootUpper_bounds_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery

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
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
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

lemma unit_update {α : Type} (f : Unit → α) (a : α) :
    Function.update f () a = fun _ => a := by
  funext u
  cases u
  simp only [Function.update_self]

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

@[simp] lemma twoStacks_false (xs ys : List Bool) : twoStacks xs ys false = xs := rfl
@[simp] lemma twoStacks_true (xs ys : List Bool) : twoStacks xs ys true = ys := rfl

lemma twoStacks_update_false (xs ys zs : List Bool) :
    Function.update (twoStacks xs ys) false zs = twoStacks zs ys := by
  funext b
  cases b <;> rfl

lemma twoStacks_update_true (xs ys zs : List Bool) :
    Function.update (twoStacks xs ys) true zs = twoStacks xs zs := by
  funext b
  cases b <;> rfl

lemma twoStacks_pure_false (xs : List Bool) :
    Function.update (fun _ : Bool => []) false xs = twoStacks xs [] := by
  funext b
  cases b <;> rfl

lemma twoStacks_pure_true (xs : List Bool) :
    Function.update (fun _ : Bool => []) true xs = twoStacks [] xs := by
  funext b
  cases b <;> rfl

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

lemma pushWord_step {K L S : Type} [DecidableEq K] (k : K) (bs : List Bool)
    (c : TM2.Stmt (fun _ : K=>Bool) L S) (v : S) (s : Stacks K) :
    TM2.stepAux (pushWord k bs c) v s=TM2.stepAux c v (Function.update s k (bs++s k)) := by
  induction bs generalizing c with
  | nil => simp only [pushWord,List.nil_append,Function.update_eq_self]
  | cons b bs ih =>
    rw [pushWord,ih]
    simp only [TM2.stepAux,Function.update_self,Function.update_idem,List.cons_append]

lemma fold_empty (xs : List Bool) (q : Bool) :
    xs.foldl (fun _ _=>false) q=if xs=[] then q else false := by
  induction xs generalizing q with
  | nil => simp
  | cons b xs ih => simp [ih]

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

def commonDen (q : J → ℚ) : ℤ := ∏ i, ((q i).den:ℤ)
def scaled (q : J → ℚ) (i : J) : ℤ :=
  (q i).num * ∏ j ∈ Finset.univ.erase i, ((q j).den:ℤ)

def data {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    (Fin n × Option (Fin n)) → ℚ := fun ⟨i,j⟩ => match j with
  | none => b i
  | some j => A i j

def integerVector {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) : Fin n → ℤ :=
  let ar := Vector.ofFn (fun i => scaled (data A b) (i,none))
  fun i => ar[i]

end MetricKMedianRecovery.BirdRational

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

def carryBit (c x y : Bool) : Bool := (c && x) || (c && y) || (x && y)

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Normalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace BinaryArithmetic

def normalize (xs : List Bool) : List Bool :=
  (xs.reverse.dropWhile (fun b => !b)).reverse

end BinaryArithmetic
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
def second (x : List Bool) : List Bool := discardPrefix x.tail

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
def denominator (x : List Bool) : List Bool := discardPrefix x

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
@[simp] lemma Signed.sign_encode (z : ℤ) : Signed.sign (Signed.encode z)=decide (z<0) := rfl
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
namespace RepeatedAppend

def copies : ℕ → List Bool → List Bool
  | 0,_=>[]
  | n+1,d=>copies n d++d
lemma length_copies (n : ℕ) (d : List Bool) : (copies n d).length=n*d.length := by
  induction n with
  | zero => simp only [copies,List.length_nil,Nat.zero_mul]
  | succ n ih => simp only [copies,List.length_append,ih,Nat.add_mul,Nat.one_mul]

end RepeatedAppend

namespace BoundedIteration

def polynomialRun (f : List Bool → List Bool) (Q R : Polynomial ℕ) (x : List Bool) : List Bool :=
  (fun s=>(f s).take (R.eval x.length))^[Q.eval x.length] x
end BoundedIteration
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_GridFloor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

def sqrtUpperFraction (p q D : ℕ) : ℚ :=
  ((Nat.sqrt (p*q*D^2)+1 : ℕ):ℚ)/((q*D:ℕ):ℚ)

end MetricKMedianRecovery.Ellipsoid

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
def integral {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j=>BirdRational.scaled (flat A) (i,j)
def determinant : {n : ℕ} → Matrix (Fin n) (Fin n) ℚ → ℚ
  | 0, _ => 1
  | n+1, A => (-1)^n * iterate A n 0 0
end MetricKMedianRecovery.BirdRationalIteration

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RealVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

section
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

def rationalRootUpper (D : ℕ) (q : ℚ) : ℚ := sqrtUpperFraction q.num.natAbs q.den D

end

open Matrix
open scoped Matrix

end MetricKMedianRecovery.Ellipsoid

end OAI
end


