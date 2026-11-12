-- Prove2me | Definitions.Def_Q238L006
-- name    : Q238L006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:21:56.175179+00:00
-- url     : https://prove2.me/theorems/dd8305ae-2612-498c-a4d2-902485df3c80
-- title:
--   Definitions bundle Q238L006 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 189 declarations of OpenAI's Lean: 121 definitions, 2 inductive types or structures and 66 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BirdRational.integerMatrix`, `OAI.MetricKMedianRecovery.BirdRational.solve`, `OAI.MetricKMedianRecovery.BitMachine.BinaryActions.add`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.bound`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.coeffAbs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.coeffSum`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.height`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.heightSum`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.mword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.numAbs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.numAbsOp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.nword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.padRow`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.padRowOp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.paddedRows`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.prepared`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rest₁`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rest₂`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rowHeight`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rowHeightOp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rowHeights`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.rows`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.factorial`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.height`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.mword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.nextDim`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.nword`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.rest₁`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.rest₂`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.rest₃`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.dummy`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.indices`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.coeffs`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.decisionInput`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.faceWords`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.negEntry`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.proposed`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.reverse`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.reverseOp`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFace.reverseRows` and 83 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Branching_CopyComputes`, `KMedianRecovery_Encoding_Encode`, `KMedianRecovery_Encoding_Encode3`, `KMedianRecovery_Encoding_OptionEncode`, `KMedianRecovery_Machines_ActionMachine`, `KMedianRecovery_Machines_Program`, `KMedianRecovery_Recovery_BoundOp`, `KMedianRecovery_Recovery_BoundedDecision`, `KMedianRecovery_Recovery_CommonDen`, `KMedianRecovery_Recovery_Copies`, `KMedianRecovery_Recovery_EvalTrans`, `KMedianRecovery_Recovery_ExecutionState`, `KMedianRecovery_Recovery_FaceSelection`, `KMedianRecovery_Recovery_FrameStacks`, `KMedianRecovery_Recovery_Fuel`, `KMedianRecovery_Recovery_LeftNum`, `KMedianRecovery_Recovery_LengthPolynomial`, `KMedianRecovery_Recovery_Min`, `KMedianRecovery_Recovery_MulComputes`, `KMedianRecovery_Recovery_Op`, `KMedianRecovery_Recovery_Op2`, `KMedianRecovery_Recovery_Pack2`, `KMedianRecovery_Recovery_Pack3`, `KMedianRecovery_Recovery_Pack7`, `KMedianRecovery_Recovery_Pack9`, `KMedianRecovery_Recovery_ProcessOutputs`, `KMedianRecovery_Recovery_Rectangular`, `KMedianRecovery_Recovery_RowInput`, `KMedianRecovery_Recovery_Stack`, `KMedianRecovery_Recovery_StackLength`, `KMedianRecovery_Recovery_Step`, `KMedianRecovery_Recovery_Step2`, `KMedianRecovery_Recovery_Store`, `KMedianRecovery_Recovery_Store2`, `KMedianRecovery_Recovery_Values`, `KMedianRecovery_Sampling_ExtractPrefix`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L000` and `Q238L001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L013`, `Q238L014`, `Q238L015`, `Q238L016`, `Q238L017`, `Q238L018`, `Q238L019`, `Q238L020` and `Q238L021`; the statement `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.indices_replicate_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L000
import Definitions.Def_Q238L001

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ExecutionState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

namespace AtomicStep

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {loc : D → X} {F : Finset X} {v lam eta : ℝ}
  {s s' : ExecutionState D X} (H : AtomicStep loc F v lam eta s s')

include H

lemma removal_connection_cap (hv1 : v < 1 / 6) (hz : 0 ≤ s.phase)
    (j : D)
    (hj' : ¬activeAt loc (1 - 3 * v) s'.phase s'.opened j) :
    ∃ f ∈ s'.opened, (1 - 3 * v) * dist (loc j) f ≤ (1 + v ^ 2) * s.phase := by
  have ht : 0 ≤ 1 - 3 * v := by linarith only [hv1]
  have hne := inactive_nonempty loc (1 - 3 * v) s'.phase s'.opened j hj'
  have hc : (1 - 3 * v) * nearestDistance (loc j) s'.opened ≤ s'.phase :=
    not_lt.mp (fun hh => hj' ((activeAt_iff loc _ _ _ j ht hne).mpr hh))
  obtain ⟨f, hf, heq⟩ := nearestDistance_attained (loc j) s'.opened hne
  refine ⟨f, hf, ?_⟩
  rw [heq] at hc
  have hphase : s'.phase ≤ (1 + v ^ 2) * s.phase := by
    cases H with
    | regular => change s.phase ≤ _; nlinarith only [mul_nonneg (sq_nonneg v) hz]
    | free => change s.phase ≤ _; nlinarith only [mul_nonneg (sq_nonneg v) hz]
    | update => exact le_rfl
  exact hc.trans hphase

lemma preserves_no_overbid (hv : 0 < v) (hv1 : v < 1 / 6) (hz : 0 < s.phase)
    (hlam : 0 < lam)
    (hpre : ∀ i ∈ F, bidRow loc (1 - 3 * v) s.phase s.opened i ≤ lam) :
    ∀ i ∈ F, bidRow loc (1 - 3 * v) s'.phase s'.opened i ≤ lam := by
  have ht : 0 ≤ 1 - 3 * v := by linarith only [hv1]
  cases H with
  | regular =>
    intro i hi
    exact (bidRow_antitone_open _ _ _ _ _ _ ht (Finset.subset_insert _ _)).trans (hpre i hi)
  | free =>
    intro i hi
    exact (bidRow_antitone_open _ _ _ _ _ _ ht (Finset.subset_insert _ _)).trans (hpre i hi)
  | update hmaximal =>
    exact phase_update_no_overbid loc F s.opened v s.phase lam hv hv1 hz hlam hpre hmaximal

end AtomicStep
end MetricKMedianRecovery

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

lemma embedStacks_apply {K L : Type} (e : K ↪ L) (s : Stacks K) (k : K) :
    embedStacks e s (e k) = s k := by
  classical
  simp only [embedStacks,dite_eq_left (show ∃ j, e j = e k from ⟨k,rfl⟩)]
  congr 1
  exact e.injective (Classical.choose_spec (show ∃ j, e j = e k from ⟨k,rfl⟩))

lemma embedStacks_update {K L : Type} [DecidableEq K] [DecidableEq L]
    (e : K ↪ L) (s : Stacks K) (k : K) (v : List Bool) :
    embedStacks e (Function.update s k v) = Function.update (embedStacks e s) (e k) v := by
  classical
  funext l
  by_cases h : ∃ j, e j = l
  · obtain ⟨j,rfl⟩ := h
    simp only [embedStacks_apply,Function.update_apply,e.injective.eq_iff]
  · rw [embedStacks_not_image e _ l h,Function.update_of_ne (by intro he; exact h ⟨k,he.symm⟩),
      embedStacks_not_image e s l h]

section Rename
variable {K L A B S T : Type} [DecidableEq K] [DecidableEq L]

lemma stepAux_rename (ek : K ↪ L) (el : A → B) (es : S → T) (rs : T → S)
    (h : ∀ s, rs (es s) = s) (ret : Option B)
    (q : TM2.Stmt (fun _ : K => Bool) A S) (s : S) (stk : Stacks K) :
    TM2.stepAux (renameStmt ek el es rs ret q) (es s) (embedStacks ek stk) =
      renameCfg ek el es ret (TM2.stepAux q s stk) := by
  induction q generalizing s stk with
  | push k f q ih =>
    simp only [renameStmt,TM2.stepAux,h,embedStacks_apply,←embedStacks_update]
    exact ih _ _
  | peek k f q ih =>
    simp only [renameStmt,TM2.stepAux,h,embedStacks_apply]
    exact ih _ _
  | pop k f q ih =>
    simp only [renameStmt,TM2.stepAux,h,embedStacks_apply,←embedStacks_update]
    exact ih _ _
  | load f q ih =>
    simp only [renameStmt,TM2.stepAux,h]
    exact ih _ _
  | branch f q r ihq ihr =>
    simp only [renameStmt,TM2.stepAux,h]
    cases f s <;> simp only [Bool.cond_false,Bool.cond_true]
    · exact ihr _ _
    · exact ihq _ _
  | goto f => simp only [renameStmt,TM2.stepAux,h,renameCfg,Option.elim_some]
  | halt => cases ret <;> rfl

end Rename

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

lemma embedStacks_pure {K L : Type} [DecidableEq K] [DecidableEq L]
    (e : K ↪ L) (k : K) (bits : List Bool) :
    embedStacks e (Function.update (fun _ => []) k bits) =
      Function.update (fun _ => []) (e k) bits := by
  rw [embedStacks_update,embedStacks_empty]

namespace Composition
variable (p q : Program)

def rightStack : q.K ↪ Stack p q where
  toFun k := if h : k = q.input then Sum.inl p.output else Sum.inr ⟨k,h⟩
  inj' := by
    intro k j h
    by_cases hk : k = q.input <;> by_cases hj : j = q.input
    · exact hk.trans hj.symm
    · simp only [dite_eq_left hk,dite_eq_right hj] at h
      contradiction
    · simp only [dite_eq_right hk,dite_eq_left hj] at h
      contradiction
    · simp only [dite_eq_right hk,dite_eq_right hj,Sum.inr.injEq,Subtype.mk.injEq] at h
      exact h

@[simp] lemma rightStack_input : rightStack p q q.input = Sum.inl p.output := by
  simp [rightStack]

noncomputable abbrev program : Program where
  K := Stack p q
  input := Sum.inl p.input
  output := rightStack p q q.output
  Label := p.Label ⊕ q.Label
  main := Sum.inl p.main
  State := p.State × q.State
  initial := (p.initial,q.initial)
  code := fun l => match l with
    | .inl l => renameStmt (leftStack p q) Sum.inl (fun s => (s,q.initial)) Prod.fst
        (some (Sum.inr q.main)) (p.code l)
    | .inr l => renameStmt (rightStack p q) Sum.inr (fun s => (p.initial,s)) Prod.snd
        none (q.code l)

noncomputable def leftCfg : p.machine.Cfg → (program p q).machine.Cfg :=
  renameCfg (leftStack p q) Sum.inl (fun s => (s,q.initial)) (some (Sum.inr q.main))

noncomputable def rightCfg : q.machine.Cfg → (program p q).machine.Cfg :=
  renameCfg (rightStack p q) Sum.inr (fun s => (p.initial,s)) none

lemma left_step (s t : p.machine.Cfg) (h : p.machine.step s = some t) :
    (program p q).machine.step (leftCfg p q s) = some (leftCfg p q t) := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    change some (TM2.stepAux (renameStmt (leftStack p q) Sum.inl
      (fun s => (s,q.initial)) Prod.fst (some (Sum.inr q.main)) (p.code l))
        (v,q.initial) (embedStacks (leftStack p q) stk)) = _
    rw [stepAux_rename _ _ _ _ (fun _ => rfl)]
    rfl

lemma right_step (s t : q.machine.Cfg) (h : q.machine.step s = some t) :
    (program p q).machine.step (rightCfg p q s) = some (rightCfg p q t) := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    change some (TM2.stepAux (renameStmt (rightStack p q) Sum.inr
      (fun s => (p.initial,s)) Prod.snd none (q.code l))
        (p.initial,v) (embedStacks (rightStack p q) stk)) = _
    rw [stepAux_rename _ _ _ _ (fun _ => rfl)]
    rfl

lemma left_initial (bits : List Bool) :
    leftCfg p q (initList p.machine bits) = initList (program p q).machine bits := by
  rw [initList_bool,initList_bool]
  change (⟨some (Sum.inl p.main),(p.initial,q.initial),
      embedStacks (leftStack p q) (Function.update (fun _ => []) p.input bits)⟩ : (program p q).machine.Cfg) = _
  rw [embedStacks_pure]
  rfl

lemma handoff (bits : List Bool) :
    leftCfg p q (haltList p.machine bits) = rightCfg p q (initList q.machine bits) := by
  rw [haltList_bool,initList_bool]
  change (⟨some (Sum.inr q.main),(p.initial,q.initial),
    embedStacks (leftStack p q) (Function.update (fun _ => []) p.output bits)⟩ : (program p q).machine.Cfg) =
    ⟨some (Sum.inr q.main),(p.initial,q.initial),
    embedStacks (rightStack p q) (Function.update (fun _ => []) q.input bits)⟩
  rw [embedStacks_pure,embedStacks_pure,rightStack_input]
  rfl

lemma right_final (bits : List Bool) :
    rightCfg p q (haltList q.machine bits) = haltList (program p q).machine bits := by
  rw [haltList_bool,haltList_bool]
  change (⟨none,(p.initial,q.initial),
      embedStacks (rightStack p q) (Function.update (fun _ => []) q.output bits)⟩ : (program p q).machine.Cfg) = _
  rw [embedStacks_pure]

noncomputable def outputs {x y z : List Bool} {m n : ℕ}
    (hp : TM2OutputsInTime p.machine x (some y) m)
    (hq : TM2OutputsInTime q.machine y (some z) n) :
    TM2OutputsInTime (program p q).machine x (some z) (n+m) := by
  have h1 := iterate_transfer p.machine.step (program p q).machine.step (leftCfg p q)
    (left_step p q) hp.steps (initList p.machine x) (haltList p.machine y) hp.evals_in_steps
  have h2 := iterate_transfer q.machine.step (program p q).machine.step (rightCfg p q)
    (right_step p q) hq.steps (initList q.machine y) (haltList q.machine z) hq.evals_in_steps
  rw [left_initial,handoff] at h1
  rw [right_final] at h2
  refine ⟨⟨hq.steps+hp.steps,?_⟩,Nat.add_le_add hq.steps_le_m hp.steps_le_m⟩
  change (fun x : Option (program p q).machine.Cfg => x.bind (program p q).machine.step)^[hq.steps+hp.steps]
    (some (initList (program p q).machine x)) = some (haltList (program p q).machine z)
  rw [Function.iterate_add_apply,h1,h2]

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

noncomputable def Program.maxPush (p : Program) : ℕ := Finset.univ.sup (fun l => pushBound (p.code l))

lemma Program.step_length (p : Program) (s t : p.machine.Cfg) (h : p.machine.step s = some t) :
    stackLength t.stk ≤ stackLength s.stk + p.maxPush := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    have hb : pushBound (p.code l) ≤ p.maxPush :=
      Finset.le_sup (f := fun l => pushBound (p.code l)) (Finset.mem_univ l)
    exact (stepAux_length (p.code l) v stk).trans (Nat.add_le_add_left hb _)

lemma Program.output_length (p : Program) {x y : List Bool} {m : ℕ}
    (h : TM2OutputsInTime p.machine x (some y) m) :
    y.length ≤ x.length+m*p.maxPush := by
  have hl := iterate_length p.machine.step (fun s => stackLength s.stk) p.maxPush
    p.step_length h.steps (initList p.machine x) (haltList p.machine y) h.evals_in_steps
  simp only [initList_bool,haltList_bool,stackLength_pure] at hl
  exact hl.trans (Nat.add_le_add_left (Nat.mul_le_mul_right p.maxPush h.steps_le_m) _)

structure PolyComputes (f : List Bool → List Bool) where
  program : Program
  time : Polynomial ℕ
  outputs : ∀ x, TM2OutputsInTime program.machine x (some (f x)) (time.eval x.length)

noncomputable def PolyComputes.comp {f g : List Bool → List Bool}
    (hf : PolyComputes f) (hg : PolyComputes g) : PolyComputes (g ∘ f) where
  program := Composition.program hf.program hg.program
  time := hg.time.comp (Polynomial.X + hf.time * Polynomial.C hf.program.maxPush) + hf.time
  outputs x := by
    have hlen := hf.program.output_length (hf.outputs x)
    have hh := Composition.outputs hf.program hg.program (hf.outputs x) (hg.outputs (f x))
    refine ⟨hh.toEvalsTo,?_⟩
    apply hh.steps_le_m.trans
    simp only [Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X]
    exact Nat.add_le_add_right (polynomial_monotone hg.time hlen) _

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

lemma extractPrefix_length (bits : List Bool) : (extractPrefix bits).length≤bits.length := by
  induction bits using List.twoStepInduction with
  | nil => simp [extractPrefix]
  | singleton b => cases b <;> simp [extractPrefix]
  | cons_cons b c bits ih _ =>
    cases b <;> simp only [extractPrefix,List.length_cons,List.length_nil] <;> omega

namespace MapLeft
variable (p : Program)

abbrev Stack := p.K ⊕ Fin 2
abbrev Label := p.Label ⊕ Fin 4
abbrev State := p.State × Option Bool

def mapStacks (s : Stacks p.K) (a b : List Bool) : Stacks (Stack p) := frameStacks s ![a,b]
@[simp] lemma stacks_left (s : Stacks p.K) (a b : List Bool) (k : p.K) :
    mapStacks p s a b (.inl k)=s k := rfl
@[simp] lemma stacks_zero (s : Stacks p.K) (a b : List Bool) :
    mapStacks p s a b (.inr 0)=a := rfl
@[simp] lemma stacks_one (s : Stacks p.K) (a b : List Bool) :
    mapStacks p s a b (.inr 1)=b := rfl
lemma updLeft (s : Stacks p.K) (a b t : List Bool) (k : p.K) :
    Function.update (mapStacks p s a b) (.inl k) t=mapStacks p (Function.update s k t) a b :=
  (frameStacks_update _ _ _ _).symm
lemma upd0 (s : Stacks p.K) (a b t : List Bool) :
    Function.update (mapStacks p s a b) (.inr 0) t=mapStacks p s t b := by
  funext i
  cases i with
  | inl k => simp [mapStacks]
  | inr k => fin_cases k <;> simp [mapStacks]
lemma upd1 (s : Stacks p.K) (a b t : List Bool) :
    Function.update (mapStacks p s a b) (.inr 1) t=mapStacks p s a t := by
  funext i
  cases i with
  | inl k => simp [mapStacks]
  | inr k => fin_cases k <;> simp [mapStacks]

abbrev program : Program where
  K := Stack p
  input := .inr 1
  output := .inr 1
  Label := Label p
  main := .inr 0
  State := State p
  initial := (p.initial,none)
  code l := match l with
    | .inl i => renameStmt Function.Embedding.inl Sum.inl (fun s => (s,none)) Prod.fst
        (some (.inr 2)) (p.code i)
    | .inr i => if i=0 then
        .pop (.inr 1) (fun s b => (s.1,b))
          (.branch (fun s => decide (s.2=some true))
            (.pop (.inr 1) (fun s b => (s.1,b))
              (.branch (fun s => s.2.isSome)
                (.push (.inr 0) (fun s => s.2.getD false)
                  (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 0))))
                (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 1)))))
            (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 1))))
      else if i=1 then
        .pop (.inr 0) (fun s b => (s.1,b))
          (.branch (fun s => s.2.isSome)
            (.push (.inl p.input) (fun s => s.2.getD false)
              (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 1))))
            (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inl p.main))))
      else if i=2 then
        .pop (.inl p.output) (fun s b => (s.1,b))
          (.branch (fun s => s.2.isSome)
            (.push (.inr 0) (fun s => s.2.getD false)
              (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 2))))
            (.push (.inr 1) (fun _ => false)
              (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 3)))))
      else
        .pop (.inr 0) (fun s b => (s.1,b))
          (.branch (fun s => s.2.isSome)
            (.push (.inr 1) (fun s => s.2.getD false)
              (.push (.inr 1) (fun _ => true)
                (.load (fun _ => (p.initial,none)) (.goto (fun _ => .inr 3)))))
            (.load (fun _ => (p.initial,none)) .halt))

def pure (k : p.K) (xs : List Bool) : Stacks p.K := Function.update (fun _ => []) k xs
lemma pure_at (k : p.K) (xs : List Bool) : pure p k xs k=xs := by simp [pure]
lemma pure_update (k : p.K) (xs ys : List Bool) :
    Function.update (pure p k xs) k ys=pure p k ys := Function.update_idem ..
lemma pure_nil (k : p.K) : pure p k []=fun _ => [] := by simp [pure]

def cfg (l : Label p) (s : Stacks p.K) (a b : List Bool) : (program p).machine.Cfg :=
  ⟨some l,(p.initial,none),mapStacks p s a b⟩
def done (ys : List Bool) : (program p).machine.Cfg :=
  ⟨none,(p.initial,none),mapStacks p (fun _ => []) [] ys⟩

def runCfg (ys : List Bool) (c : p.machine.Cfg) : (program p).machine.Cfg :=
  ⟨c.l.elim (some (.inr 2)) (fun l => some (.inl l)),(c.var,none),mapStacks p c.stk [] ys⟩

lemma run_step (ys : List Bool) (s t : p.machine.Cfg) (h : p.machine.step s=some t) :
    (program p).machine.step (runCfg p ys s)=some (runCfg p ys t) := by
  rcases s with ⟨l,v,stk⟩
  cases l with
  | none => simp only [FinTM2.step,TM2.step] at h; contradiction
  | some l =>
    simp only [FinTM2.step,TM2.step] at h
    have ht := Option.some.inj h
    subst t
    change some (TM2.stepAux (renameStmt Function.Embedding.inl Sum.inl (fun s => (s,none))
      Prod.fst (some (.inr 2)) (p.code l)) (v,none) (frameStacks stk ![[],ys]))=_
    rw [stepAux_frame _ _ _ (fun _ => rfl)]
    rfl

lemma parse_nil (a : List Bool) :
    (program p).machine.step (cfg p (.inr 0) (fun _=>[]) a [])=
      some (cfg p (.inr 1) (fun _=>[]) a []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd1]; rfl
lemma parse_false (xs a : List Bool) :
    (program p).machine.step (cfg p (.inr 0) (fun _=>[]) a (false::xs))=
      some (cfg p (.inr 1) (fun _=>[]) a xs) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd1]; rfl
lemma parse_one (a : List Bool) :
    (program p).machine.step (cfg p (.inr 0) (fun _=>[]) a [true])=
      some (cfg p (.inr 1) (fun _=>[]) a []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd1]; rfl
lemma parse_true (b : Bool) (xs a : List Bool) :
    (program p).machine.step (cfg p (.inr 0) (fun _=>[]) a (true::b::xs))=
      some (cfg p (.inr 0) (fun _=>[]) (b::a) xs) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0,upd1]; rfl
lemma restore_nil (xs ys : List Bool) :
    (program p).machine.step (cfg p (.inr 1) (pure p p.input xs) [] ys)=
      some (cfg p (.inl p.main) (pure p p.input xs) [] ys) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0]; rfl
lemma restore_cons (b : Bool) (a xs ys : List Bool) :
    (program p).machine.step (cfg p (.inr 1) (pure p p.input xs) (b::a) ys)=
      some (cfg p (.inr 1) (pure p p.input (b::xs)) a ys) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0,updLeft,pure_at,pure_update]; rfl
lemma reverse_nil (a ys : List Bool) :
    (program p).machine.step (cfg p (.inr 2) (pure p p.output []) a ys)=
      some (cfg p (.inr 3) (fun _=>[]) a (false::ys)) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,updLeft,upd1,pure_nil]; rfl
lemma reverse_cons (b : Bool) (xs a ys : List Bool) :
    (program p).machine.step (cfg p (.inr 2) (pure p p.output (b::xs)) a ys)=
      some (cfg p (.inr 2) (pure p p.output xs) (b::a) ys) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,updLeft,upd0,pure_at,pure_update]; rfl
lemma encode_nil (ys : List Bool) :
    (program p).machine.step (cfg p (.inr 3) (fun _=>[]) [] ys)=some (done p ys) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,done,upd0]; rfl
lemma encode_cons (b : Bool) (xs ys : List Bool) :
    (program p).machine.step (cfg p (.inr 3) (fun _=>[]) (b::xs) ys)=
      some (cfg p (.inr 3) (fun _=>[]) xs (true::b::ys)) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0,upd1]; rfl

end MapLeft
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

namespace MapLeft
variable (p : Program)

noncomputable def parse_phase (bits a : List Bool) :
    EvalsToInTime (program p).machine.step (cfg p (.inr 0) (fun _=>[]) a bits)
      (some (cfg p (.inr 1) (fun _=>[]) ((extractPrefix bits).reverse++a) (discardPrefix bits)))
      (bits.length+1) := by
  induction bits using List.twoStepInduction generalizing a with
  | nil => exact one_step (parse_nil p a)
  | singleton b =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_cons,List.length_nil] using
        time_mono (one_step (parse_false p [] a)) (by decide : 1≤2)
    | true => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append,List.length_cons,List.length_nil] using
        time_mono (one_step (parse_one p a)) (by decide : 1≤2)
  | cons_cons b c bits ih _ =>
    cases b with
    | false => simpa only [extractPrefix,discardPrefix,List.reverse_nil,List.nil_append] using
        time_mono (one_step (parse_false p (c::bits) a)) (by simp : 1≤(false::c::bits).length+1)
    | true =>
      have hh := step_then (parse_true p c bits a) (ih (c::a))
      simp only [extractPrefix,discardPrefix,List.reverse_cons,List.append_assoc,List.singleton_append] at ⊢
      exact time_mono hh (by simp)

noncomputable def restore_phase (a xs ys : List Bool) :
    EvalsToInTime (program p).machine.step (cfg p (.inr 1) (pure p p.input xs) a ys)
      (some (cfg p (.inl p.main) (pure p p.input (a.reverse++xs)) [] ys)) (a.length+1) := by
  induction a generalizing xs with
  | nil => exact one_step (restore_nil p xs ys)
  | cons b a ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using step_then (restore_cons p b a xs ys) (ih (b::xs))

noncomputable def reverse_phase (xs a ys : List Bool) :
    EvalsToInTime (program p).machine.step (cfg p (.inr 2) (pure p p.output xs) a ys)
      (some (cfg p (.inr 3) (fun _=>[]) (xs.reverse++a) (false::ys))) (xs.length+1) := by
  induction xs generalizing a with
  | nil => exact one_step (reverse_nil p a ys)
  | cons b xs ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using step_then (reverse_cons p b xs a ys) (ih (b::a))

noncomputable def encode_phase (xs ys : List Bool) :
    EvalsToInTime (program p).machine.step (cfg p (.inr 3) (fun _=>[]) xs ys)
      (some (done p (xs.reverse.flatMap (fun b => [true,b])++ys))) (xs.length+1) := by
  induction xs generalizing ys with
  | nil => exact one_step (encode_nil p ys)
  | cons b xs ih =>
    simpa only [List.length_cons,List.reverse_cons,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      step_then (encode_cons p b xs ys) (ih (true::b::ys))

lemma initial (xs : List Bool) : initList (program p).machine xs=cfg p (.inr 0) (fun _=>[]) [] xs := by
  rw [initList_bool]
  congr 1
  have he : (fun _ : Stack p => ([] : List Bool))=mapStacks p (fun _=>[]) [] [] := by
    funext i
    cases i with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  rw [he,upd1]
lemma final (xs : List Bool) : haltList (program p).machine xs=done p xs := by
  rw [haltList_bool]
  congr 1
  have he : (fun _ : Stack p => ([] : List Bool))=mapStacks p (fun _=>[]) [] [] := by
    funext i
    cases i with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  rw [he,upd1]
lemma run_initial (xs ys : List Bool) :
    runCfg p ys (initList p.machine xs)=cfg p (.inl p.main) (pure p p.input xs) [] ys := by
  rw [initList_bool]
  rfl
lemma run_final (xs ys : List Bool) :
    runCfg p ys (haltList p.machine xs)=cfg p (.inr 2) (pure p p.output xs) [] ys := by
  rw [haltList_bool]
  rfl

end MapLeft

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Store
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace ProductBits

def store (a b c : List Bool) : Stacks (Fin 3) := ![a,b,c]
@[simp] lemma store0 (a b c : List Bool) : store a b c 0=a := rfl
@[simp] lemma store1 (a b c : List Bool) : store a b c 1=b := rfl
@[simp] lemma store2 (a b c : List Bool) : store a b c 2=c := rfl
lemma upd0 (a b c t : List Bool) : Function.update (store a b c) 0 t=store t b c := by
  funext i; fin_cases i <;> simp [store]
lemma upd1 (a b c t : List Bool) : Function.update (store a b c) 1 t=store a t c := by
  funext i; fin_cases i <;> simp [store]
lemma upd2 (a b c t : List Bool) : Function.update (store a b c) 2 t=store a b t := by
  funext i; fin_cases i <;> simp [store]

lemma projections_length (xs : List Bool) :
    (extractPrefix xs).length≤xs.length ∧ (discardPrefix xs).length≤xs.length := by
  induction xs using List.twoStepInduction with
  | nil => simp [extractPrefix,discardPrefix]
  | singleton b => cases b <;> simp [extractPrefix,discardPrefix]
  | cons_cons b c xs ih _ => cases b <;> simp only [extractPrefix,discardPrefix,List.length_cons,List.length_nil] <;> omega

end ProductBits

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Store2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace WordOperations

def store (xs ys : List Bool) : Stacks (Fin 2) := ![xs,ys]

end WordOperations

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
open BinaryArithmetic WordOperations

def first (x : List Bool) : List Bool := extractPrefix x.tail
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

open WordOperations BinaryArithmetic
namespace Signed

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
open WordOperations BinaryArithmetic
namespace BinaryRational

def numerator (x : List Bool) : List Bool := extractPrefix x
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
open WordOperations BinaryArithmetic
@[simp] lemma extractPrefix_pairBits (x y : List Bool) : extractPrefix (pairBits (x,y))=x := extractPrefix_pair x y
@[simp] lemma discardPrefix_pairBits (x y : List Bool) : discardPrefix (pairBits (x,y))=y := discardPrefix_pair x y
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
open WordOperations BinaryArithmetic
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
open WordOperations UnaryTake
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
open WordOperations UnaryTake

structure PolynomialCounter (P : Polynomial ℕ) where
  word : List Bool → List Bool
  computes : PolyComputes word
  word_length : ∀ x,(word x).length=P.eval x.length
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
open WordOperations UnaryTake

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
open WordOperations BinaryArithmetic
namespace WordList.Lookup

def step (x : List Bool) : List Bool :=
  if value (extractPrefix x)=0 then x
  else pairBits ((value (extractPrefix x)-1).bits,WordList.tail (discardPrefix x))

def run (x : List Bool) : List Bool := WordList.head (discardPrefix (step^[x.length] x))
end WordList.Lookup
end
open WordOperations
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
open WordOperations BinaryArithmetic
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

open WordOperations BinaryArithmetic
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
open WordOperations BinaryArithmetic
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

def integerMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) : Matrix (Fin n) (Fin n) ℤ :=
  BirdInteger.freeze (Matrix.of (fun i j => scaled (data A b) (i,some j)))

def solve {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) : Fin n → ℚ :=
  let Z := integerMatrix A b
  let w := integerVector A b
  let d := BirdInteger.determinant Z
  let ar := Vector.ofFn (fun i =>
    (BirdInteger.determinant (BirdInteger.freeze (Z.updateCol i w)):ℚ)/(d:ℚ))
  fun i => ar[i]

end MetricKMedianRecovery.BirdRational

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
open WordOperations
namespace WordList.Find

def context : List Bool → List Bool := extractPrefix
def item : List Bool → List Bool := extractPrefix ∘ discardPrefix
def accum : List Bool → List Bool := discardPrefix ∘ discardPrefix
end WordList.Find
end
open WordOperations BinaryArithmetic
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
open WordOperations BinaryArithmetic Ellipsoid
namespace BinaryEllipsoidInitial
open WordList

def dummy (u : List Bool) : List Bool := repeatWords (pairBits (u,[]))
noncomputable def indices : List Bool → List Bool := Indices.run ∘ dummy
end BinaryEllipsoidInitial
end
open WordOperations BinaryArithmetic Ellipsoid
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
open WordOperations BinaryArithmetic
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
open WordOperations BinaryArithmetic Ellipsoid
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

open WordOperations BinaryArithmetic
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
open WordOperations BinaryArithmetic Ellipsoid
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
open WordOperations BinaryArithmetic Ellipsoid
open WordList

def first : List Bool → List Bool := extractPrefix
def rest₁ : List Bool → List Bool := discardPrefix
def rest₂ : List Bool → List Bool := discardPrefix ∘ rest₁
def bound : List Bool → List Bool := extractPrefix ∘ rest₂
def rows : List Bool → List Bool := discardPrefix ∘ rest₂
end BinaryRationalDecision

open WordOperations
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
open WordOperations BinaryArithmetic Ellipsoid
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

open WordOperations BinaryArithmetic Ellipsoid Matrix
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
open WordOperations BinaryArithmetic
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
open WordOperations BinaryArithmetic
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
open WordOperations BinaryArithmetic WordList
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
open WordOperations BinaryArithmetic WordList
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
open WordOperations BinaryArithmetic WordList
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
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
noncomputable def add (x : List Bool) : List Bool := encode [(2:ℕ).bits,extractPrefix x,discardPrefix x]
end MetricKMedianRecovery.BitMachine.BinaryActions

end OAI
end


