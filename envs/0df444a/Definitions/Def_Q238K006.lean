-- Prove2me | Definitions.Def_Q238K006
-- name    : Q238K006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:12:21.549331+00:00
-- url     : https://prove2.me/theorems/a9cfb767-4bf0-44b3-8fc7-09ba66bfe6dd
-- title:
--   Definitions bundle Q238K006 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 105 declarations of OpenAI's Lean: 37 definitions, 2 inductive types or structures and 66 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BirdRational.integerMatrix`, `OAI.MetricKMedianRecovery.BirdRational.integerVector`, `OAI.MetricKMedianRecovery.BirdRational.solve`, `OAI.MetricKMedianRecovery.BirdRationalIteration.integral`, `OAI.MetricKMedianRecovery.BitMachine.Composition.leftCfg`, `OAI.MetricKMedianRecovery.BitMachine.Composition.outputs`, `OAI.MetricKMedianRecovery.BitMachine.Composition.program`, `OAI.MetricKMedianRecovery.BitMachine.Composition.rightCfg`, `OAI.MetricKMedianRecovery.BitMachine.Composition.rightStack`, `OAI.MetricKMedianRecovery.BitMachine.MapLeft.Label`, `OAI.MetricKMedianRecovery.BitMachine.MapLeft.Stack`, `OAI.MetricKMedianRecovery.BitMachine.MapLeft.State`, `OAI.MetricKMedianRecovery.BitMachine.MapLeft.cfg`, `OAI.MetricKMedianRecovery.BitMachine.MapLeft.done`, `OAI.MetricKMedianRecovery.BitMachine.MapLeft.encode_phase`, `OAI.MetricKMedianRecovery.BitMachine.MapLeft.mapStacks`, `OAI.MetricKMedianRecovery.BitMachine.MapLeft.outputs`, `OAI.MetricKMedianRecovery.BitMachine.MapLeft.parse_phase`, `OAI.MetricKMedianRecovery.BitMachine.MapLeft.program`, `OAI.MetricKMedianRecovery.BitMachine.MapLeft.pure`, `OAI.MetricKMedianRecovery.BitMachine.MapLeft.restore_phase`, `OAI.MetricKMedianRecovery.BitMachine.MapLeft.reverse_phase`, `OAI.MetricKMedianRecovery.BitMachine.MapLeft.runCfg`, `OAI.MetricKMedianRecovery.BitMachine.PolyComputes`, `OAI.MetricKMedianRecovery.BitMachine.PolyComputes.comp`, `OAI.MetricKMedianRecovery.BitMachine.PolyComputes.mapLeft`, `OAI.MetricKMedianRecovery.BitMachine.PolynomialCounter`, `OAI.MetricKMedianRecovery.BitMachine.ProductBits.cfg`, `OAI.MetricKMedianRecovery.BitMachine.ProductBits.copy_phase`, `OAI.MetricKMedianRecovery.BitMachine.ProductBits.done`, `OAI.MetricKMedianRecovery.BitMachine.ProductBits.duplicate_computes`, `OAI.MetricKMedianRecovery.BitMachine.ProductBits.encode_phase`, `OAI.MetricKMedianRecovery.BitMachine.ProductBits.program`, `OAI.MetricKMedianRecovery.BitMachine.ProductBits.restore_phase`, `OAI.MetricKMedianRecovery.BitMachine.ProductBits.reverse_phase`, `OAI.MetricKMedianRecovery.BitMachine.ProductBits.store`, `OAI.MetricKMedianRecovery.BitMachine.Program.maxPush`, `OAI.MetricKMedianRecovery.BitMachine.SameIO.Stack`, `OAI.MetricKMedianRecovery.BitMachine.WordOperations.store`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedianRecovery_Machines_Program`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/Program.lean), [`KMedianRecovery_Recovery_CommonDen`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CommonDen.lean), [`KMedianRecovery_Recovery_Copies`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Copies.lean), [`KMedianRecovery_Recovery_EvalTrans`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/EvalTrans.lean), [`KMedianRecovery_Recovery_ExecutionState`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/ExecutionState.lean), [`KMedianRecovery_Recovery_FrameStacks`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/FrameStacks.lean), [`KMedianRecovery_Recovery_Iterate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Iterate.lean), [`KMedianRecovery_Recovery_Stack`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Stack.lean), [`KMedianRecovery_Recovery_Stack2`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Stack2.lean), [`KMedianRecovery_Recovery_StackLength`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/StackLength.lean), [`KMedianRecovery_Recovery_Store`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Store.lean), [`KMedianRecovery_Recovery_Store2`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Store2.lean).
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K000` and `Q238K001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238K017`, `Q238K018`, `Q238K019`, `Q238K021`, `Q238K022` and `Q238K023`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K000
import Definitions.Def_Q238K001

section
-- module Solutions.Q238_KM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
end OAICompat434

end OAI
end

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

def integerVector {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) : Fin n → ℤ :=
  let ar := Vector.ofFn (fun i => scaled (data A b) (i,none))
  fun i => ar[i]

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FrameStacks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

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
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.discardPrefix_pairBits _root_.OAI.MetricKMedianRecovery.BitMachine.extractPrefix_pairBits
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

noncomputable def outputs (bits out : List Bool) (n : ℕ)
    (h : TM2OutputsInTime p.machine (extractPrefix bits) (some out) n) :
    TM2OutputsInTime (program p).machine bits (some (pairBits (out,discardPrefix bits)))
      (n+2*bits.length+2*out.length+4) := by
  let xs := extractPrefix bits
  let ys := discardPrefix bits
  have hparse := parse_phase p bits []
  simp only [List.append_nil] at hparse
  have hrestore := restore_phase p xs.reverse [] ys
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at hrestore
  rw [pure_nil] at hrestore
  have hrun : EvalsToInTime (program p).machine.step
      (runCfg p ys (initList p.machine xs)) (some (runCfg p ys (haltList p.machine out))) n := by
    refine ⟨⟨h.steps,?_⟩,h.steps_le_m⟩
    exact iterate_transfer _ _ (runCfg p ys) (run_step p ys) h.steps _ _ h.evals_in_steps
  rw [run_initial,run_final] at hrun
  have hreverse := reverse_phase p out [] ys
  simp only [List.append_nil] at hreverse
  have hencode := encode_phase p out.reverse (false::ys)
  simp only [List.reverse_reverse,List.length_reverse] at hencode
  have hh := eval_trans hparse (eval_trans hrestore (eval_trans hrun (eval_trans hreverse hencode)))
  simp only [TM2OutputsInTime,Option.map_some,initial,final,pairBits,List.append_assoc,List.cons_append,List.nil_append]
  apply time_mono hh
  have hl : xs.length≤bits.length := extractPrefix_length bits
  omega

end MapLeft

noncomputable def PolyComputes.mapLeft {f : List Bool → List Bool} (hf : PolyComputes f) :
    PolyComputes (fun bits => pairBits (f (extractPrefix bits),discardPrefix bits)) where
  program := MapLeft.program hf.program
  time := hf.time+2*Polynomial.X+2*(Polynomial.X+hf.time*Polynomial.C hf.program.maxPush)+4
  outputs bits := by
    have hh := MapLeft.outputs hf.program bits (f (extractPrefix bits))
      (hf.time.eval (extractPrefix bits).length) (hf.outputs (extractPrefix bits))
    have hx := extractPrefix_length bits
    have ho := hf.program.output_length (hf.outputs (extractPrefix bits))
    have ht := polynomial_monotone hf.time hx
    apply time_mono hh
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_C]
    nlinarith

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Stack2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace SameIO
variable (p : Program)

abbrev Stack := p.K ⊕ Unit

end SameIO

end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Store
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.discardPrefix_pairBits _root_.OAI.MetricKMedianRecovery.BitMachine.extractPrefix_pairBits
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

abbrev program (duplicate : Bool) : Program where
  K := Fin 3
  input := 0
  output := 0
  Label := Fin 4
  main := 0
  State := Option Bool
  initial := none
  code l := if l=0 then
    if duplicate then
      .pop 0 (fun _ b => b)
        (.branch Option.isSome
          (.push 1 (fun s => s.getD false)
            (.push 2 (fun s => s.getD false)
              (.load (fun _=>none) (.goto (fun _=>0)))))
          (.load (fun _=>none) (.goto (fun _=>2))))
    else
      .pop 0 (fun _ b => b)
        (.branch (fun s => decide (s=some true))
          (.pop 0 (fun _ b => b)
            (.branch Option.isSome
              (.push 1 (fun s => s.getD false) (.load (fun _=>none) (.goto (fun _=>0))))
              (.load (fun _=>none) (.goto (fun _=>1)))))
          (.load (fun _=>none) (.goto (fun _=>1))))
    else if l=1 then
      .pop 0 (fun _ b => b)
        (.branch Option.isSome
          (.push 2 (fun s => s.getD false) (.load (fun _=>none) (.goto (fun _=>1))))
          (.load (fun _=>none) (.goto (fun _=>2))))
    else if l=2 then
      .pop 1 (fun _ b => b)
        (.branch Option.isSome
          (.push 0 (fun s => s.getD false) (.load (fun _=>none) (.goto (fun _=>2))))
          (.push 0 (fun _=>false) (.load (fun _=>none) (.goto (fun _=>3)))))
    else
      .pop 2 (fun _ b => b)
        (.branch Option.isSome
          (.push 0 (fun s=>s.getD false)
            (.push 0 (fun _=>true) (.load (fun _=>none) (.goto (fun _=>3)))))
          (.load (fun _=>none) .halt))

def cfg (mode : Bool) (l : Fin 4) (a b c : List Bool) : (program mode).machine.Cfg :=
  ⟨some l,none,store a b c⟩
def done (mode : Bool) (out : List Bool) : (program mode).machine.Cfg :=
  ⟨none,none,store out [] []⟩
lemma copy_nil (b c : List Bool) :
    (program true).machine.step (cfg true 0 [] b c)=some (cfg true 2 [] b c) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0]; rfl
lemma copy_cons (x : Bool) (a b c : List Bool) :
    (program true).machine.step (cfg true 0 (x::a) b c)=some (cfg true 0 a (x::b) (x::c)) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0,upd1,upd2]; rfl
lemma parse_nil (b : List Bool) :
    (program false).machine.step (cfg false 0 [] b [])=some (cfg false 1 [] b []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0]; rfl
lemma parse_false (a b : List Bool) :
    (program false).machine.step (cfg false 0 (false::a) b [])=some (cfg false 1 a b []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0]; rfl
lemma parse_one (b : List Bool) :
    (program false).machine.step (cfg false 0 [true] b [])=some (cfg false 1 [] b []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0]; rfl
lemma parse_true (x : Bool) (a b : List Bool) :
    (program false).machine.step (cfg false 0 (true::x::a) b [])=some (cfg false 0 a (x::b) []) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0,upd1]; rfl
lemma reverse_nil (mode : Bool) (b c : List Bool) :
    (program mode).machine.step (cfg mode 1 [] b c)=some (cfg mode 2 [] b c) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0]; rfl
lemma reverse_cons (mode x : Bool) (a b c : List Bool) :
    (program mode).machine.step (cfg mode 1 (x::a) b c)=some (cfg mode 1 a b (x::c)) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd0,upd2]; rfl
lemma restore_nil (mode : Bool) (a c : List Bool) :
    (program mode).machine.step (cfg mode 2 a [] c)=some (cfg mode 3 (false::a) [] c) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd1,upd0]; rfl
lemma restore_cons (mode x : Bool) (a b c : List Bool) :
    (program mode).machine.step (cfg mode 2 a (x::b) c)=some (cfg mode 2 (x::a) b c) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd1,upd0]; rfl
lemma encode_nil (mode : Bool) (a : List Bool) :
    (program mode).machine.step (cfg mode 3 a [] [])=some (done mode a) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,done,upd2]; rfl
lemma encode_cons (mode x : Bool) (a c : List Bool) :
    (program mode).machine.step (cfg mode 3 a [] (x::c))=some (cfg mode 3 (true::x::a) [] c) := by
  simp [FinTM2.step,program,TM2.step,TM2.stepAux,cfg,upd2,upd0]; rfl

noncomputable def copy_phase (a b c : List Bool) :
    EvalsToInTime (program true).machine.step (cfg true 0 a b c)
      (some (cfg true 2 [] (a.reverse++b) (a.reverse++c))) (a.length+1) := by
  induction a generalizing b c with
  | nil => exact one_step (copy_nil b c)
  | cons x a ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using step_then (copy_cons x a b c) (ih (x::b) (x::c))

noncomputable def reverse_phase (mode : Bool) (a b c : List Bool) :
    EvalsToInTime (program mode).machine.step (cfg mode 1 a b c)
      (some (cfg mode 2 [] b (a.reverse++c))) (a.length+1) := by
  induction a generalizing c with
  | nil => exact one_step (reverse_nil mode b c)
  | cons x a ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using step_then (reverse_cons mode x a b c) (ih (x::c))

noncomputable def restore_phase (mode : Bool) (a b c : List Bool) :
    EvalsToInTime (program mode).machine.step (cfg mode 2 a b c)
      (some (cfg mode 3 (false::(b.reverse++a)) [] c)) (b.length+1) := by
  induction b generalizing a with
  | nil => exact one_step (restore_nil mode a c)
  | cons x b ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using step_then (restore_cons mode x a b c) (ih (x::a))

noncomputable def encode_phase (mode : Bool) (a c : List Bool) :
    EvalsToInTime (program mode).machine.step (cfg mode 3 a [] c)
      (some (done mode (c.reverse.flatMap (fun b=>[true,b])++a))) (c.length+1) := by
  induction c generalizing a with
  | nil => exact one_step (encode_nil mode a)
  | cons x c ih =>
    simpa only [List.length_cons,List.reverse_cons,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      step_then (encode_cons mode x a c) (ih (true::x::a))

lemma initial (mode : Bool) (xs : List Bool) : initList (program mode).machine xs=cfg mode 0 xs [] [] := by
  rw [initList_bool]
  congr 1
  funext i; fin_cases i <;> simp [program,store]
lemma final (mode : Bool) (xs : List Bool) : haltList (program mode).machine xs=done mode xs := by
  rw [haltList_bool]
  congr 1
  funext i; fin_cases i <;> simp [program,store]

noncomputable def duplicate_computes : PolyComputes (fun xs => pairBits (xs,xs)) where
  program := program true
  time := 3*Polynomial.X+3
  outputs xs := by
    have h1 := copy_phase xs [] []
    have h2 := restore_phase true [] xs.reverse xs.reverse
    have h3 := encode_phase true (false::xs) xs.reverse
    simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h1 h2 h3
    have hh := eval_trans h1 (eval_trans h2 h3)
    simp only [TM2OutputsInTime,Option.map_some,initial,final,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X,pairBits,List.append_assoc,List.cons_append,List.nil_append]
    exact time_mono hh (by omega)

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
@[simp] lemma store0 (xs ys : List Bool) : store xs ys 0=xs := rfl
@[simp] lemma store1 (xs ys : List Bool) : store xs ys 1=ys := rfl
lemma upd0 (xs ys zs : List Bool) : Function.update (store xs ys) 0 zs=store zs ys := by
  funext i; fin_cases i <;> simp [store]

end WordOperations

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Iterate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BirdRationalIteration
open Matrix
open scoped BigOperators

def integral {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j=>BirdRational.scaled (flat A) (i,j)
end MetricKMedianRecovery.BirdRationalIteration

end OAI
end


