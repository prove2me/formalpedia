-- Prove2me | Definitions.Def_OAIQ035K000
-- name    : OAIQ035K000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:53:06.70057+00:00
-- url     : https://prove2.me/theorems/b1bb9603-a222-443f-8142-1b8cab3b0de9
-- title:
--   Definitions bundle OAIQ035K000 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 136 declarations of OpenAI's Lean: 77 definitions, 6 inductive types or structures, 1 instance and 52 theorems. The definitions and types are `OAI.MetricKMedian.Analytic.A`, `OAI.MetricKMedian.Analytic.B`, `OAI.MetricKMedian.Analytic.P`, `OAI.MetricKMedian.Analytic.aTaylor`, `OAI.MetricKMedian.Analytic.coefficient`, `OAI.MetricKMedian.Analytic.expApprox`, `OAI.MetricKMedian.Analytic.m`, `OAI.MetricKMedian.Analytic.moment`, `OAI.MetricKMedian.Analytic.pTaylor`, `OAI.MetricKMedian.Analytic.rateDerivative`, `OAI.MetricKMedian.Analytic.taylorError`, `OAI.MetricKMedian.Analytic.timeRate`, `OAI.MetricKMedian.Binary.AdditionLoop.S`, `OAI.MetricKMedian.Binary.AdditionLoop.body`, `OAI.MetricKMedian.Binary.AdditionLoop.ec`, `OAI.MetricKMedian.Binary.AdditionLoop.empty`, `OAI.MetricKMedian.Binary.AdditionLoop.enc`, `OAI.MetricKMedian.Binary.AdditionLoop.ey`, `OAI.MetricKMedian.Binary.AdditionLoop.finish`, `OAI.MetricKMedian.Binary.AdditionLoop.next`, `OAI.MetricKMedian.Binary.Compose.Key`, `OAI.MetricKMedian.Binary.Compose.Label`, `OAI.MetricKMedian.Binary.Compose.State`, `OAI.MetricKMedian.Binary.Compose.auxiliary`, `OAI.MetricKMedian.Binary.Compose.clean`, `OAI.MetricKMedian.Binary.Compose.code`, `OAI.MetricKMedian.Binary.Compose.following`, `OAI.MetricKMedian.Binary.Compose.left`, `OAI.MetricKMedian.Binary.Compose.machine`, `OAI.MetricKMedian.Binary.Compose.phaseLabel`, `OAI.MetricKMedian.Binary.Compose.right`, `OAI.MetricKMedian.Binary.Compose.source`, `OAI.MetricKMedian.Binary.Compose.target`, `OAI.MetricKMedian.Binary.Compose.transfer`, `OAI.MetricKMedian.Binary.Compose.transferCfg`, `OAI.MetricKMedian.Binary.Embedding`, `OAI.MetricKMedian.Binary.Embedding.cfg`, `OAI.MetricKMedian.Binary.Embedding.stmt`, `OAI.MetricKMedian.Binary.FiniteTransducer.Q`, `OAI.MetricKMedian.Binary.FiniteTransducer.prefixes` and 43 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Analysis_Coefficients`, `KMedian_Analysis_TaylorExpansion`, `KMedian_Binary_BinaryAddition`, `KMedian_Binary_BooleanComposition`, `KMedian_Binary_BooleanEmbedding`, `KMedian_Binary_BooleanEncoding`, `KMedian_Binary_BooleanFinite`, `KMedian_Binary_BooleanListPrimitives`, `KMedian_Binary_BooleanMachine`, `KMedian_Binary_BooleanParallelTransducer`, `KMedian_Binary_BooleanPolynomial`, `KMedian_Binary_BooleanTransducer`, `KMedian_Geometry_MomentAnalysis`, `KMedian_Geometry_TimeAdvance`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K013`, `OAIQ035K014`, `OAIQ035K015`, `OAIQ035K016`, `OAIQ035K017`, `OAIQ035K018`, `OAIQ035K019`, `OAIQ035K020`, `OAIQ035K021`, `OAIQ035K023`, `OAIQ035K024`, `OAIQ035K025`, `OAIQ035K036`, `OAIQ035K038` and `OAIQ035K062`; the statements `OAI.MetricKMedian.Analytic.P_le_half`, `OAI.MetricKMedian.Analytic.P_nonneg`, `OAI.MetricKMedian.Analytic.coefficient_identity_drift`, `OAI.MetricKMedian.Analytic.m_nonneg`, `OAI.MetricKMedian.Certificates.T1_actual_pos`, `OAI.MetricKMedian.Certificates.T2_actual_pos`, `OAI.MetricKMedian.Certificates.Yprime_actual_bounds`, `OAI.MetricKMedian.Certificates.a_approximation`, `OAI.MetricKMedian.Certificates.k_envelope`, `OAI.MetricKMedian.Certificates.p_approximation` and `OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift`; the proofs of `OAI.MetricKMedian.Analytic.P_le_half`, `OAI.MetricKMedian.Analytic.P_nonneg`, `OAI.MetricKMedian.Analytic.coefficient_identity_drift`, `OAI.MetricKMedian.Analytic.m_nonneg`, `OAI.MetricKMedian.Certificates.T1_actual_pos`, `OAI.MetricKMedian.Certificates.T2_actual_pos`, `OAI.MetricKMedian.Certificates.Yprime_actual_bounds`, `OAI.MetricKMedian.Certificates.a_approximation`, `OAI.MetricKMedian.Certificates.k_envelope`, `OAI.MetricKMedian.Certificates.p_approximation` and `OAI.MetricKMedian.Preparation.support_repaired_cost`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ035_KM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.Analytic

noncomputable def A (x : ℝ) : ℝ :=
  1 + 2 * ∫ t : ℝ in 0..1, (1 - Real.exp (-t * x))

noncomputable def P (x : ℝ) : ℝ :=
  ∫ t : ℝ in 0..1, t * Real.exp (-t * x)

noncomputable def B (x : ℝ) : ℝ := 2 * P x

noncomputable def m (x : ℝ) : ℝ := A x - 1 - 2 * x * P x

@[simp] theorem A_zero : A 0 = 1 := by simp [A]

@[simp] theorem P_zero : P 0 = 1 / 2 := by
  simp only [P, mul_zero, Real.exp_zero, mul_one]
  norm_num

end MetricKMedian.Analytic


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_TaylorExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Analytic

noncomputable def expApprox (n : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, u ^ k / (k.factorial : ℝ)

noncomputable def pTaylor (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-x) ^ k / ((k.factorial : ℝ) * (k + 2))

noncomputable def aTaylor (n : ℕ) (x : ℝ) : ℝ :=
  3 - 2 * ∑ k ∈ Finset.range n, (-x) ^ k / ((k.factorial : ℝ) * (k + 1))

noncomputable def taylorError : ℝ := 14 / (6227020800 * 13)

end MetricKMedian.Analytic


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Turing StateTransition Function Finset

structure Machine where
  K : Type
  [decK : DecidableEq K]
  [finK : Fintype K]
  input : K
  output : K
  Label : Type
  [finLabel : Fintype Label]
  main : Label
  State : Type
  [finState : Fintype State]
  initial : State
  code : Label → TM2.Stmt (fun _ : K => Bool) Label State

attribute [instance] Machine.decK Machine.finK Machine.finLabel Machine.finState

namespace Machine

def tm (M : Machine) : FinTM2 where
  K := M.K
  k₀ := M.input
  k₁ := M.output
  Γ _ := Bool
  Λ := M.Label
  main := M.main
  σ := M.State
  initialState := M.initial
  m := M.code

abbrev Cfg (M : Machine) := TM2.Cfg (fun _ : M.K => Bool) M.Label M.State

def initialCfg (M : Machine) (s : List Bool) : M.Cfg :=
  ⟨some M.main, M.initial, fun k => if k=M.input then s else []⟩

def finalCfg (M : Machine) (s : List Bool) : M.Cfg :=
  ⟨none, M.initial, fun k => if k=M.output then s else []⟩

@[simp] theorem init_eq (M : Machine) (s : List Bool) :
    initList M.tm s=M.initialCfg s := by
  rfl

@[simp] theorem halt_eq (M : Machine) (s : List Bool) :
    haltList M.tm s=M.finalCfg s := by
  rfl

abbrev step (M : Machine) : M.Cfg → Option M.Cfg := TM2.step M.code

end Machine

theorem cfg_ext {K L S : Type} {a b : TM2.Cfg (fun _ : K => Bool) L S}
    (hl : a.l=b.l) (hv : a.var=b.var) (hs : a.stk=b.stk) : a=b := by
  cases a
  cases b
  cases hl
  cases hv
  cases hs
  rfl

inductive Trace {α : Type*} (f : α → Option α) : ℕ → α → α → Prop
  | refl (a : α) : Trace f 0 a a
  | cons {n : ℕ} {a b c : α} : f a=some b → Trace f n b c → Trace f (n+1) a c

namespace Trace
variable {α β : Type*} {f : α → Option α}

theorem trans {n m : ℕ} {a b c : α} (h : Trace f n a b) (g : Trace f m b c) :
    Trace f (n+m) a c := by
  induction h with
  | refl => simpa using g
  | cons hs ht ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using cons hs (ih g)

theorem map {g : β → Option β} (e : α → β)
    (he : ∀ a b, f a=some b → g (e a)=some (e b))
    {n : ℕ} {a b : α} (h : Trace f n a b) : Trace g n (e a) (e b) := by
  induction h with
  | refl => exact refl _
  | cons hs _ ih => exact cons (he _ _ hs) ih

theorem iterate_eq {n : ℕ} {a b : α} (h : Trace f n a b) :
    (flip bind f)^[n] (some a)=some b := by
  induction h with
  | refl => rfl
  | cons hs ht ih =>
      rw [Function.iterate_succ_apply,show (flip bind f) (some _)=_ from hs]
      exact ih

end Trace

namespace Machine
variable {K L S : Type} [DecidableEq K]

def pushes : TM2.Stmt (fun _ : K => Bool) L S → ℕ
  | .push _ _ q => 1+pushes q
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ => 0
  | .halt => 0

def volume [Fintype K] (s : K → List Bool) : ℕ := ∑ k, (s k).length

variable [Fintype K]

def growth (M : Machine) : ℕ := ∑ l, pushes (M.code l)

@[simp] theorem initial_volume (M : Machine) (s : List Bool) :
    volume (M.initialCfg s).stk=s.length := by
  classical
  simp only [initialCfg,volume,apply_ite List.length,List.length_nil]
  simp

@[simp] theorem final_volume (M : Machine) (s : List Bool) :
    volume (M.finalCfg s).stk=s.length := by
  classical
  simp only [finalCfg,volume,apply_ite List.length,List.length_nil]
  simp

end Machine
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Binary
open Turing Function

structure Embedding (K L S K' L' S' : Type) [DecidableEq K] [DecidableEq K'] where
  key : K → K'
  read : S' → S
  write : S' → S → S'
  state : S → S'
  read_state : ∀ v, read (state v)=v
  write_state : ∀ v w, write (state v) w=state w
  stack : (K → List Bool) → K' → List Bool
  stack_key : ∀ s k, stack s (key k)=s k
  stack_update : ∀ s k x, stack (update s k x)=update (stack s) (key k) x
  label : L → L'
  halted : Option L'
  stop : TM2.Stmt (fun _ : K' => Bool) L' S'
  stop_spec : ∀ v s, TM2.stepAux stop (state v) (stack s)=⟨halted,state v,stack s⟩

namespace Embedding
variable {K L S K' L' S' : Type} [DecidableEq K] [DecidableEq K']
variable (E : Embedding K L S K' L' S')

def stmt : TM2.Stmt (fun _ : K => Bool) L S → TM2.Stmt (fun _ : K' => Bool) L' S'
  | .push k f q => .push (E.key k) (fun v => f (E.read v)) (stmt q)
  | .peek k f q => .peek (E.key k) (fun v x => E.write v (f (E.read v) x)) (stmt q)
  | .pop k f q => .pop (E.key k) (fun v x => E.write v (f (E.read v) x)) (stmt q)
  | .load f q => .load (fun v => E.write v (f (E.read v))) (stmt q)
  | .branch f q r => .branch (fun v => f (E.read v)) (stmt q) (stmt r)
  | .goto f => .goto (fun v => E.label (f (E.read v)))
  | .halt => E.stop

def cfg (a : TM2.Cfg (fun _ : K => Bool) L S) : TM2.Cfg (fun _ : K' => Bool) L' S' :=
  ⟨a.l.elim E.halted (fun l => some (E.label l)),E.state a.var,E.stack a.stk⟩

end Embedding
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Binary
open Turing Function

namespace Compose
variable (M N : Machine)

abbrev Key := M.K ⊕ (Unit ⊕ N.K)
abbrev Label := M.Label ⊕ (Bool ⊕ N.Label)
abbrev State := M.State × N.State × Option Bool

abbrev phaseLabel (b : Bool) : Label M N := .inr (.inl b)
abbrev auxiliary : Key M N := .inr (.inl ())

def left : Embedding M.K M.Label M.State (Key M N) (Label M N) (State M N) where
  key := Sum.inl
  read := Prod.fst
  write v x := (x,v.2)
  state v := (v,N.initial,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := Sum.elim s (fun _ => [])
  stack_key _ _ := rfl
  stack_update s k x := by
    funext j
    rcases j with j | j
    · simp only [update_apply,Sum.elim_inl,Sum.inl.injEq]
    · simp only [update_apply,Sum.elim_inr,Sum.inr_ne_inl,ite_false]
  label := Sum.inl
  halted := some (phaseLabel M N false)
  stop := .goto (fun _ => phaseLabel M N false)
  stop_spec _ _ := rfl

def right : Embedding N.K N.Label N.State (Key M N) (Label M N) (State M N) where
  key k := .inr (.inr k)
  read v := v.2.1
  write v x := (v.1,x,v.2.2)
  state v := (M.initial,v,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := Sum.elim (fun _ => []) (Sum.elim (fun _ => []) s)
  stack_key _ _ := rfl
  stack_update s k x := by
    funext j
    rcases j with j | j
    · simp only [update_apply,Sum.elim_inl,Sum.inl_ne_inr,ite_false]
    · rcases j with j | j <;> simp only [update_apply,Sum.elim_inl,Sum.elim_inr,Sum.inr.injEq,Sum.inl_ne_inr,ite_false]
  label l := .inr (.inr l)
  halted := none
  stop := .halt
  stop_spec _ _ := rfl

def source (b : Bool) : Key M N := if b then auxiliary M N else .inl M.output

def target (b : Bool) : Key M N := if b then .inr (.inr N.input) else auxiliary M N

 theorem source_ne_target (b : Bool) : source M N b ≠ target M N b := by
  cases b <;> simp [source,target,auxiliary]

def following (b : Bool) : Label M N :=
  if b then .inr (.inr N.main) else phaseLabel M N true

def clean (v : State M N) : State M N := (v.1,v.2.1,none)

def transfer (b : Bool) : TM2.Stmt (fun _ : Key M N => Bool) (Label M N) (State M N) :=
  .pop (source M N b) (fun v c => (v.1,v.2.1,c))
    (.branch (fun v => v.2.2.isSome)
      (.push (target M N b) (fun v => v.2.2.getD false)
        (.load (clean M N) (.goto (fun _ => phaseLabel M N b))))
      (.load (clean M N) (.goto (fun _ => following M N b))))

def code : Label M N → TM2.Stmt (fun _ : Key M N => Bool) (Label M N) (State M N)
  | .inl l => (left M N).stmt (M.code l)
  | .inr (.inl b) => transfer M N b
  | .inr (.inr l) => (right M N).stmt (N.code l)

abbrev machine : Machine where
  K := Key M N
  input := .inl M.input
  output := .inr (.inr N.output)
  Label := Label M N
  main := .inl M.main
  State := State M N
  initial := (M.initial,N.initial,none)
  code := code M N

 theorem code_left (l : M.Label) : (machine M N).code ((left M N).label l)=
    (left M N).stmt (M.code l) := rfl

 theorem code_right (l : N.Label) : (machine M N).code ((right M N).label l)=
    (right M N).stmt (N.code l) := rfl

 theorem initial_left (s : List Bool) : (left M N).cfg (M.initialCfg s)=
    (machine M N).initialCfg s := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [Embedding.cfg,left,Machine.initialCfg,machine]

 theorem final_right (s : List Bool) : (right M N).cfg (N.finalCfg s)=
    (machine M N).finalCfg s := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [Embedding.cfg,right,Machine.finalCfg,machine]
  · rcases k with k | k <;> simp [Embedding.cfg,right,Machine.finalCfg,machine]

end Compose

def twoStacks {K : Type} [DecidableEq K] (a b : K) (xs ys : List Bool) (k : K) : List Bool :=
  if k=a then xs else if k=b then ys else []

@[simp] theorem twoStacks_source {K : Type} [DecidableEq K] (a b : K) (xs ys : List Bool) :
    twoStacks a b xs ys a=xs := by simp [twoStacks]

@[simp] theorem twoStacks_target {K : Type} [DecidableEq K] {a b : K} (h : a≠b)
    (xs ys : List Bool) : twoStacks a b xs ys b=ys := by simp [twoStacks,h.symm]

 theorem twoStacks_move {K : Type} [DecidableEq K] {a b : K} (h : a≠b)
    (x : Bool) (xs ys : List Bool) :
    update (update (twoStacks a b (x::xs) ys) a xs) b (x::ys)=twoStacks a b xs (x::ys) := by
  funext k
  by_cases ha : k=a
  · subst k; simp [h,twoStacks]
  · by_cases hb : k=b
    · subst k; simp [h.symm,twoStacks]
    · simp [ha,hb,twoStacks]

 theorem twoStacks_pop_empty {K : Type} [DecidableEq K] (a b : K) (ys : List Bool) :
    update (twoStacks a b [] ys) a []=twoStacks a b [] ys := by
  funext k
  by_cases h : k=a <;> simp [twoStacks,h]

namespace Compose
variable (M N : Machine)

def transferCfg (b : Bool) (xs ys : List Bool) : (machine M N).Cfg :=
  ⟨some (phaseLabel M N b), (M.initial,N.initial,none),
    twoStacks (source M N b) (target M N b) xs ys⟩

 theorem transfer_cons (b x : Bool) (xs ys : List Bool) :
    (machine M N).step (transferCfg M N b (x::xs) ys)=
      some (transferCfg M N b xs (x::ys)) := by
  change some (TM2.stepAux (transfer M N b) (M.initial,N.initial,none)
    (twoStacks (source M N b) (target M N b) (x::xs) ys))=some (transferCfg M N b xs (x::ys))
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.getD_some,clean]
  rw [update_of_ne (Ne.symm (source_ne_target M N b)),twoStacks_target (source_ne_target M N b)]
  rw [twoStacks_move (source_ne_target M N b)]
  rfl

 theorem transfer_run (b : Bool) (xs ys : List Bool) :
    Trace (machine M N).step xs.length (transferCfg M N b xs ys)
      (transferCfg M N b [] (xs.reverse++ys)) := by
  induction xs generalizing ys with
  | nil => exact Trace.refl _
  | cons x xs ih =>
      have h := Trace.cons (transfer_cons M N b x xs ys) (ih (x::ys))
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using h

 theorem transfer_empty (b : Bool) (ys : List Bool) :
    (machine M N).step (transferCfg M N b [] ys)=
      some ⟨some (following M N b),(M.initial,N.initial,none),
        twoStacks (source M N b) (target M N b) [] ys⟩ := by
  change some (TM2.stepAux (transfer M N b) (M.initial,N.initial,none)
    (twoStacks (source M N b) (target M N b) [] ys))=_
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false,clean,twoStacks_pop_empty]

 theorem left_final_transfer (xs : List Bool) :
    (left M N).cfg (M.finalCfg xs)=transferCfg M N false xs [] := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [Embedding.cfg,left,Machine.finalCfg,transferCfg,twoStacks,source,target,auxiliary,Sum.inl.injEq,Sum.inl_ne_inr]
  · rcases k with k | k <;>
      simp [Embedding.cfg,left,Machine.finalCfg,transferCfg,twoStacks,source,target,auxiliary,Sum.inr.injEq,Sum.inr_ne_inl]

 theorem transfer_change (ys : List Bool) :
    (machine M N).step (transferCfg M N false [] ys)=some (transferCfg M N true ys []) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [transferCfg,source,target,twoStacks,auxiliary,Sum.inl.injEq,Sum.inl_ne_inr]
  · rcases k with k | k <;> simp [transferCfg,source,target,twoStacks,auxiliary,Sum.inr.injEq,Sum.inr_ne_inl]

 theorem transfer_end (ys : List Bool) :
    (machine M N).step (transferCfg M N true [] ys)=some ((right M N).cfg (N.initialCfg ys)) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [Embedding.cfg,right,Machine.initialCfg,source,target,twoStacks,auxiliary,Sum.inl_ne_inr]
  · rcases k with k | k <;>
      simp [Embedding.cfg,right,Machine.initialCfg,source,target,twoStacks,auxiliary,Sum.inr.injEq,Sum.inr_ne_inl]

 theorem transfer_full (xs : List Bool) :
    Trace (machine M N).step (2*xs.length+2)
      ((left M N).cfg (M.finalCfg xs)) ((right M N).cfg (N.initialCfg xs)) := by
  rw [left_final_transfer]
  have h₁ := transfer_run M N false xs []
  simp only [List.append_nil] at h₁
  have h₂ := Trace.cons (transfer_change M N xs.reverse) (transfer_run M N true xs.reverse [])
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at h₂
  have h₃ := Trace.cons (transfer_end M N xs) (Trace.refl _)
  have hh := (h₁.trans h₂).trans h₃
  simpa only [show xs.length+(xs.length+1)+(0+1)=2*xs.length+2 by omega] using hh

end Compose
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Turing Polynomial

structure PolyProgram {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) where
  machine : Machine
  time : Polynomial ℕ
  outputs : ∀ a, TM2OutputsInTime machine.tm (ea a) (some (eb (f a))) (time.eval (ea a).length)

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
variable {f : α → β} {g : β → γ}

 noncomputable def sizeBound (P : PolyProgram ea eb f) : Polynomial ℕ :=
  X+P.time*C P.machine.growth

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanTransducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Turing Function Polynomial Finset

structure Transducer where
  Q : Type
  [finiteQ : Fintype Q]
  initial : Q
  next : Q → Bool → Q × List Bool
  finish : Q → List Bool
attribute [instance] Transducer.finiteQ

namespace Transducer
variable (T : Transducer)

def run : T.Q → List Bool → List Bool
  | q, [] => T.finish q
  | q, b::xs => (T.next q b).2 ++ run (T.next q b).1 xs

def width : ℕ := max (univ.sup (fun q => (T.finish q).length))
  (univ.sup (fun x : T.Q × Bool => (T.next x.1 x.2).2.length))

 theorem finish_length (q : T.Q) : (T.finish q).length ≤ T.width :=
  (le_sup (f:=fun q => (T.finish q).length) (mem_univ q)).trans (Nat.le_max_left _ _)

 theorem next_length (q : T.Q) (b : Bool) : (T.next q b).2.length ≤ T.width :=
  (le_sup (f:=fun x : T.Q × Bool => (T.next x.1 x.2).2.length) (mem_univ (q,b))).trans (Nat.le_max_right _ _)

 theorem run_length (q : T.Q) (xs : List Bool) : (T.run q xs).length ≤ T.width*(xs.length+1) := by
  induction xs generalizing q with
  | nil => simpa only [run,List.length_nil,zero_add,mul_one] using T.finish_length q
  | cons b xs ih =>
      have hn := T.next_length q b
      have ht := ih (T.next q b).1
      simp only [run,List.length_append,List.length_cons]
      rw [show xs.length+1+1=(xs.length+1)+1 by rfl,Nat.mul_add,mul_one]
      omega

inductive Key | input | buffer | output deriving DecidableEq
instance instFintypeKey : Fintype Key := ⟨{Key.input,Key.buffer,Key.output},by
  intro k
  cases k <;> simp⟩
open Key
abbrev Label := T.Q ⊕ Unit
abbrev State := Option Bool

def emit : List Bool → TM2.Stmt (fun _ : Key => Bool) (Label T) State →
    TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | [], q => q
  | b::bs, q => .push buffer (fun _ => b) (emit bs q)

 theorem emit_step (bits : List Bool) (q : TM2.Stmt (fun _ : Key => Bool) (Label T) State)
    (v : State) (s : Key → List Bool) :
    TM2.stepAux (emit T bits q) v s=
      TM2.stepAux q v (update s buffer (bits.reverse++s buffer)) := by
  induction bits generalizing s with
  | nil => simp only [emit,List.reverse_nil,List.nil_append,update_eq_self]
  | cons b bs ih =>
      simp only [emit,TM2.stepAux,ih,update_self,update_idem,List.reverse_cons]
      simp only [List.append_assoc,List.singleton_append]

def transfer : TM2.Stmt (fun _ : Key => Bool) (Label T) State :=
  .pop buffer (fun _ b => b)
    (.branch Option.isSome
      (.push output (fun b => b.getD false) (.load (fun _ => none) (.goto (fun _ => .inr ()))))
      (.load (fun _ => none) .halt))

def code : Label T → TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | .inl q => .pop input (fun _ b => b)
      (.branch Option.isSome
        (.branch (fun b => b.getD false)
          (.load (fun _ => none) (emit T (T.next q true).2 (.goto (fun _ => .inl (T.next q true).1))))
          (.load (fun _ => none) (emit T (T.next q false).2 (.goto (fun _ => .inl (T.next q false).1)))))
        (.load (fun _ => none) (emit T (T.finish q) (.goto (fun _ => .inr ())))))
  | .inr _ => transfer T

abbrev machine : Machine where
  K := Key
  input := input
  output := output
  Label := Label T
  main := .inl T.initial
  State := State
  initial := none
  code := code T

def store (xs ys zs : List Bool) : Key → List Bool
  | input => xs
  | buffer => ys
  | output => zs

 theorem stacks_update_input (xs ys zs ts : List Bool) :
    update (store xs ys zs) input ts=store ts ys zs := by
  funext k
  cases k <;> simp [store]

 theorem stacks_update_buffer (xs ys zs ts : List Bool) :
    update (store xs ys zs) buffer ts=store xs ts zs := by
  funext k
  cases k <;> simp [store]

 theorem stacks_update_output (xs ys zs ts : List Bool) :
    update (store xs ys zs) output ts=store xs ys ts := by
  funext k
  cases k <;> simp [store]

def readCfg (q : T.Q) (xs ys : List Bool) : (machine T).Cfg :=
  ⟨some (.inl q),none,store xs ys []⟩

def transferCfg (ys zs : List Bool) : (machine T).Cfg :=
  ⟨some (.inr ()),none,store [] ys zs⟩

 theorem read_cons (q : T.Q) (b : Bool) (xs ys : List Bool) :
    (machine T).step (T.readCfg q (b::xs) ys)=
      some (T.readCfg (T.next q b).1 xs ((T.next q b).2.reverse++ys)) := by
  cases b <;>
    simp [readCfg,TM2.step,code,TM2.stepAux,store,List.head?,List.tail,
      emit_step,stacks_update_input,stacks_update_buffer]

 theorem read_nil (q : T.Q) (ys : List Bool) :
    (machine T).step (T.readCfg q [] ys)=some (T.transferCfg ((T.finish q).reverse++ys) []) := by
  simp [readCfg,transferCfg,TM2.step,code,TM2.stepAux,store,List.head?,List.tail,
    emit_step,stacks_update_input,stacks_update_buffer]

 theorem read_run (q : T.Q) (xs ys : List Bool) :
    Trace (machine T).step (xs.length+1) (T.readCfg q xs ys)
      (T.transferCfg ((T.run q xs).reverse++ys) []) := by
  induction xs generalizing q ys with
  | nil => exact Trace.cons (T.read_nil q ys) (Trace.refl _)
  | cons b xs ih =>
      have h := Trace.cons (T.read_cons q b xs ys) (ih (T.next q b).1 ((T.next q b).2.reverse++ys))
      simpa only [run,List.reverse_append,List.append_assoc,List.length_cons] using h

 theorem transfer_cons (b : Bool) (ys zs : List Bool) :
    (machine T).step (T.transferCfg (b::ys) zs)=some (T.transferCfg ys (b::zs)) := by
  simp [transferCfg,TM2.step,code,transfer,TM2.stepAux,store,List.head?,List.tail,
    stacks_update_buffer,stacks_update_output]

 theorem transfer_nil (zs : List Bool) :
    (machine T).step (T.transferCfg [] zs)=some ((machine T).finalCfg zs) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [Machine.finalCfg,code,transfer,TM2.stepAux,store]

 theorem transfer_run (ys zs : List Bool) :
    Trace (machine T).step (ys.length+1) (T.transferCfg ys zs)
      ((machine T).finalCfg (ys.reverse++zs)) := by
  induction ys generalizing zs with
  | nil => exact Trace.cons (T.transfer_nil zs) (Trace.refl _)
  | cons b ys ih =>
      have h := Trace.cons (T.transfer_cons b ys zs) (ih (b::zs))
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using h

 theorem run_trace (xs : List Bool) :
    Trace (machine T).step (xs.length+(T.run T.initial xs).length+2)
      ((machine T).initialCfg xs) ((machine T).finalCfg (T.run T.initial xs)) := by
  have hi : (machine T).initialCfg xs=T.readCfg T.initial xs [] := by
    apply cfg_ext <;> try rfl
    funext k
    cases k <;> simp [Machine.initialCfg,readCfg,store]
  rw [hi]
  have hr := T.read_run T.initial xs []
  simp only [List.append_nil] at hr
  have h := hr.trans (T.transfer_run (T.run T.initial xs).reverse [])
  simpa only [List.append_nil,List.length_reverse,List.reverse_reverse,
    show xs.length+1+((T.run T.initial xs).length+1)=xs.length+(T.run T.initial xs).length+2 by omega] using h

noncomputable def program : PolyProgram id id (T.run T.initial) where
  machine := machine T
  time := C (T.width+1)*X+C (T.width+2)
  outputs xs := by
    refine ⟨⟨_,(T.run_trace xs).iterate_eq⟩,?_⟩
    have hl := T.run_length T.initial xs
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,id_eq]
    nlinarith

end Transducer
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

def quote : List Bool → List Bool
  | [] => [false]
  | b::bs => true::b::quote bs

@[simp] theorem quote_length (bs : List Bool) : (quote bs).length=2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [quote,List.length_cons,ih]; omega

def encodePair {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (x : α × β) : List Bool :=
  quote (ea x.1)++eb x.2

@[simp] theorem encodePair_length {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (x : α × β) :
    (encodePair ea eb x).length=2*(ea x.1).length+1+(eb x.2).length := by
  simp only [encodePair,List.length_append,quote_length]

namespace WordTransducer

def projecting (tail : Bool) : Transducer where
  Q := Option Bool
  initial := none
  next q b := match q with
    | none => (some (!b),[])
    | some false => (none,if tail then [] else [b])
    | some true => (some true,if tail then [b] else [])
  finish _ := []

 theorem projecting_done (tail : Bool) (xs : List Bool) :
    (projecting tail).run (some true) xs=if tail then xs else [] := by
  induction xs with
  | nil => cases tail <;> rfl
  | cons b xs ih =>
      change (if tail then [b] else [])++(projecting tail).run (some true) xs=_
      rw [ih]
      cases tail <;> simp

 theorem projecting_pair (tail : Bool) (xs ys : List Bool) :
    (projecting tail).run none (quote xs++ys)=if tail then ys else xs := by
  induction xs with
  | nil => exact projecting_done tail ys
  | cons b xs ih =>
      change (if tail then [] else [b])++(projecting tail).run none (quote xs++ys)=_
      rw [ih]
      cases tail <;> simp

end WordTransducer

namespace PolyProgram

 def of_word {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    {g : List Bool → List Bool} (P : PolyProgram id id g)
    (h : ∀ a, g (ea a)=eb (f a)) : PolyProgram ea eb f where
  machine := P.machine
  time := P.time
  outputs a := by simpa only [id_eq,h a] using P.outputs (ea a)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanParallelTransducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.Binary
open Turing Function Polynomial Finset

namespace ParallelTransducer

abbrev Key := Fin 4
abbrev left : Key := 1
abbrev right : Key := 2
abbrev State := Option Bool

end ParallelTransducer
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanListPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

def encodeBool (b : Bool) : List Bool := [b]

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Finset

namespace FiniteTransducer
variable {α β : Type} [Fintype α] (ea : α → List Bool) (eb : β → List Bool) (f : α → β)

noncomputable def prefixes : Finset (List Bool) :=
  univ.biUnion (fun a => (ea a).inits.toFinset)

 theorem mem_prefixes (a : α) (xs ys : List Bool) (h : xs++ys=ea a) : xs∈prefixes ea := by
  classical
  apply mem_biUnion.mpr
  refine ⟨a,mem_univ _,List.mem_toFinset.mpr ?_⟩
  exact (List.mem_inits _ _).mpr ⟨ys,h⟩

abbrev Q := Option {xs : List Bool // xs∈prefixes ea}

noncomputable def state (xs : List Bool) : Q ea :=
  if h : xs∈prefixes ea then some ⟨xs,h⟩ else none

noncomputable abbrev table : Transducer where
  Q := Q ea
  initial := state ea []
  next q b := (match q with | none => none | some xs => state ea (xs.val++[b]),[])
  finish q := match q with
    | none => []
    | some xs => if h : ∃ a, ea a=xs.val then eb (f (Classical.choose h)) else []

 theorem next_state (xs : List Bool) (b : Bool) (h : xs∈prefixes ea) :
    (table ea eb f).next (state ea xs) b=(state ea (xs++[b]),[]) := by
  simp only [table,state,dite_eq_left h]

 theorem finish_state (a : α) (hinj : Injective ea) :
    (table ea eb f).finish (state ea (ea a))=eb (f a) := by
  have hm := mem_prefixes ea a (ea a) [] (List.append_nil _)
  have hex : ∃ a', ea a'=ea a := ⟨a,rfl⟩
  simp only [state,dite_eq_left hm,dite_eq_left hex]
  have he := Classical.choose_spec hex
  rw [hinj he]

 theorem run_state (a : α) (hinj : Injective ea) (xs ys : List Bool) (h : xs++ys=ea a) :
    (table ea eb f).run (state ea xs) ys=eb (f a) := by
  induction ys generalizing xs with
  | nil =>
      have he : xs=ea a := by simpa only [List.append_nil] using h
      rw [he]
      exact finish_state ea eb f a hinj
  | cons b ys ih =>
      change ((table ea eb f).next (state ea xs) b).2 ++
        (table ea eb f).run ((table ea eb f).next (state ea xs) b).1 ys = _
      rw [next_state ea eb f xs b (mem_prefixes ea a xs (b::ys) h),List.nil_append]
      apply ih
      simpa only [List.append_assoc,List.singleton_append] using h

noncomputable def program (hinj : Injective ea) : PolyProgram ea eb f :=
  (table ea eb f).program.of_word (fun a =>
    run_state ea eb f a hinj [] (ea a) rfl)

end FiniteTransducer

 theorem encodeBool_injective : Injective encodeBool := by
  intro a b h
  simpa only [encodeBool,List.cons.injEq,true_and,and_true] using h

 theorem encodePair_injective {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    (ha : Injective ea) (hb : Injective eb) : Injective (encodePair ea eb) := by
  intro a b h
  have hx := congrArg ((WordTransducer.projecting false).run none) h
  have hy := congrArg ((WordTransducer.projecting true).run none) h
  simp only [encodePair,WordTransducer.projecting_pair,Bool.false_eq_true,ite_false,ite_true] at hx hy
  exact Prod.ext (ha hx) (hb hy)

namespace PolyProgram

noncomputable def boolFunction {α β : Type} [Fintype α] (ea : α → List Bool) (eb : β → List Bool)
    (f : α → β) (hinj : Injective ea) : PolyProgram ea eb f :=
  FiniteTransducer.program ea eb f hinj

noncomputable def boolAnd : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => x.1 && x.2) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BinaryAddition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word

def sumBit (a b c : Bool) : Bool := xor (xor a b) c
 def carryBit (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

end Word

namespace AdditionLoop
abbrev S := List Bool × (List Bool × (Bool × List Bool))
abbrev ec : Bool × List Bool → List Bool := encodePair encodeBool id
abbrev ey : List Bool × (Bool × List Bool) → List Bool := encodePair id ec
abbrev enc : S → List Bool := encodePair id ey
 def empty (s : S) : Bool := s.1.isEmpty && s.2.1.isEmpty
 def next (s : S) : S :=
  (s.1.tail,(s.2.1.tail,(Word.carryBit (s.1.head?.getD false) (s.2.1.head?.getD false) s.2.2.1,
    Word.sumBit (s.1.head?.getD false) (s.2.1.head?.getD false) s.2.2.1 :: s.2.2.2)))
 def finish (s : S) : List Bool := (if s.2.2.1 then true::s.2.2.2 else s.2.2.2).reverse
 def body (s : S) : List Bool ⊕ S := if empty s then .inl (finish s) else .inr (next s)

 theorem enc_length (s : S) : (enc s).length=2*s.1.length+2*s.2.1.length+s.2.2.2.length+5 := by
  simp only [enc,ey,ec,encodePair_length,encodeBool,id_eq,List.length_cons,List.length_nil]
  omega

end AdditionLoop

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_MomentAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Analytic

open MeasureTheory Set Filter
open scoped Topology Filter Interval

noncomputable def moment (n : ℕ) (x : ℝ) : ℝ := ∫ t : ℝ in 0..1, t^n*Real.exp (-t*x)

noncomputable def coefficient (x y : ℝ) : ℝ := A x+B x*(y-x)

end MetricKMedian.Analytic
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_TimeAdvance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Analytic
open Set

noncomputable def timeRate (x y : ℝ) : ℝ := 2*x*(y-x)*moment 2 x
noncomputable def rateDerivative (x y : ℝ) : ℝ :=
  2*(y-2*x)*moment 2 x-2*x*(y-x)*moment 3 x

end MetricKMedian.Analytic

end
end

end OAI
end


