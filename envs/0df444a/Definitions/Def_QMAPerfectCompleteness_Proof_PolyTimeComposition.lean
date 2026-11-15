-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
-- name    : QMAPerfectCompleteness_Proof_PolyTimeComposition
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:44:54.1822+00:00
-- url     : https://prove2.me/theorems/103152d7-6f94-4376-b9cc-05365febe436
-- title:
--   Finite-machine simulation and size bounds
-- statement:
--   Defines continuation and label-mapping operations for finite stack machines, together with push-count and stack-length bounds. Successful-execution simulation and polynomial monotonicity supply the bookkeeping for explicit compiler composition, without using an unproved general composition theorem.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/PolyTimeComposition.lean, retained declaration span lines 16–251.

/- Generated from Solutions.PolyTimeComposition by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QAlgorithms_ClassicalStringComputability



/-! Concrete TM2 tools for the uniform compiler layer. No use of the upstream
`proof_wanted TM2ComputableInPolyTime.comp`. -/

open Turing StateTransition

namespace QMAPerfectCompleteness.Uniformity

attribute [local instance] FinTM2.ΛFin

namespace Statement

variable {K Λ σ : Type} {Γ : K → Type}

/-- Maximum number of pushes in one execution of a finite statement. -/
def pushBound : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushBound q + 1
  | .peek _ _ q => pushBound q
  | .pop _ _ q => pushBound q
  | .load _ q => pushBound q
  | .branch _ q r => max (pushBound q) (pushBound r)
  | .goto _ => 0
  | .halt => 0

/-- A statement can grow any stack by at most its syntactic push bound. -/
theorem stepAux_length_bound [DecidableEq K] (q : TM2.Stmt Γ Λ σ)
    (v : σ) (S : ∀ k, List (Γ k)) (L : ℕ) (hS : ∀ k, (S k).length ≤ L) :
    ∀ k, ((TM2.stepAux q v S).stk k).length ≤ L + pushBound q := by
  induction q generalizing v S L with
  | push k f q ih =>
    have hupdate : ∀ j, ((Function.update S k (f v :: S k)) j).length ≤ L + 1 := by
      intro j
      by_cases h : j = k
      · subst j
        simpa using Nat.succ_le_succ (hS k)
      · simpa [Function.update_of_ne h] using (hS j).trans (Nat.le_succ L)
    simpa only [TM2.stepAux, pushBound, Nat.add_assoc, Nat.add_comm 1] using
      ih v _ (L + 1) hupdate
  | peek k f q ih => exact ih _ _ _ hS
  | pop k f q ih =>
    have hupdate : ∀ j, ((Function.update S k (S k).tail) j).length ≤ L := by
      intro j
      by_cases h : j = k
      · subst j
        simp only [Function.update_self, List.length_tail]
        exact (Nat.sub_le _ _).trans (hS k)
      · simpa [Function.update_of_ne h] using hS j
    exact ih _ _ _ hupdate
  | load f q ih => exact ih _ _ _ hS
  | branch f q r ihq ihr =>
    cases hf : f v
    · simpa [TM2.stepAux, hf, pushBound] using fun k =>
        (ihr v S L hS k).trans (Nat.add_le_add_left (Nat.le_max_right _ _) L)
    · simpa [TM2.stepAux, hf, pushBound] using fun k =>
        (ihq v S L hS k).trans (Nat.add_le_add_left (Nat.le_max_left _ _) L)
  | goto f => simpa [TM2.stepAux, pushBound] using hS
  | halt => simpa [TM2.stepAux, pushBound] using hS

/-- Replace halting leaves by a continuation; existing jumps remain jumps. -/
def continueWith (r : TM2.Stmt Γ Λ σ) : TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ σ
  | .push k f q => .push k f (continueWith r q)
  | .peek k f q => .peek k f (continueWith r q)
  | .pop k f q => .pop k f (continueWith r q)
  | .load f q => .load f (continueWith r q)
  | .branch f q q' => .branch f (continueWith r q) (continueWith r q')
  | .goto f => .goto f
  | .halt => r

/-- Continuation semantics, including all local stack and state changes of the first statement. -/
theorem stepAux_continueWith [DecidableEq K] (r q : TM2.Stmt Γ Λ σ)
    (v : σ) (S : ∀ k, List (Γ k)) :
    TM2.stepAux (continueWith r q) v S =
      let c := TM2.stepAux q v S
      match c.l with
      | none => TM2.stepAux r c.var c.stk
      | some _ => c := by
  induction q generalizing v S with
  | push k f q ih => exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f q q' ih ih' => cases hf : f v <;> simp [continueWith, TM2.stepAux, hf, ih, ih']
  | goto f => rfl
  | halt => rfl

/-- Relabel a finite program without altering its stacks or internal state. -/
def mapLabels {Λ' : Type} (e : Λ → Λ') : TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' σ
  | .push k f q => .push k f (mapLabels e q)
  | .peek k f q => .peek k f (mapLabels e q)
  | .pop k f q => .pop k f (mapLabels e q)
  | .load f q => .load f (mapLabels e q)
  | .branch f q r => .branch f (mapLabels e q) (mapLabels e r)
  | .goto f => .goto (e ∘ f)
  | .halt => .halt

/-- Relabel the control component of a configuration. -/
def mapCfgLabels {Λ' : Type} (e : Λ → Λ') (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ' σ :=
  ⟨c.l.map e, c.var, c.stk⟩

/-- Label relabeling commutes exactly with statement execution. -/
theorem stepAux_mapLabels [DecidableEq K] {Λ' : Type} (e : Λ → Λ')
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    TM2.stepAux (mapLabels e q) v S = mapCfgLabels e (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr => cases hf : f v <;> simp [mapLabels, TM2.stepAux, hf, ihq, ihr]
  | goto f => rfl
  | halt => rfl

end Statement

/-- A finite machine has a uniform bound on the number of pushes in one step. -/
def machinePushBound (tm : FinTM2) : ℕ :=
  Finset.univ.sup fun l : tm.Λ => Statement.pushBound (tm.m l)

theorem statement_pushBound_le (tm : FinTM2) (l : tm.Λ) :
    Statement.pushBound (tm.m l) ≤ machinePushBound tm :=
  Finset.le_sup (f := fun l => Statement.pushBound (tm.m l)) (Finset.mem_univ l)

/-- The stack growth of a machine step is bounded uniformly over labels and internal states. -/
theorem step_length_bound (tm : FinTM2) (c c' : tm.Cfg) (hstep : tm.step c = some c')
    (L : ℕ) (hS : ∀ k, (c.stk k).length ≤ L) :
    ∀ k, (c'.stk k).length ≤ L + machinePushBound tm := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => simp [FinTM2.step, TM2.step] at hstep
  | some l =>
    change some (TM2.stepAux (tm.m l) v S) = some c' at hstep
    have heq := Option.some.inj hstep
    subst c' 
    intro k
    exact (Statement.stepAux_length_bound (tm.m l) v S L hS k).trans
      (Nat.add_le_add_left (statement_pushBound_le tm l) L)

/-- After n executed steps, every stack has grown by at most B*n symbols. -/
theorem iterate_length_bound (tm : FinTM2) (c : tm.Cfg) (L : ℕ)
    (hS : ∀ k, (c.stk k).length ≤ L) (n : ℕ) (c' : tm.Cfg)
    (hrun : (fun o : Option tm.Cfg => o.bind tm.step)^[n] (some c) = some c') :
    ∀ k, (c'.stk k).length ≤ L + machinePushBound tm * n := by
  induction n generalizing c' with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq] at hrun
    subst c'
    simpa using hS
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at hrun
    cases hmid : (fun o : Option tm.Cfg => o.bind tm.step)^[n] (some c) with
    | none =>
      have hnone := congrArg (fun o : Option tm.Cfg => o.bind tm.step) hmid
      have himpossible : (none : Option tm.Cfg) = some c' := hnone.symm.trans hrun
      cases himpossible
    | some mid =>
      have hstep : tm.step mid = some c' := by simpa only [hmid, Option.bind_some] using hrun
      have hbound := step_length_bound tm mid c' hstep _ (ih mid hmid)
      simpa only [Nat.mul_succ, Nat.add_assoc] using hbound

/-- Any successful bounded-time computation has linearly bounded output length. -/
theorem output_length_bound (tm : FinTM2) (s : List (tm.Γ tm.k₀))
    (t : List (tm.Γ tm.k₁)) (m : ℕ) (h : TM2OutputsInTime tm s (some t) m) :
    t.length ≤ s.length + machinePushBound tm * m := by
  have hinitial : ∀ k, ((initList tm s).stk k).length ≤ s.length := by
    intro k
    by_cases hk : k = tm.k₀
    · subst k
      simp [initList]
    · simp [initList, hk]
  have hrun : (fun o : Option tm.Cfg => o.bind tm.step)^[h.steps] (some (initList tm s)) =
      some (haltList tm t) := h.evals_in_steps
  have hlen := iterate_length_bound tm (initList tm s) s.length hinitial h.steps
    (haltList tm t) hrun tm.k₁
  have hfinal : ((haltList tm t).stk tm.k₁).length = t.length := by simp [haltList]
  rw [hfinal] at hlen
  exact hlen.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ h.steps_le_m) _)

/-- A polynomial-time machine's output encoding has polynomially bounded length. -/
theorem polytime_output_length_bound {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤
      (ea a).length + machinePushBound h.tm * h.time.eval (ea a).length := by
  simpa only [List.length_map] using output_length_bound h.tm _ _ _ (h.outputsFun a)





/-- A simulation of successful steps is sufficient when the source run ends at a concrete
configuration. Unlike a total simulation, this permits a source halt to be wired to the next
phase of a composite machine. -/
theorem successful_iterate_simulation {A B : Type} (f : A → Option A) (g : B → Option B)
    (tr : A → B) (hstep : ∀ a a', f a = some a' → g (tr a) = some (tr a'))
    (n : ℕ) (a b : A)
    (hrun : (fun o : Option A => o.bind f)^[n] (some a) = some b) :
    (fun o : Option B => o.bind g)^[n] (some (tr a)) = some (tr b) := by
  induction n generalizing b with
  | zero =>
    have hab : a = b := Option.some.inj hrun
    subst b
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at hrun ⊢
    cases hmid : (fun o : Option A => o.bind f)^[n] (some a) with
    | none =>
      have hnone := congrArg (fun o : Option A => o.bind f) hmid
      have himpossible : (none : Option A) = some b := hnone.symm.trans hrun
      cases himpossible
    | some c =>
      rw [ih c hmid]
      apply hstep c b
      simpa only [hmid, Option.bind_some] using hrun



/-- A polynomial over naturals is monotone on natural inputs. -/
theorem natPolynomial_eval_monotone (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab n)







end QMAPerfectCompleteness.Uniformity


