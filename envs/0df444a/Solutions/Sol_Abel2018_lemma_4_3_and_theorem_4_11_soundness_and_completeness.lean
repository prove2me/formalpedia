-- Prove2me | solution 1 for Abel2018.lemma_4_3_and_theorem_4_11_soundness_and_completeness
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:57:30.660038+00:00
-- url     : https://prove2.me/submissions/2e06e3c2-540b-4463-be9c-76c4131d24f0

import Definitions.Def_Abel2018_LogicalRelation

/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/Untyped.agda. These are raw terms; validity is a separate judgment.
-/

namespace Abel2018































































theorem NaturalView.toWhnf {n : Term} : NaturalView n → Whnf n
  | .zero => .zero
  | .succ => .succ
  | .neutral h => .neutral h

theorem SmallTypeView.toWhnf {A : Term} : SmallTypeView A → Whnf A
  | .pi => .pi
  | .nat => .nat
  | .neutral h => .neutral h

theorem FunctionView.toWhnf {f : Term} : FunctionView f → Whnf f
  | .lam => .lam
  | .neutral h => .neutral h

theorem Neutral.rename {t : Term} (ρ : Nat → Nat) : Neutral t → Neutral (Abel2018.rename ρ t)
  | .var n => .var (ρ n)
  | .app h => .app (h.rename ρ)
  | .natrec h => .natrec (h.rename ρ)

theorem Neutral.wk {t : Term} (ρ : Wk) : Neutral t → Neutral (Abel2018.wk ρ t)
  | .var n => .var (wkVar ρ n)
  | .app h => .app (h.wk ρ)
  | .natrec h => .natrec (h.wk ρ)

theorem Whnf.wk {t : Term} (ρ : Wk) : Whnf t → Whnf (Abel2018.wk ρ t)
  | .univ => .univ
  | .pi => .pi
  | .nat => .nat
  | .lam => .lam
  | .zero => .zero
  | .succ => .succ
  | .neutral h => .neutral (h.wk ρ)

theorem NaturalView.wk {t : Term} (ρ : Wk) : NaturalView t → NaturalView (Abel2018.wk ρ t)
  | .zero => .zero
  | .succ => .succ
  | .neutral h => .neutral (h.wk ρ)

theorem SmallTypeView.wk {t : Term} (ρ : Wk) : SmallTypeView t → SmallTypeView (Abel2018.wk ρ t)
  | .pi => .pi
  | .nat => .nat
  | .neutral h => .neutral (h.wk ρ)

theorem FunctionView.wk {t : Term} (ρ : Wk) : FunctionView t → FunctionView (Abel2018.wk ρ t)
  | .lam => .lam
  | .neutral h => .neutral (h.wk ρ)

end Abel2018

/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/Untyped/Properties.agda.
-/

namespace Abel2018

theorem wkVar_lift {ρ ρ' : Wk} (h : ∀ x, wkVar ρ x = wkVar ρ' x) :
    ∀ x, wkVar (.lift ρ) x = wkVar (.lift ρ') x
  | 0 => rfl
  | x + 1 => congrArg (· + 1) (h x)

theorem wkVar_to_wk {ρ ρ' : Wk} (h : ∀ x, wkVar ρ x = wkVar ρ' x) :
    ∀ t, wk ρ t = wk ρ' t
  | .univ => rfl
  | .pi A B => by
      simp [wk, wkVar_to_wk h A, wkVar_to_wk (wkVar_lift h) B]
  | .nat => rfl
  | .var x => congrArg Term.var (h x)
  | .lam t => congrArg Term.lam (wkVar_to_wk (wkVar_lift h) t)
  | .app t u => by
      simp [wk, wkVar_to_wk h t, wkVar_to_wk h u]
  | .zero => rfl
  | .succ t => congrArg Term.succ (wkVar_to_wk h t)
  | .natrec A z s n => by
      simp [wk, wkVar_to_wk (wkVar_lift h) A,
        wkVar_to_wk h z, wkVar_to_wk h s, wkVar_to_wk h n]

theorem wkVar_lift_id : ∀ x, wkVar (.lift .id) x = wkVar .id x
  | 0 => rfl
  | _ + 1 => rfl

theorem wkVar_id (x : Nat) : wkVar .id x = x := rfl

@[simp]
theorem wk_id : ∀ t, wk .id t = t
  | .univ => rfl
  | .pi A B => by
      rw [wk, wk_id A, wkVar_to_wk wkVar_lift_id B, wk_id B]
  | .nat => rfl
  | .var _ => rfl
  | .lam t => by
      rw [wk, wkVar_to_wk wkVar_lift_id t, wk_id t]
  | .app t u => by
      rw [wk, wk_id t, wk_id u]
  | .zero => rfl
  | .succ t => congrArg Term.succ (wk_id t)
  | .natrec A z s n => by
      rw [wk, wkVar_to_wk wkVar_lift_id A, wk_id A, wk_id z, wk_id s, wk_id n]

@[simp]
theorem wk_lift_id (t : Term) : wk (.lift .id) t = t :=
  (wkVar_to_wk wkVar_lift_id t).trans (wk_id t)

theorem wkVar_comp : ∀ (ρ ρ' : Wk) (x : Nat),
    wkVar ρ (wkVar ρ' x) = wkVar (compWk ρ ρ') x
  | .id, _, _ => rfl
  | .step ρ, ρ', x => congrArg (· + 1) (wkVar_comp ρ ρ' x)
  | .lift _, .id, _ => rfl
  | .lift ρ, .step ρ', x => congrArg (· + 1) (wkVar_comp ρ ρ' x)
  | .lift _, .lift _, 0 => rfl
  | .lift ρ, .lift ρ', x + 1 => congrArg (· + 1) (wkVar_comp ρ ρ' x)

theorem wk_comp : ∀ (ρ ρ' : Wk) (t : Term),
    wk ρ (wk ρ' t) = wk (compWk ρ ρ') t
  | ρ, ρ', .univ => rfl
  | ρ, ρ', .pi A B => by
      simp [wk, wk_comp ρ ρ' A, wk_comp (.lift ρ) (.lift ρ') B, compWk]
  | ρ, ρ', .nat => rfl
  | ρ, ρ', .var x => congrArg Term.var (wkVar_comp ρ ρ' x)
  | ρ, ρ', .lam t => by
      simp [wk, wk_comp (.lift ρ) (.lift ρ') t, compWk]
  | ρ, ρ', .app t u => by
      simp [wk, wk_comp ρ ρ' t, wk_comp ρ ρ' u]
  | ρ, ρ', .zero => rfl
  | ρ, ρ', .succ t => congrArg Term.succ (wk_comp ρ ρ' t)
  | ρ, ρ', .natrec A z s n => by
      simp [wk, wk_comp (.lift ρ) (.lift ρ') A,
        wk_comp ρ ρ' z, wk_comp ρ ρ' s, wk_comp ρ ρ' n, compWk]

theorem lift_step_comp : ∀ ρ : Wk,
    compWk (.step .id) ρ = compWk (.lift ρ) (.step .id)
  | .id => rfl
  | .step ρ => congrArg Wk.step (lift_step_comp ρ)
  | .lift _ => rfl

theorem wk1_wk (ρ : Wk) (t : Term) : wk1 (wk ρ t) = wk (.step ρ) t :=
  wk_comp (.step .id) ρ t

theorem lift_wk1 (ρ : Wk) (t : Term) : wk (.lift ρ) (wk1 t) = wk (.step ρ) t := by
  unfold wk1
  rw [wk_comp (.lift ρ) (.step .id) t, ← lift_step_comp ρ]
  rfl

theorem wk1_wk_eq_lift_wk1 (ρ : Wk) (t : Term) :
    wk1 (wk ρ t) = wk (.lift ρ) (wk1 t) :=
  (wk1_wk ρ t).trans (lift_wk1 ρ t).symm

theorem substVar_lift {σ σ' : Subst} (h : ∀ x, σ x = σ' x) :
    ∀ x, liftSubst σ x = liftSubst σ' x
  | 0 => rfl
  | x + 1 => congrArg wk1 (h x)

theorem substVar_to_subst {σ σ' : Subst} (h : ∀ x, σ x = σ' x) :
    ∀ t, subst σ t = subst σ' t
  | .univ => rfl
  | .pi A B => by
      simp [subst, substVar_to_subst h A, substVar_to_subst (substVar_lift h) B]
  | .nat => rfl
  | .var x => h x
  | .lam t => congrArg Term.lam (substVar_to_subst (substVar_lift h) t)
  | .app t u => by
      simp [subst, substVar_to_subst h t, substVar_to_subst h u]
  | .zero => rfl
  | .succ t => congrArg Term.succ (substVar_to_subst h t)
  | .natrec A z s n => by
      simp [subst, substVar_to_subst (substVar_lift h) A,
        substVar_to_subst h z, substVar_to_subst h s, substVar_to_subst h n]

theorem subst_lift_id : ∀ x, liftSubst idSubst x = idSubst x
  | 0 => rfl
  | _ + 1 => rfl

@[simp]
theorem subst_id : ∀ t, subst idSubst t = t
  | .univ => rfl
  | .pi A B => by
      rw [subst, subst_id A, substVar_to_subst subst_lift_id B, subst_id B]
  | .nat => rfl
  | .var _ => rfl
  | .lam t => by
      rw [subst, substVar_to_subst subst_lift_id t, subst_id t]
  | .app t u => by
      rw [subst, subst_id t, subst_id u]
  | .zero => rfl
  | .succ t => congrArg Term.succ (subst_id t)
  | .natrec A z s n => by
      rw [subst, substVar_to_subst subst_lift_id A, subst_id A,
        subst_id z, subst_id s, subst_id n]

theorem subst_lift_wkSubst {ρ : Wk} {σ : Subst} (t : Term) :
    subst (wkSubst (.lift ρ) (liftSubst σ)) t = subst (liftSubst (wkSubst ρ σ)) t := by
  apply substVar_to_subst
  intro x
  cases x with
  | zero => rfl
  | succ x => exact (wk1_wk_eq_lift_wk1 ρ (σ x)).symm

theorem subst_lift_substWk {ρ : Wk} {σ : Subst} (t : Term) :
    subst (substWk (liftSubst σ) (.lift ρ)) t = subst (liftSubst (substWk σ ρ)) t := by
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem wk_subst {ρ : Wk} {σ : Subst} :
    ∀ t, wk ρ (subst σ t) = subst (wkSubst ρ σ) t
  | .univ => rfl
  | .pi A B => by
      rw [subst, wk, subst, wk_subst A, wk_subst B, subst_lift_wkSubst B]
  | .nat => rfl
  | .var _ => rfl
  | .lam t => by
      rw [subst, wk, subst, wk_subst t, subst_lift_wkSubst t]
  | .app t u => by
      rw [subst, wk, subst, wk_subst t, wk_subst u]
  | .zero => rfl
  | .succ t => congrArg Term.succ (wk_subst t)
  | .natrec A z s n => by
      rw [subst, wk, subst, wk_subst A, subst_lift_wkSubst A,
        wk_subst z, wk_subst s, wk_subst n]

theorem subst_wk {ρ : Wk} {σ : Subst} :
    ∀ t, subst σ (wk ρ t) = subst (substWk σ ρ) t
  | .univ => rfl
  | .pi A B => by
      rw [wk, subst, subst, subst_wk A, subst_wk B, subst_lift_substWk B]
  | .nat => rfl
  | .var _ => rfl
  | .lam t => by
      rw [wk, subst, subst, subst_wk t, subst_lift_substWk t]
  | .app t u => by
      rw [wk, subst, subst, subst_wk t, subst_wk u]
  | .zero => rfl
  | .succ t => congrArg Term.succ (subst_wk t)
  | .natrec A z s n => by
      rw [wk, subst, subst, subst_wk A, subst_lift_substWk A,
        subst_wk z, subst_wk s, subst_wk n]

theorem wk_subst_lift {ρ : Wk} {σ : Subst} (G : Term) :
    wk (.lift ρ) (subst (liftSubst σ) G) = subst (liftSubst (wkSubst ρ σ)) G :=
  (wk_subst G).trans (subst_lift_wkSubst G)

theorem wk_eq_subst (ρ : Wk) (t : Term) : wk ρ t = subst (toSubst ρ) t := by
  have h : wk ρ (subst idSubst t) = subst (wkSubst ρ idSubst) t := wk_subst t
  rw [subst_id] at h
  exact h

theorem substCompLift {σ σ' : Subst} :
    ∀ x, compSubst (liftSubst σ) (liftSubst σ') x = liftSubst (compSubst σ σ') x
  | 0 => rfl
  | x + 1 => (subst_wk (σ' x)).trans (wk_subst (σ' x)).symm

theorem substCompEq {σ σ' : Subst} :
    ∀ t, subst σ (subst σ' t) = subst (compSubst σ σ') t
  | .univ => rfl
  | .pi A B => by
      rw [subst, subst, substCompEq A, substCompEq B, substVar_to_subst substCompLift B]
      rfl
  | .nat => rfl
  | .var _ => rfl
  | .lam t => by
      rw [subst, subst, substCompEq t, substVar_to_subst substCompLift t]
      rfl
  | .app t u => by
      rw [subst, subst, substCompEq t, substCompEq u]
      rfl
  | .zero => rfl
  | .succ t => congrArg Term.succ (substCompEq t)
  | .natrec A z s n => by
      rw [subst, subst, substCompEq A, substVar_to_subst substCompLift A,
        substCompEq z, substCompEq s, substCompEq n]
      rfl

theorem wk_comp_subst {a : Term} (ρ ρ' : Wk) (G : Term) :
    subst0 (wk (.lift (compWk ρ ρ')) G) a =
      subst0 (wk (.lift ρ) (wk (.lift ρ') G)) a :=
  congrArg (fun x ↦ subst0 x a) (wk_comp (.lift ρ) (.lift ρ') G).symm

theorem wk_beta {ρ : Wk} {a : Term} (t : Term) :
    wk ρ (subst0 t a) = subst0 (wk (.lift ρ) t) (wk ρ a) := by
  unfold subst0
  rw [wk_subst t, subst_wk t]
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem wk_betaKeep {ρ : Wk} {a : Term} (t : Term) :
    wk (.lift ρ) (substKeep t a) = substKeep (wk (.lift ρ) t) (wk (.lift ρ) a) := by
  unfold substKeep
  rw [wk_subst t, subst_wk t]
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem wk_arr (ρ : Wk) (A B : Term) :
    wk ρ (arr A B) = arr (wk ρ A) (wk ρ B) := by
  unfold arr
  rw [wk, wk1_wk_eq_lift_wk1]

theorem wk_beta_natrec (ρ : Wk) (G : Term) :
    wk ρ (recStepType G) = recStepType (wk (.lift ρ) G) := by
  unfold recStepType arr
  rw [wk, wk, ← wk1_wk_eq_lift_wk1 (.lift ρ), wk_betaKeep G]
  rfl

theorem substVarSingletonComp {u : Term} {σ : Subst} :
    ∀ x, compSubst (sgSubst u) (liftSubst σ) x = consSubst σ u x
  | 0 => rfl
  | x + 1 => (subst_wk (σ x)).trans (subst_id (σ x))

theorem substSingletonComp {a : Term} {σ : Subst} (t : Term) :
    subst (compSubst (sgSubst a) (liftSubst σ)) t = subst (consSubst σ a) t :=
  substVar_to_subst substVarSingletonComp t

theorem singleSubstComp (t : Term) (σ : Subst) (G : Term) :
    subst0 (subst (liftSubst σ) G) t = subst (consSubst σ t) G :=
  (substCompEq G).trans (substSingletonComp G)

theorem singleSubstWkComp {ρ : Wk} (t : Term) (σ : Subst) (G : Term) :
    subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) t =
      subst (consSubst (wkSubst ρ σ) t) G := by
  rw [wk_subst_lift, singleSubstComp]

theorem singleSubstLift {σ : Subst} (G t : Term) :
    subst σ (subst0 G t) = subst0 (subst (liftSubst σ) G) (subst σ t) := by
  unfold subst0
  rw [substCompEq G, substCompEq G]
  apply substVar_to_subst
  intro x
  cases x with
  | zero => rfl
  | succ x => exact (substVarSingletonComp (x + 1)).symm

theorem idWkLiftSubstLemma (σ : Subst) (G : Term) :
    subst0 (wk (.lift (.step .id)) (subst (liftSubst σ) G)) (.var 0) =
      subst (liftSubst σ) G := by
  rw [singleSubstWkComp (.var 0) σ G]
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem substVarCompKeep {t : Term} (σ : Subst) :
    ∀ x, compSubst (consSubst (wk1Subst idSubst) (subst (liftSubst σ) t)) (liftSubst σ) x =
      compSubst (liftSubst σ) (consSubst (wk1Subst idSubst) t) x
  | 0 => rfl
  | x + 1 => (subst_wk (σ x)).trans (wk_eq_subst (.step .id) (σ x)).symm

theorem singleSubstLiftKeep (σ : Subst) (G t : Term) :
    subst (liftSubst σ) (substKeep G t) =
      substKeep (subst (liftSubst σ) G) (subst (liftSubst σ) t) := by
  unfold substKeep
  rw [substCompEq G, substCompEq G]
  exact (substVar_to_subst (substVarCompKeep σ) G).symm

theorem substConsComp {σ : Subst} {t G : Term} :
    subst (consSubst (fun x ↦ σ (x + 1)) (subst (tailSubst σ) t)) G =
      subst σ (subst (consSubst (fun x ↦ .var (x + 1)) (wk1 t)) G) := by
  rw [substCompEq G]
  apply substVar_to_subst
  intro x
  cases x with
  | zero => exact (subst_wk (σ := σ) (ρ := .step .id) t).symm
  | succ _ => rfl

@[simp]
theorem subst_consSubst_wk1 (σ : Subst) (a m : Term) :
    subst (consSubst σ a) (wk1 m) = subst σ m :=
  subst_wk (σ := consSubst σ a) (ρ := .step .id) m

@[simp]
theorem subst_sgSubst_wk1 (a m : Term) : subst (sgSubst a) (wk1 m) = m := by
  unfold sgSubst
  rw [subst_consSubst_wk1, subst_id]

theorem wkSingleSubstId (F : Term) :
    subst0 (wk (.lift (.step .id)) F) (.var 0) = F := by
  unfold subst0
  rw [subst_wk F]
  refine Eq.trans ?_ (subst_id F)
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem cons_wk_subst (ρ : Wk) (σ : Subst) (a t : Term) :
    subst (compSubst (substWk (sgSubst a) (.lift ρ)) (liftSubst σ)) t =
      subst (consSubst (wkSubst ρ σ) a) t := by
  apply substVar_to_subst
  intro x
  cases x with
  | zero => rfl
  | succ x => exact (subst_wk (σ x)).trans (wk_eq_subst ρ (σ x)).symm

theorem natrecSucCaseLemma {σ : Subst} :
    ∀ x, compSubst (wkSubst (.step .id) (consSubst (wk1Subst idSubst) (.succ (.var 0))))
      (liftSubst σ) x =
      compSubst (substWk (liftSubst (liftSubst σ)) (.step .id))
        (consSubst (wk1Subst idSubst) (.succ (.var 0))) x
  | 0 => rfl
  | x + 1 => by
      change subst (wkSubst (.step .id) (consSubst (wk1Subst idSubst) (.succ (.var 0))))
        (wk (.step .id) (σ x)) = wk (.step .id) (wk (.step .id) (σ x))
      rw [← wk_subst (ρ := .step .id), subst_wk (ρ := .step .id) (σ x)]
      exact congrArg (wk (.step .id)) (wk_eq_subst (.step .id) (σ x)).symm

theorem natrecSucCase (σ : Subst) (F : Term) :
    subst σ (recStepType F) = recStepType (subst (liftSubst σ) F) := by
  unfold recStepType arr substKeep
  dsimp [subst, liftSubst]
  congr 1
  congr 1
  unfold wk1
  rw [subst_wk (ρ := .step .id), substCompEq F, wk_subst (ρ := .step .id), substCompEq F]
  exact (substVar_to_subst natrecSucCaseLemma F).symm

theorem natrecIrrelevantSubstLemma (F z s m : Term) (σ : Subst) :
    ∀ x,
      compSubst
        (substWk
          (compSubst
            (compSubst (sgSubst (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m))
              (liftSubst (sgSubst m)))
            (liftSubst (liftSubst σ)))
          (.step .id))
        (consSubst (tailSubst idSubst) (.succ (.var 0))) x =
      consSubst σ (.succ m) x
  | 0 => by
      change Term.succ (subst (sgSubst (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m)) (wk1 m)) =
        Term.succ m
      rw [subst_sgSubst_wk1]
  | x + 1 => by
      dsimp [compSubst, substWk, consSubst, tailSubst, idSubst, liftSubst, wkVar, subst]
      rw [substSingletonComp, subst_consSubst_wk1, subst_sgSubst_wk1]

theorem natrecIrrelevantSubst (F z s m : Term) (σ : Subst) :
    subst (consSubst σ (.succ m)) F =
      subst0
        (subst (liftSubst (sgSubst m))
          (subst (liftSubst (liftSubst σ))
            (wk1 (substKeep F (.succ (.var 0))))))
        (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m) := by
  unfold subst0 substKeep wk1
  rw [substCompEq, substCompEq, subst_wk (ρ := .step .id), substCompEq]
  exact (substVar_to_subst (natrecIrrelevantSubstLemma F z s m σ) F).symm

theorem natrecIrrelevantSubstLemma' (F z s n : Term) :
    ∀ x,
      compSubst
        (substWk
          (compSubst (sgSubst (.natrec F z s n)) (liftSubst (sgSubst n)))
          (.step .id))
        (consSubst (tailSubst idSubst) (.succ (.var 0))) x =
      consSubst idSubst (.succ n) x
  | 0 => by
      change Term.succ (subst (sgSubst (.natrec F z s n)) (wk1 n)) = Term.succ n
      rw [subst_sgSubst_wk1]
  | _ + 1 => rfl

theorem natrecIrrelevantSubst' (F z s n : Term) :
    subst0
      (subst (liftSubst (sgSubst n))
        (wk1 (substKeep F (.succ (.var 0)))))
      (.natrec F z s n) =
      subst0 F (.succ n) := by
  unfold subst0 substKeep wk1
  rw [substCompEq, subst_wk (ρ := .step .id), substCompEq]
  exact substVar_to_subst (natrecIrrelevantSubstLemma' F z s n) F

theorem cons0wkLift1_id (σ : Subst) (G : Term) :
    subst (sgSubst (.var 0)) (wk (.lift (.step .id)) (subst (liftSubst σ) G)) =
      subst (liftSubst σ) G := by
  rw [subst_wk (subst (liftSubst σ) G)]
  refine Eq.trans ?_ (subst_id (subst (liftSubst σ) G))
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem substConsId {σ : Subst} {t : Term} (G : Term) :
    subst (consSubst σ (subst σ t)) G = subst σ (subst (sgSubst t) G) := by
  rw [substCompEq G]
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem substConsTailId {G t : Term} {σ : Subst} :
    subst (consSubst (tailSubst σ) (subst σ t)) G =
      subst σ (subst (consSubst (tailSubst idSubst) t) G) := by
  rw [substCompEq G]
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem substConcatSingleton' {a : Term} {σ : Subst} (t : Term) :
    subst (compSubst σ (sgSubst a)) t = subst (consSubst σ (subst σ a)) t := by
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem wk1_tailId (t : Term) : wk1 t = subst (tailSubst idSubst) t := by
  unfold wk1
  exact (subst_id (wk (.step .id) t)).symm.trans (subst_wk (ρ := .step .id) t)

end Abel2018

/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/Typed.agda. Judgments express inhabitation of the source derivation types.
Contexts are newest-first lists rather than snoc lists. This definition layer makes no
claim to reproduce the source's metatheoretic absence of K in Lean's own metatheory.
-/

namespace Abel2018





























end Abel2018

/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/Typed/Weakening.agda (Lemma 2.7 of POPL 2018).
-/

namespace Abel2018



/-- Composition of typed weakenings (`_•ₜ_`). -/
theorem WkCtx.comp {ρ ρ' : Wk} {Γ Δ Δ' : Context}
    (h₁ : WkCtx ρ Γ Δ) (h₂ : WkCtx ρ' Δ Δ') : WkCtx (compWk ρ ρ') Γ Δ' := by
  induction h₁ generalizing ρ' Δ' with
  | id => exact h₂
  | step h₁ ih => exact .step (ih h₂)
  | @lift Δ₀ Γ₀ B ρ₀ h₁ ih =>
      cases h₂ with
      | id => exact .lift h₁
      | step h₂ => exact .step (ih h₂)
      | @lift Δ'₀ _ A ρ'₀ h₂ =>
          have hcomp : WkCtx (.lift (compWk ρ₀ ρ'₀)) (wk (compWk ρ₀ ρ'₀) A :: Γ₀) (A :: Δ'₀) :=
            .lift (ih h₂)
          rw [← wk_comp ρ₀ ρ'₀ A] at hcomp
          exact hcomp

/-- Weakening of context membership (`wkIndex`). -/
theorem wkIndex {Γ Δ : Context} {n : Nat} {A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (_hΔ : CtxWf Δ) (hm : Member n A Γ) :
    Member (wkVar ρ n) (wk ρ A) Δ := by
  induction hρ generalizing n A with
  | id =>
      rw [wk_id]
      exact hm
  | @step Γ₀ Δ₀ B ρ₀ hρ ih =>
      cases _hΔ with
      | cons hΔ₀ _ =>
          have h := Member.there (B := B) (ih hΔ₀ hm)
          rw [wk1_wk] at h
          exact h
  | @lift Γ₀ Δ₀ B ρ₀ hρ ih =>
      cases _hΔ with
      | cons hΔ₀ _ =>
          cases hm with
          | here =>
              have h : Member 0 (wk1 (wk ρ₀ B)) (wk ρ₀ B :: Δ₀) := .here
              rw [wk1_wk_eq_lift_wk1] at h
              exact h
          | there hm₀ =>
              have h := Member.there (B := wk ρ₀ B) (ih hΔ₀ hm₀)
              rw [wk1_wk_eq_lift_wk1] at h
              exact h

private abbrev WkTypeWfMotive (Γ : Context) (A : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → TypeWf Δ (wk ρ A)

private abbrev WkHasTypeMotive (Γ : Context) (t A : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → HasType Δ (wk ρ t) (wk ρ A)

private abbrev WkTypeEqMotive (Γ : Context) (A B : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → TypeEq Δ (wk ρ A) (wk ρ B)

private abbrev WkTermEqMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → TermEq Δ (wk ρ t) (wk ρ u) (wk ρ A)

private theorem wk_nat_case {Γ : Context} (_hΓ : CtxWf Γ) : WkTypeWfMotive Γ .nat :=
  fun _ hΔ ↦ .nat hΔ

private theorem wk_univ_case {Γ : Context} (_hΓ : CtxWf Γ) : WkTypeWfMotive Γ .univ :=
  fun _ hΔ ↦ .univ hΔ

private theorem wk_pi_type_case {Γ : Context} {F G : Term}
    (_hF : TypeWf Γ F) (_hG : TypeWf (F :: Γ) G)
    (ihF : WkTypeWfMotive Γ F) (ihG : WkTypeWfMotive (F :: Γ) G) :
    WkTypeWfMotive Γ (.pi F G) :=
  fun hρ hΔ ↦
    let hρF := ihF hρ hΔ
    .pi hρF (ihG (.lift hρ) (.cons hΔ hρF))

private theorem wk_fromUniv_type_case {Γ : Context} {A : Term}
    (_hA : HasType Γ A .univ) (ihA : WkHasTypeMotive Γ A .univ) :
    WkTypeWfMotive Γ A :=
  fun hρ hΔ ↦ .fromUniv (ihA hρ hΔ)

private theorem wk_nat_term_case {Γ : Context} (_hΓ : CtxWf Γ) :
    WkHasTypeMotive Γ .nat .univ :=
  fun _ hΔ ↦ .nat hΔ

private theorem wk_pi_term_case {Γ : Context} {F G : Term}
    (_hF : HasType Γ F .univ) (_hG : HasType (F :: Γ) G .univ)
    (ihF : WkHasTypeMotive Γ F .univ) (ihG : WkHasTypeMotive (F :: Γ) G .univ) :
    WkHasTypeMotive Γ (.pi F G) .univ :=
  fun hρ hΔ ↦
    let hρF := ihF hρ hΔ
    .pi hρF (ihG (.lift hρ) (.cons hΔ (.fromUniv hρF)))

private theorem wk_var_case {Γ : Context} {A : Term} {x : Nat}
    (_hΓ : CtxWf Γ) (hm : Member x A Γ) :
    WkHasTypeMotive Γ (.var x) A :=
  fun hρ hΔ ↦ .var hΔ (wkIndex hρ hΔ hm)

private theorem wk_lam_case {Γ : Context} {F G t : Term}
    (_hF : TypeWf Γ F) (_ht : HasType (F :: Γ) t G)
    (ihF : WkTypeWfMotive Γ F) (iht : WkHasTypeMotive (F :: Γ) t G) :
    WkHasTypeMotive Γ (.lam t) (.pi F G) :=
  fun hρ hΔ ↦
    let hρF := ihF hρ hΔ
    .lam hρF (iht (.lift hρ) (.cons hΔ hρF))

private theorem wk_app_case {Γ : Context} {g a F G : Term}
    (_hg : HasType Γ g (.pi F G)) (_ha : HasType Γ a F)
    (ihg : WkHasTypeMotive Γ g (.pi F G)) (iha : WkHasTypeMotive Γ a F) :
    WkHasTypeMotive Γ (.app g a) (subst0 G a) := by
  intro Δ ρ hρ hΔ
  rw [wk, wk_beta (ρ := ρ) (a := a) G]
  exact HasType.app (ihg hρ hΔ) (iha hρ hΔ)

private theorem wk_zero_case {Γ : Context} (_hΓ : CtxWf Γ) :
    WkHasTypeMotive Γ .zero .nat :=
  fun _ hΔ ↦ .zero hΔ

private theorem wk_succ_case {Γ : Context} {n : Term}
    (_hn : HasType Γ n .nat) (ihn : WkHasTypeMotive Γ n .nat) :
    WkHasTypeMotive Γ (.succ n) .nat :=
  fun hρ hΔ ↦ .succ (ihn hρ hΔ)

private theorem wk_natrec_case {Γ : Context} {G s z n : Term}
    (_hG : TypeWf (.nat :: Γ) G) (_hz : HasType Γ z (subst0 G .zero))
    (_hs : HasType Γ s (recStepType G)) (_hn : HasType Γ n .nat)
    (ihG : WkTypeWfMotive (.nat :: Γ) G)
    (ihz : WkHasTypeMotive Γ z (subst0 G .zero))
    (ihs : WkHasTypeMotive Γ s (recStepType G))
    (ihn : WkHasTypeMotive Γ n .nat) :
    WkHasTypeMotive Γ (.natrec G z s n) (subst0 G n) := by
  intro Δ ρ hρ hΔ
  have hρG : TypeWf (.nat :: Δ) (wk (.lift ρ) G) :=
    ihG (WkCtx.lift (A := .nat) hρ) (.cons hΔ (.nat hΔ))
  have hρz : HasType Δ (wk ρ z) (subst0 (wk (.lift ρ) G) .zero) := by
    have hz' := ihz hρ hΔ
    rw [wk_beta (ρ := ρ) (a := .zero) G] at hz'
    exact hz'
  have hρs : HasType Δ (wk ρ s) (recStepType (wk (.lift ρ) G)) := by
    have hs' := ihs hρ hΔ
    rw [wk_beta_natrec ρ G] at hs'
    exact hs'
  have hρn : HasType Δ (wk ρ n) .nat := ihn hρ hΔ
  rw [wk, wk_beta (ρ := ρ) (a := n) G]
  exact HasType.natrec hρG hρz hρs hρn

private theorem wk_conv_case {Γ : Context} {t A B : Term}
    (_ht : HasType Γ t A) (_hEq : TypeEq Γ A B)
    (iht : WkHasTypeMotive Γ t A) (ihEq : WkTypeEqMotive Γ A B) :
    WkHasTypeMotive Γ t B :=
  fun hρ hΔ ↦ .conv (iht hρ hΔ) (ihEq hρ hΔ)

private theorem wk_fromUniv_eq_case {Γ : Context} {A B : Term}
    (_hEq : TermEq Γ A B .univ) (ihEq : WkTermEqMotive Γ A B .univ) :
    WkTypeEqMotive Γ A B :=
  fun hρ hΔ ↦ .fromUniv (ihEq hρ hΔ)

private theorem wk_refl_type_case {Γ : Context} {A : Term}
    (_hA : TypeWf Γ A) (ihA : WkTypeWfMotive Γ A) :
    WkTypeEqMotive Γ A A :=
  fun hρ hΔ ↦ .refl (ihA hρ hΔ)

private theorem wk_symm_type_case {Γ : Context} {A B : Term}
    (_hEq : TypeEq Γ A B) (ihEq : WkTypeEqMotive Γ A B) :
    WkTypeEqMotive Γ B A :=
  fun hρ hΔ ↦ .symm (ihEq hρ hΔ)

private theorem wk_trans_type_case {Γ : Context} {A B C : Term}
    (_h₁ : TypeEq Γ A B) (_h₂ : TypeEq Γ B C)
    (ih₁ : WkTypeEqMotive Γ A B) (ih₂ : WkTypeEqMotive Γ B C) :
    WkTypeEqMotive Γ A C :=
  fun hρ hΔ ↦ .trans (ih₁ hρ hΔ) (ih₂ hρ hΔ)

private theorem wk_pi_type_eq_case {Γ : Context} {F H G E : Term}
    (_hF : TypeWf Γ F) (_hFH : TypeEq Γ F H) (_hGE : TypeEq (F :: Γ) G E)
    (ihF : WkTypeWfMotive Γ F)
    (ihFH : WkTypeEqMotive Γ F H)
    (ihGE : WkTypeEqMotive (F :: Γ) G E) :
    WkTypeEqMotive Γ (.pi F G) (.pi H E) :=
  fun hρ hΔ ↦
    let hρF := ihF hρ hΔ
    .pi hρF (ihFH hρ hΔ) (ihGE (.lift hρ) (.cons hΔ hρF))

private theorem wk_refl_term_case {Γ : Context} {t A : Term}
    (_ht : HasType Γ t A) (iht : WkHasTypeMotive Γ t A) :
    WkTermEqMotive Γ t t A :=
  fun hρ hΔ ↦ .refl (iht hρ hΔ)

private theorem wk_symm_term_case {Γ : Context} {t u A : Term}
    (_hEq : TermEq Γ t u A) (ihEq : WkTermEqMotive Γ t u A) :
    WkTermEqMotive Γ u t A :=
  fun hρ hΔ ↦ .symm (ihEq hρ hΔ)

private theorem wk_trans_term_case {Γ : Context} {t u r A : Term}
    (_h₁ : TermEq Γ t u A) (_h₂ : TermEq Γ u r A)
    (ih₁ : WkTermEqMotive Γ t u A) (ih₂ : WkTermEqMotive Γ u r A) :
    WkTermEqMotive Γ t r A :=
  fun hρ hΔ ↦ .trans (ih₁ hρ hΔ) (ih₂ hρ hΔ)

private theorem wk_conv_term_case {Γ : Context} {A B t u : Term}
    (_hEq : TermEq Γ t u A) (_hAB : TypeEq Γ A B)
    (ihEq : WkTermEqMotive Γ t u A) (ihAB : WkTypeEqMotive Γ A B) :
    WkTermEqMotive Γ t u B :=
  fun hρ hΔ ↦ .conv (ihEq hρ hΔ) (ihAB hρ hΔ)

private theorem wk_pi_term_eq_case {Γ : Context} {E F G H : Term}
    (_hF : TypeWf Γ F) (_hFH : TermEq Γ F H .univ) (_hGE : TermEq (F :: Γ) G E .univ)
    (ihF : WkTypeWfMotive Γ F)
    (ihFH : WkTermEqMotive Γ F H .univ)
    (ihGE : WkTermEqMotive (F :: Γ) G E .univ) :
    WkTermEqMotive Γ (.pi F G) (.pi H E) .univ :=
  fun hρ hΔ ↦
    let hρF := ihF hρ hΔ
    .pi hρF (ihFH hρ hΔ) (ihGE (.lift hρ) (.cons hΔ hρF))

private theorem wk_app_term_eq_case {Γ : Context} {a b f g F G : Term}
    (_hfg : TermEq Γ f g (.pi F G)) (_hab : TermEq Γ a b F)
    (ihfg : WkTermEqMotive Γ f g (.pi F G))
    (ihab : WkTermEqMotive Γ a b F) :
    WkTermEqMotive Γ (.app f a) (.app g b) (subst0 G a) := by
  intro Δ ρ hρ hΔ
  rw [wk, wk, wk_beta (ρ := ρ) (a := a) G]
  exact TermEq.app (ihfg hρ hΔ) (ihab hρ hΔ)

private theorem wk_beta_term_eq_case {Γ : Context} {a t F G : Term}
    (_hF : TypeWf Γ F) (_ht : HasType (F :: Γ) t G) (_ha : HasType Γ a F)
    (ihF : WkTypeWfMotive Γ F)
    (iht : WkHasTypeMotive (F :: Γ) t G)
    (iha : WkHasTypeMotive Γ a F) :
    WkTermEqMotive Γ (.app (.lam t) a) (subst0 t a) (subst0 G a) := by
  intro Δ ρ hρ hΔ
  let hρF := ihF hρ hΔ
  rw [wk, wk, wk_beta (ρ := ρ) (a := a) t, wk_beta (ρ := ρ) (a := a) G]
  exact TermEq.beta hρF (iht (.lift hρ) (.cons hΔ hρF)) (iha hρ hΔ)

private theorem wk_eta_term_eq_case {Γ : Context} {f g F G : Term}
    (_hF : TypeWf Γ F) (_hf : HasType Γ f (.pi F G)) (_hg : HasType Γ g (.pi F G))
    (_hfg : TermEq (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G)
    (ihF : WkTypeWfMotive Γ F)
    (ihf : WkHasTypeMotive Γ f (.pi F G))
    (ihg : WkHasTypeMotive Γ g (.pi F G))
    (ihfg : WkTermEqMotive (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G) :
    WkTermEqMotive Γ f g (.pi F G) := by
  intro Δ ρ hρ hΔ
  let hρF := ihF hρ hΔ
  have hfg' : TermEq (wk ρ F :: Δ)
      (.app (wk (.lift ρ) (wk1 f)) (.var 0))
      (.app (wk (.lift ρ) (wk1 g)) (.var 0))
      (wk (.lift ρ) G) :=
    ihfg (.lift hρ) (.cons hΔ hρF)
  rw [← wk1_wk_eq_lift_wk1 ρ f, ← wk1_wk_eq_lift_wk1 ρ g] at hfg'
  exact TermEq.eta hρF (ihf hρ hΔ) (ihg hρ hΔ) hfg'

private theorem wk_succ_term_eq_case {Γ : Context} {m n : Term}
    (_hmn : TermEq Γ m n .nat) (ihmn : WkTermEqMotive Γ m n .nat) :
    WkTermEqMotive Γ (.succ m) (.succ n) .nat :=
  fun hρ hΔ ↦ .succ (ihmn hρ hΔ)

private theorem wk_natrec_term_eq_case {Γ : Context} {z z' s s' n n' F F' : Term}
    (_hFF' : TypeEq (.nat :: Γ) F F')
    (_hzz' : TermEq Γ z z' (subst0 F .zero))
    (_hss' : TermEq Γ s s' (recStepType F))
    (_hnn' : TermEq Γ n n' .nat)
    (ihFF' : WkTypeEqMotive (.nat :: Γ) F F')
    (ihzz' : WkTermEqMotive Γ z z' (subst0 F .zero))
    (ihss' : WkTermEqMotive Γ s s' (recStepType F))
    (ihnn' : WkTermEqMotive Γ n n' .nat) :
    WkTermEqMotive Γ (.natrec F z s n) (.natrec F' z' s' n') (subst0 F n) := by
  intro Δ ρ hρ hΔ
  have hρFF' : TypeEq (.nat :: Δ) (wk (.lift ρ) F) (wk (.lift ρ) F') :=
    ihFF' (WkCtx.lift (A := .nat) hρ) (.cons hΔ (.nat hΔ))
  have hρzz' : TermEq Δ (wk ρ z) (wk ρ z') (subst0 (wk (.lift ρ) F) .zero) := by
    have h := ihzz' hρ hΔ
    rw [wk_beta (ρ := ρ) (a := .zero) F] at h
    exact h
  have hρss' : TermEq Δ (wk ρ s) (wk ρ s') (recStepType (wk (.lift ρ) F)) := by
    have h := ihss' hρ hΔ
    rw [wk_beta_natrec ρ F] at h
    exact h
  have hρnn' : TermEq Δ (wk ρ n) (wk ρ n') .nat := ihnn' hρ hΔ
  rw [wk, wk, wk_beta (ρ := ρ) (a := n) F]
  exact TermEq.natrec hρFF' hρzz' hρss' hρnn'

private theorem wk_natrecZero_term_eq_case {Γ : Context} {z s F : Term}
    (_hF : TypeWf (.nat :: Γ) F)
    (_hz : HasType Γ z (subst0 F .zero))
    (_hs : HasType Γ s (recStepType F))
    (ihF : WkTypeWfMotive (.nat :: Γ) F)
    (ihz : WkHasTypeMotive Γ z (subst0 F .zero))
    (ihs : WkHasTypeMotive Γ s (recStepType F)) :
    WkTermEqMotive Γ (.natrec F z s .zero) z (subst0 F .zero) := by
  intro Δ ρ hρ hΔ
  have hρF : TypeWf (.nat :: Δ) (wk (.lift ρ) F) :=
    ihF (WkCtx.lift (A := .nat) hρ) (.cons hΔ (.nat hΔ))
  have hρz : HasType Δ (wk ρ z) (subst0 (wk (.lift ρ) F) .zero) := by
    have h := ihz hρ hΔ
    rw [wk_beta (ρ := ρ) (a := .zero) F] at h
    exact h
  have hρs : HasType Δ (wk ρ s) (recStepType (wk (.lift ρ) F)) := by
    have h := ihs hρ hΔ
    rw [wk_beta_natrec ρ F] at h
    exact h
  rw [wk, wk_beta (ρ := ρ) (a := .zero) F]
  exact TermEq.natrecZero hρF hρz hρs

private theorem wk_natrecSucc_term_eq_case {Γ : Context} {n z s F : Term}
    (_hn : HasType Γ n .nat)
    (_hF : TypeWf (.nat :: Γ) F)
    (_hz : HasType Γ z (subst0 F .zero))
    (_hs : HasType Γ s (recStepType F))
    (ihn : WkHasTypeMotive Γ n .nat)
    (ihF : WkTypeWfMotive (.nat :: Γ) F)
    (ihz : WkHasTypeMotive Γ z (subst0 F .zero))
    (ihs : WkHasTypeMotive Γ s (recStepType F)) :
    WkTermEqMotive Γ (.natrec F z s (.succ n)) (.app (.app s n) (.natrec F z s n))
      (subst0 F (.succ n)) := by
  intro Δ ρ hρ hΔ
  have hρn : HasType Δ (wk ρ n) .nat := ihn hρ hΔ
  have hρF : TypeWf (.nat :: Δ) (wk (.lift ρ) F) :=
    ihF (WkCtx.lift (A := .nat) hρ) (.cons hΔ (.nat hΔ))
  have hρz : HasType Δ (wk ρ z) (subst0 (wk (.lift ρ) F) .zero) := by
    have h := ihz hρ hΔ
    rw [wk_beta (ρ := ρ) (a := .zero) F] at h
    exact h
  have hρs : HasType Δ (wk ρ s) (recStepType (wk (.lift ρ) F)) := by
    have h := ihs hρ hΔ
    rw [wk_beta_natrec ρ F] at h
    exact h
  rw [wk, wk_beta (ρ := ρ) (a := .succ n) F]
  exact TermEq.natrecSucc hρn hρF hρz hρs

/-- Weakening of well-formed types (`wk`, Lemma 2.7). -/
theorem wkTypeWf {Γ Δ : Context} {A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (d : TypeWf Γ A) : TypeWf Δ (wk ρ A) :=
  (TypeWf.rec (motive_1 := fun _ _ ↦ True)
    (motive_2 := fun Γ A _ ↦ WkTypeWfMotive Γ A)
    (motive_3 := fun Γ t A _ ↦ WkHasTypeMotive Γ t A)
    (motive_4 := fun Γ A B _ ↦ WkTypeEqMotive Γ A B)
    (motive_5 := fun Γ t u A _ ↦ WkTermEqMotive Γ t u A)
    trivial
    (fun _ _ _ _ ↦ trivial)
    (fun hΓ _ ↦ wk_nat_case hΓ)
    (fun hΓ _ ↦ wk_univ_case hΓ)
    (fun hF hG ihF ihG ↦ wk_pi_type_case hF hG ihF ihG)
    (fun hA ihA ↦ wk_fromUniv_type_case hA ihA)
    (fun hΓ _ ↦ wk_nat_term_case hΓ)
    (fun hF hG ihF ihG ↦ wk_pi_term_case hF hG ihF ihG)
    (fun hΓ hm _ ↦ wk_var_case hΓ hm)
    (fun hF ht ihF iht ↦ wk_lam_case hF ht ihF iht)
    (fun hg ha ihg iha ↦ wk_app_case hg ha ihg iha)
    (fun hΓ _ ↦ wk_zero_case hΓ)
    (fun hn ihn ↦ wk_succ_case hn ihn)
    (fun hG hz hs hn ihG ihz ihs ihn ↦ wk_natrec_case hG hz hs hn ihG ihz ihs ihn)
    (fun ht hEq iht ihEq ↦ wk_conv_case ht hEq iht ihEq)
    (fun hEq ihEq ↦ wk_fromUniv_eq_case hEq ihEq)
    (fun hA ihA ↦ wk_refl_type_case hA ihA)
    (fun hEq ihEq ↦ wk_symm_type_case hEq ihEq)
    (fun h₁ h₂ ih₁ ih₂ ↦ wk_trans_type_case h₁ h₂ ih₁ ih₂)
    (fun hF hFH hGE ihF ihFH ihGE ↦ wk_pi_type_eq_case hF hFH hGE ihF ihFH ihGE)
    (fun ht iht ↦ wk_refl_term_case ht iht)
    (fun hEq ihEq ↦ wk_symm_term_case hEq ihEq)
    (fun h₁ h₂ ih₁ ih₂ ↦ wk_trans_term_case h₁ h₂ ih₁ ih₂)
    (fun hEq hAB ihEq ihAB ↦ wk_conv_term_case hEq hAB ihEq ihAB)
    (fun hF hFH hGE ihF ihFH ihGE ↦ wk_pi_term_eq_case hF hFH hGE ihF ihFH ihGE)
    (fun hfg hab ihfg ihab ↦ wk_app_term_eq_case hfg hab ihfg ihab)
    (fun hF ht ha ihF iht iha ↦ wk_beta_term_eq_case hF ht ha ihF iht iha)
    (fun hF hf hg hfg ihF ihf ihg ihfg ↦ wk_eta_term_eq_case hF hf hg hfg ihF ihf ihg ihfg)
    (fun hmn ihmn ↦ wk_succ_term_eq_case hmn ihmn)
    (fun hFF' hzz' hss' hnn' ihFF' ihzz' ihss' ihnn' ↦
      wk_natrec_term_eq_case hFF' hzz' hss' hnn' ihFF' ihzz' ihss' ihnn')
    (fun hF hz hs ihF ihz ihs ↦ wk_natrecZero_term_eq_case hF hz hs ihF ihz ihs)
    (fun hn hF hz hs ihn ihF ihz ihs ↦ wk_natrecSucc_term_eq_case hn hF hz hs ihn ihF ihz ihs)
    d) hρ hΔ

/-- Weakening of well-typed terms (`wkTerm`, Lemma 2.7). -/
theorem wkHasType {Γ Δ : Context} {t A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (d : HasType Γ t A) :
    HasType Δ (wk ρ t) (wk ρ A) :=
  (HasType.rec (motive_1 := fun _ _ ↦ True)
    (motive_2 := fun Γ A _ ↦ WkTypeWfMotive Γ A)
    (motive_3 := fun Γ t A _ ↦ WkHasTypeMotive Γ t A)
    (motive_4 := fun Γ A B _ ↦ WkTypeEqMotive Γ A B)
    (motive_5 := fun Γ t u A _ ↦ WkTermEqMotive Γ t u A)
    trivial
    (fun _ _ _ _ ↦ trivial)
    (fun hΓ _ ↦ wk_nat_case hΓ)
    (fun hΓ _ ↦ wk_univ_case hΓ)
    (fun hF hG ihF ihG ↦ wk_pi_type_case hF hG ihF ihG)
    (fun hA ihA ↦ wk_fromUniv_type_case hA ihA)
    (fun hΓ _ ↦ wk_nat_term_case hΓ)
    (fun hF hG ihF ihG ↦ wk_pi_term_case hF hG ihF ihG)
    (fun hΓ hm _ ↦ wk_var_case hΓ hm)
    (fun hF ht ihF iht ↦ wk_lam_case hF ht ihF iht)
    (fun hg ha ihg iha ↦ wk_app_case hg ha ihg iha)
    (fun hΓ _ ↦ wk_zero_case hΓ)
    (fun hn ihn ↦ wk_succ_case hn ihn)
    (fun hG hz hs hn ihG ihz ihs ihn ↦ wk_natrec_case hG hz hs hn ihG ihz ihs ihn)
    (fun ht hEq iht ihEq ↦ wk_conv_case ht hEq iht ihEq)
    (fun hEq ihEq ↦ wk_fromUniv_eq_case hEq ihEq)
    (fun hA ihA ↦ wk_refl_type_case hA ihA)
    (fun hEq ihEq ↦ wk_symm_type_case hEq ihEq)
    (fun h₁ h₂ ih₁ ih₂ ↦ wk_trans_type_case h₁ h₂ ih₁ ih₂)
    (fun hF hFH hGE ihF ihFH ihGE ↦ wk_pi_type_eq_case hF hFH hGE ihF ihFH ihGE)
    (fun ht iht ↦ wk_refl_term_case ht iht)
    (fun hEq ihEq ↦ wk_symm_term_case hEq ihEq)
    (fun h₁ h₂ ih₁ ih₂ ↦ wk_trans_term_case h₁ h₂ ih₁ ih₂)
    (fun hEq hAB ihEq ihAB ↦ wk_conv_term_case hEq hAB ihEq ihAB)
    (fun hF hFH hGE ihF ihFH ihGE ↦ wk_pi_term_eq_case hF hFH hGE ihF ihFH ihGE)
    (fun hfg hab ihfg ihab ↦ wk_app_term_eq_case hfg hab ihfg ihab)
    (fun hF ht ha ihF iht iha ↦ wk_beta_term_eq_case hF ht ha ihF iht iha)
    (fun hF hf hg hfg ihF ihf ihg ihfg ↦ wk_eta_term_eq_case hF hf hg hfg ihF ihf ihg ihfg)
    (fun hmn ihmn ↦ wk_succ_term_eq_case hmn ihmn)
    (fun hFF' hzz' hss' hnn' ihFF' ihzz' ihss' ihnn' ↦
      wk_natrec_term_eq_case hFF' hzz' hss' hnn' ihFF' ihzz' ihss' ihnn')
    (fun hF hz hs ihF ihz ihs ↦ wk_natrecZero_term_eq_case hF hz hs ihF ihz ihs)
    (fun hn hF hz hs ihn ihF ihz ihs ↦ wk_natrecSucc_term_eq_case hn hF hz hs ihn ihF ihz ihs)
    d) hρ hΔ

/-- Weakening of type equality (`wkEq`, Lemma 2.7). -/
theorem wkTypeEq {Γ Δ : Context} {A B : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (d : TypeEq Γ A B) :
    TypeEq Δ (wk ρ A) (wk ρ B) :=
  (TypeEq.rec (motive_1 := fun _ _ ↦ True)
    (motive_2 := fun Γ A _ ↦ WkTypeWfMotive Γ A)
    (motive_3 := fun Γ t A _ ↦ WkHasTypeMotive Γ t A)
    (motive_4 := fun Γ A B _ ↦ WkTypeEqMotive Γ A B)
    (motive_5 := fun Γ t u A _ ↦ WkTermEqMotive Γ t u A)
    trivial
    (fun _ _ _ _ ↦ trivial)
    (fun hΓ _ ↦ wk_nat_case hΓ)
    (fun hΓ _ ↦ wk_univ_case hΓ)
    (fun hF hG ihF ihG ↦ wk_pi_type_case hF hG ihF ihG)
    (fun hA ihA ↦ wk_fromUniv_type_case hA ihA)
    (fun hΓ _ ↦ wk_nat_term_case hΓ)
    (fun hF hG ihF ihG ↦ wk_pi_term_case hF hG ihF ihG)
    (fun hΓ hm _ ↦ wk_var_case hΓ hm)
    (fun hF ht ihF iht ↦ wk_lam_case hF ht ihF iht)
    (fun hg ha ihg iha ↦ wk_app_case hg ha ihg iha)
    (fun hΓ _ ↦ wk_zero_case hΓ)
    (fun hn ihn ↦ wk_succ_case hn ihn)
    (fun hG hz hs hn ihG ihz ihs ihn ↦ wk_natrec_case hG hz hs hn ihG ihz ihs ihn)
    (fun ht hEq iht ihEq ↦ wk_conv_case ht hEq iht ihEq)
    (fun hEq ihEq ↦ wk_fromUniv_eq_case hEq ihEq)
    (fun hA ihA ↦ wk_refl_type_case hA ihA)
    (fun hEq ihEq ↦ wk_symm_type_case hEq ihEq)
    (fun h₁ h₂ ih₁ ih₂ ↦ wk_trans_type_case h₁ h₂ ih₁ ih₂)
    (fun hF hFH hGE ihF ihFH ihGE ↦ wk_pi_type_eq_case hF hFH hGE ihF ihFH ihGE)
    (fun ht iht ↦ wk_refl_term_case ht iht)
    (fun hEq ihEq ↦ wk_symm_term_case hEq ihEq)
    (fun h₁ h₂ ih₁ ih₂ ↦ wk_trans_term_case h₁ h₂ ih₁ ih₂)
    (fun hEq hAB ihEq ihAB ↦ wk_conv_term_case hEq hAB ihEq ihAB)
    (fun hF hFH hGE ihF ihFH ihGE ↦ wk_pi_term_eq_case hF hFH hGE ihF ihFH ihGE)
    (fun hfg hab ihfg ihab ↦ wk_app_term_eq_case hfg hab ihfg ihab)
    (fun hF ht ha ihF iht iha ↦ wk_beta_term_eq_case hF ht ha ihF iht iha)
    (fun hF hf hg hfg ihF ihf ihg ihfg ↦ wk_eta_term_eq_case hF hf hg hfg ihF ihf ihg ihfg)
    (fun hmn ihmn ↦ wk_succ_term_eq_case hmn ihmn)
    (fun hFF' hzz' hss' hnn' ihFF' ihzz' ihss' ihnn' ↦
      wk_natrec_term_eq_case hFF' hzz' hss' hnn' ihFF' ihzz' ihss' ihnn')
    (fun hF hz hs ihF ihz ihs ↦ wk_natrecZero_term_eq_case hF hz hs ihF ihz ihs)
    (fun hn hF hz hs ihn ihF ihz ihs ↦ wk_natrecSucc_term_eq_case hn hF hz hs ihn ihF ihz ihs)
    d) hρ hΔ

/-- Weakening of term equality (`wkEqTerm`, Lemma 2.7). -/
theorem wkTermEq {Γ Δ : Context} {t u A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (d : TermEq Γ t u A) :
    TermEq Δ (wk ρ t) (wk ρ u) (wk ρ A) :=
  (TermEq.rec (motive_1 := fun _ _ ↦ True)
    (motive_2 := fun Γ A _ ↦ WkTypeWfMotive Γ A)
    (motive_3 := fun Γ t A _ ↦ WkHasTypeMotive Γ t A)
    (motive_4 := fun Γ A B _ ↦ WkTypeEqMotive Γ A B)
    (motive_5 := fun Γ t u A _ ↦ WkTermEqMotive Γ t u A)
    trivial
    (fun _ _ _ _ ↦ trivial)
    (fun hΓ _ ↦ wk_nat_case hΓ)
    (fun hΓ _ ↦ wk_univ_case hΓ)
    (fun hF hG ihF ihG ↦ wk_pi_type_case hF hG ihF ihG)
    (fun hA ihA ↦ wk_fromUniv_type_case hA ihA)
    (fun hΓ _ ↦ wk_nat_term_case hΓ)
    (fun hF hG ihF ihG ↦ wk_pi_term_case hF hG ihF ihG)
    (fun hΓ hm _ ↦ wk_var_case hΓ hm)
    (fun hF ht ihF iht ↦ wk_lam_case hF ht ihF iht)
    (fun hg ha ihg iha ↦ wk_app_case hg ha ihg iha)
    (fun hΓ _ ↦ wk_zero_case hΓ)
    (fun hn ihn ↦ wk_succ_case hn ihn)
    (fun hG hz hs hn ihG ihz ihs ihn ↦ wk_natrec_case hG hz hs hn ihG ihz ihs ihn)
    (fun ht hEq iht ihEq ↦ wk_conv_case ht hEq iht ihEq)
    (fun hEq ihEq ↦ wk_fromUniv_eq_case hEq ihEq)
    (fun hA ihA ↦ wk_refl_type_case hA ihA)
    (fun hEq ihEq ↦ wk_symm_type_case hEq ihEq)
    (fun h₁ h₂ ih₁ ih₂ ↦ wk_trans_type_case h₁ h₂ ih₁ ih₂)
    (fun hF hFH hGE ihF ihFH ihGE ↦ wk_pi_type_eq_case hF hFH hGE ihF ihFH ihGE)
    (fun ht iht ↦ wk_refl_term_case ht iht)
    (fun hEq ihEq ↦ wk_symm_term_case hEq ihEq)
    (fun h₁ h₂ ih₁ ih₂ ↦ wk_trans_term_case h₁ h₂ ih₁ ih₂)
    (fun hEq hAB ihEq ihAB ↦ wk_conv_term_case hEq hAB ihEq ihAB)
    (fun hF hFH hGE ihF ihFH ihGE ↦ wk_pi_term_eq_case hF hFH hGE ihF ihFH ihGE)
    (fun hfg hab ihfg ihab ↦ wk_app_term_eq_case hfg hab ihfg ihab)
    (fun hF ht ha ihF iht iha ↦ wk_beta_term_eq_case hF ht ha ihF iht iha)
    (fun hF hf hg hfg ihF ihf ihg ihfg ↦ wk_eta_term_eq_case hF hf hg hfg ihF ihf ihg ihfg)
    (fun hmn ihmn ↦ wk_succ_term_eq_case hmn ihmn)
    (fun hFF' hzz' hss' hnn' ihFF' ihzz' ihss' ihnn' ↦
      wk_natrec_term_eq_case hFF' hzz' hss' hnn' ihFF' ihzz' ihss' ihnn')
    (fun hF hz hs ihF ihz ihs ↦ wk_natrecZero_term_eq_case hF hz hs ihF ihz ihs)
    (fun hn hF hz hs ihn ihF ihz ihs ↦ wk_natrecSucc_term_eq_case hn hF hz hs ihn ihF ihz ihs)
    d) hρ hΔ

/-- Weakening of single-step term reduction (`wkRedTerm`). -/
theorem wkStep {Γ Δ : Context} {t u A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (d : Step Γ t u A) :
    Step Δ (wk ρ t) (wk ρ u) (wk ρ A) := by
  induction d with
  | conv hStep hEq ih => exact .conv ih (wkTypeEq hρ hΔ hEq)
  | @app A B t u a _ ha ih =>
      rw [wk, wk, wk_beta (ρ := ρ) (a := a) B]
      exact Step.app ih (wkHasType hρ hΔ ha)
  | @beta A B a t hA ht ha =>
      let hρA := wkTypeWf hρ hΔ hA
      rw [wk, wk, wk_beta (ρ := ρ) (a := a) t, wk_beta (ρ := ρ) (a := a) B]
      exact Step.beta hρA (wkHasType (.lift hρ) (.cons hΔ hρA) ht) (wkHasType hρ hΔ ha)
  | @natrec z s n n' F hF hz hs _ ih =>
      have hρF : TypeWf (.nat :: Δ) (wk (.lift ρ) F) :=
        wkTypeWf (WkCtx.lift (A := .nat) hρ) (.cons hΔ (.nat hΔ)) hF
      have hρz : HasType Δ (wk ρ z) (subst0 (wk (.lift ρ) F) .zero) := by
        have h := wkHasType hρ hΔ hz
        rw [wk_beta (ρ := ρ) (a := .zero) F] at h
        exact h
      have hρs : HasType Δ (wk ρ s) (recStepType (wk (.lift ρ) F)) := by
        have h := wkHasType hρ hΔ hs
        rw [wk_beta_natrec ρ F] at h
        exact h
      rw [wk, wk, wk_beta (ρ := ρ) (a := n) F]
      exact Step.natrec hρF hρz hρs ih
  | @natrecZero z s F hF hz hs =>
      have hρF : TypeWf (.nat :: Δ) (wk (.lift ρ) F) :=
        wkTypeWf (WkCtx.lift (A := .nat) hρ) (.cons hΔ (.nat hΔ)) hF
      have hρz : HasType Δ (wk ρ z) (subst0 (wk (.lift ρ) F) .zero) := by
        have h := wkHasType hρ hΔ hz
        rw [wk_beta (ρ := ρ) (a := .zero) F] at h
        exact h
      have hρs : HasType Δ (wk ρ s) (recStepType (wk (.lift ρ) F)) := by
        have h := wkHasType hρ hΔ hs
        rw [wk_beta_natrec ρ F] at h
        exact h
      rw [wk, wk_beta (ρ := ρ) (a := .zero) F]
      exact Step.natrecZero hρF hρz hρs
  | @natrecSucc n z s F hn hF hz hs =>
      have hρn : HasType Δ (wk ρ n) .nat := wkHasType hρ hΔ hn
      have hρF : TypeWf (.nat :: Δ) (wk (.lift ρ) F) :=
        wkTypeWf (WkCtx.lift (A := .nat) hρ) (.cons hΔ (.nat hΔ)) hF
      have hρz : HasType Δ (wk ρ z) (subst0 (wk (.lift ρ) F) .zero) := by
        have h := wkHasType hρ hΔ hz
        rw [wk_beta (ρ := ρ) (a := .zero) F] at h
        exact h
      have hρs : HasType Δ (wk ρ s) (recStepType (wk (.lift ρ) F)) := by
        have h := wkHasType hρ hΔ hs
        rw [wk_beta_natrec ρ F] at h
        exact h
      rw [wk, wk_beta (ρ := ρ) (a := .succ n) F]
      exact Step.natrecSucc hρn hρF hρz hρs

/-- Weakening of single-step type reduction (`wkRed`). -/
theorem wkTypeStep {Γ Δ : Context} {A B : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) :
    TypeStep Γ A B → TypeStep Δ (wk ρ A) (wk ρ B)
  | .fromUniv hStep => .fromUniv (wkStep hρ hΔ hStep)

/-- Weakening of multi-step type reduction (`wkRed*`). -/
theorem wkTypeStar {Γ Δ : Context} {A B : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) :
    TypeStar Γ A B → TypeStar Δ (wk ρ A) (wk ρ B)
  | .refl hA => .refl (wkTypeWf hρ hΔ hA)
  | .step h₁ h₂ => .step (wkTypeStep hρ hΔ h₁) (wkTypeStar hρ hΔ h₂)

/-- Weakening of multi-step term reduction (`wkRed*Term`). -/
theorem wkStar {Γ Δ : Context} {t u A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) :
    Star Γ t u A → Star Δ (wk ρ t) (wk ρ u) (wk ρ A)
  | .refl ht => .refl (wkHasType hρ hΔ ht)
  | .step h₁ h₂ => .step (wkStep hρ hΔ h₁) (wkStar hρ hΔ h₂)

/-- Weakening of bundled well-formed multi-step type reduction (`wkRed:*:`). -/
theorem wkTypeStarWf {Γ Δ : Context} {A B : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (h : TypeStarWf Γ A B) :
    TypeStarWf Δ (wk ρ A) (wk ρ B) :=
  ⟨wkTypeWf hρ hΔ h.source, wkTypeWf hρ hΔ h.target, wkTypeStar hρ hΔ h.reduction⟩

/-- Weakening of bundled well-typed multi-step term reduction (`wkRed:*:Term`). -/
theorem wkStarWf {Γ Δ : Context} {t u A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (h : StarWf Γ t u A) :
    StarWf Δ (wk ρ t) (wk ρ u) (wk ρ A) :=
  ⟨wkHasType hρ hΔ h.source, wkHasType hρ hΔ h.target, wkStar hρ hΔ h.reduction⟩

end Abel2018

/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/Typed/Properties.agda, Definition/Typed/Reduction.agda,
Definition/Typed/RedSteps.agda, Definition/Typed/EqualityRelation.agda,
Definition/Typed/EqRelInstance.agda.
-/

namespace Abel2018

/-- Induction principle on `HasType` alone (for properties that do not need hypotheses on `TypeWf`/`TypeEq`). -/
theorem HasType.indOnly
    {motive : ∀ (Γ : Context) (t A : Term), HasType Γ t A → Prop}
    (nat : ∀ {Γ} (hΓ : CtxWf Γ), motive Γ .nat .univ (.nat hΓ))
    (pi : ∀ {Γ F G} (hF : HasType Γ F .univ) (hG : HasType (F :: Γ) G .univ),
      motive Γ F .univ hF → motive (F :: Γ) G .univ hG → motive Γ (.pi F G) .univ (.pi hF hG))
    (var : ∀ {Γ A x} (hΓ : CtxWf Γ) (hm : Member x A Γ), motive Γ (.var x) A (.var hΓ hm))
    (lam : ∀ {Γ F G t} (hF : TypeWf Γ F) (ht : HasType (F :: Γ) t G),
      motive (F :: Γ) t G ht → motive Γ (.lam t) (.pi F G) (.lam hF ht))
    (app : ∀ {Γ g a F G} (hg : HasType Γ g (.pi F G)) (ha : HasType Γ a F),
      motive Γ g (.pi F G) hg → motive Γ a F ha → motive Γ (.app g a) (subst0 G a) (.app hg ha))
    (zero : ∀ {Γ} (hΓ : CtxWf Γ), motive Γ .zero .nat (.zero hΓ))
    (succ : ∀ {Γ n} (hn : HasType Γ n .nat), motive Γ n .nat hn → motive Γ (.succ n) .nat (.succ hn))
    (natrec : ∀ {Γ G s z n} (hG : TypeWf (.nat :: Γ) G) (hz : HasType Γ z (subst0 G .zero))
      (hs : HasType Γ s (recStepType G)) (hn : HasType Γ n .nat),
      motive Γ z (subst0 G .zero) hz → motive Γ s (recStepType G) hs → motive Γ n .nat hn →
      motive Γ (.natrec G z s n) (subst0 G n) (.natrec hG hz hs hn))
    (conv : ∀ {Γ t A B} (ht : HasType Γ t A) (hEq : TypeEq Γ A B),
      motive Γ t A ht → motive Γ t B (.conv ht hEq))
    {Γ : Context} {t A : Term} (d : HasType Γ t A) : motive Γ t A d :=
  HasType.rec
    (motive_1 := fun _ _ ↦ True)
    (motive_2 := fun _ _ _ ↦ True)
    (motive_3 := motive)
    (motive_4 := fun _ _ _ _ ↦ True)
    (motive_5 := fun _ _ _ _ _ ↦ True)
    trivial
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun hΓ _ ↦ nat hΓ)
    (fun hF hG ihF ihG ↦ pi hF hG ihF ihG)
    (fun hΓ hm _ ↦ var hΓ hm)
    (fun hF ht _ iht ↦ lam hF ht iht)
    (fun hg ha ihg iha ↦ app hg ha ihg iha)
    (fun hΓ _ ↦ zero hΓ)
    (fun hn ihn ↦ succ hn ihn)
    (fun hG hz hs hn _ ihz ihs ihn ↦ natrec hG hz hs hn ihz ihs ihn)
    (fun ht hEq iht _ ↦ conv ht hEq iht)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    d

theorem CtxWf.tail {Γ : Context} {A : Term} : CtxWf (A :: Γ) → CtxWf Γ
  | .cons hΓ _ => hΓ

theorem CtxWf.headWf {Γ : Context} {A : Term} : CtxWf (A :: Γ) → TypeWf Γ A
  | .cons _ hA => hA

/-- Context well-formedness extracted from a type derivation (`wf`). -/
theorem wfType {Γ : Context} {A : Term} (d : TypeWf Γ A) : CtxWf Γ :=
  TypeWf.rec
    (motive_1 := fun Γ _ ↦ CtxWf Γ)
    (motive_2 := fun Γ _ _ ↦ CtxWf Γ)
    (motive_3 := fun Γ _ _ _ ↦ CtxWf Γ)
    (motive_4 := fun Γ _ _ _ ↦ CtxWf Γ)
    (motive_5 := fun Γ _ _ _ _ ↦ CtxWf Γ)
    .nil
    (fun hΓ hA _ _ ↦ .cons hΓ hA)
    (fun hΓ _ ↦ hΓ)
    (fun hΓ _ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun _ ihA ↦ ihA)
    (fun hΓ _ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun hΓ _ _ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun _ _ _ iha ↦ iha)
    (fun hΓ _ ↦ hΓ)
    (fun _ ihn ↦ ihn)
    (fun _ _ _ _ _ ihz _ _ ↦ ihz)
    (fun _ _ iht _ ↦ iht)
    (fun _ ihEq ↦ ihEq)
    (fun _ ihA ↦ ihA)
    (fun _ ihEq ↦ ihEq)
    (fun _ _ ih₁ _ ↦ ih₁)
    (fun _ _ _ _ ihFH _ ↦ ihFH)
    (fun _ iht ↦ iht)
    (fun _ ihEq ↦ ihEq)
    (fun _ _ ih₁ _ ↦ ih₁)
    (fun _ _ ihEq _ ↦ ihEq)
    (fun _ _ _ _ ihFH _ ↦ ihFH)
    (fun _ _ ihfg _ ↦ ihfg)
    (fun _ _ _ _ _ iha ↦ iha)
    (fun _ _ _ _ _ ihf _ _ ↦ ihf)
    (fun _ ihmn ↦ ihmn)
    (fun _ _ _ _ _ ihzz' _ _ ↦ ihzz')
    (fun _ _ _ _ ihz _ ↦ ihz)
    (fun _ _ _ _ ihn _ _ _ ↦ ihn)
    d

/-- Context well-formedness extracted from a term typing derivation (`wfTerm`). -/
theorem wfTerm {Γ : Context} {t A : Term} (d : HasType Γ t A) : CtxWf Γ :=
  HasType.indOnly (motive := fun Γ _ _ _ ↦ CtxWf Γ)
    (fun hΓ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun hΓ _ ↦ hΓ)
    (fun _ _ iht ↦ CtxWf.tail iht)
    (fun _ _ _ iha ↦ iha)
    (fun hΓ ↦ hΓ)
    (fun _ ihn ↦ ihn)
    (fun _ _ _ _ ihz _ _ ↦ ihz)
    (fun _ _ iht ↦ iht)
    d

/-- Context well-formedness extracted from a type equality derivation (`wfEq`). -/
theorem wfTypeEq {Γ : Context} {A B : Term} (d : TypeEq Γ A B) : CtxWf Γ :=
  TypeEq.rec
    (motive_1 := fun Γ _ ↦ CtxWf Γ)
    (motive_2 := fun Γ _ _ ↦ CtxWf Γ)
    (motive_3 := fun Γ _ _ _ ↦ CtxWf Γ)
    (motive_4 := fun Γ _ _ _ ↦ CtxWf Γ)
    (motive_5 := fun Γ _ _ _ _ ↦ CtxWf Γ)
    .nil
    (fun hΓ hA _ _ ↦ .cons hΓ hA)
    (fun hΓ _ ↦ hΓ)
    (fun hΓ _ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun _ ihA ↦ ihA)
    (fun hΓ _ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun hΓ _ _ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun _ _ _ iha ↦ iha)
    (fun hΓ _ ↦ hΓ)
    (fun _ ihn ↦ ihn)
    (fun _ _ _ _ _ ihz _ _ ↦ ihz)
    (fun _ _ iht _ ↦ iht)
    (fun _ ihEq ↦ ihEq)
    (fun _ ihA ↦ ihA)
    (fun _ ihEq ↦ ihEq)
    (fun _ _ ih₁ _ ↦ ih₁)
    (fun _ _ _ _ ihFH _ ↦ ihFH)
    (fun _ iht ↦ iht)
    (fun _ ihEq ↦ ihEq)
    (fun _ _ ih₁ _ ↦ ih₁)
    (fun _ _ ihEq _ ↦ ihEq)
    (fun _ _ _ _ ihFH _ ↦ ihFH)
    (fun _ _ ihfg _ ↦ ihfg)
    (fun _ _ _ _ _ iha ↦ iha)
    (fun _ _ _ _ _ ihf _ _ ↦ ihf)
    (fun _ ihmn ↦ ihmn)
    (fun _ _ _ _ _ ihzz' _ _ ↦ ihzz')
    (fun _ _ _ _ ihz _ ↦ ihz)
    (fun _ _ _ _ ihn _ _ _ ↦ ihn)
    d

/-- Context well-formedness extracted from a term equality derivation (`wfEqTerm`). -/
theorem wfTermEq {Γ : Context} {t u A : Term} (d : TermEq Γ t u A) : CtxWf Γ :=
  TermEq.rec
    (motive_1 := fun Γ _ ↦ CtxWf Γ)
    (motive_2 := fun Γ _ _ ↦ CtxWf Γ)
    (motive_3 := fun Γ _ _ _ ↦ CtxWf Γ)
    (motive_4 := fun Γ _ _ _ ↦ CtxWf Γ)
    (motive_5 := fun Γ _ _ _ _ ↦ CtxWf Γ)
    .nil
    (fun hΓ hA _ _ ↦ .cons hΓ hA)
    (fun hΓ _ ↦ hΓ)
    (fun hΓ _ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun _ ihA ↦ ihA)
    (fun hΓ _ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun hΓ _ _ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun _ _ _ iha ↦ iha)
    (fun hΓ _ ↦ hΓ)
    (fun _ ihn ↦ ihn)
    (fun _ _ _ _ _ ihz _ _ ↦ ihz)
    (fun _ _ iht _ ↦ iht)
    (fun _ ihEq ↦ ihEq)
    (fun _ ihA ↦ ihA)
    (fun _ ihEq ↦ ihEq)
    (fun _ _ ih₁ _ ↦ ih₁)
    (fun _ _ _ _ ihFH _ ↦ ihFH)
    (fun _ iht ↦ iht)
    (fun _ ihEq ↦ ihEq)
    (fun _ _ ih₁ _ ↦ ih₁)
    (fun _ _ ihEq _ ↦ ihEq)
    (fun _ _ _ _ ihFH _ ↦ ihFH)
    (fun _ _ ihfg _ ↦ ihfg)
    (fun _ _ _ _ _ iha ↦ iha)
    (fun _ _ _ _ _ ihf _ _ ↦ ihf)
    (fun _ ihmn ↦ ihmn)
    (fun _ _ _ _ _ ihzz' _ _ ↦ ihzz')
    (fun _ _ _ _ ihz _ ↦ ihz)
    (fun _ _ _ _ ihn _ _ _ ↦ ihn)
    d

/-- Single-step term reduction is included in judgmental equality (`subsetTerm`, Lemma 2.2). -/
theorem subsetTerm {Γ : Context} {t u A : Term} :
    Step Γ t u A → TermEq Γ t u A
  | .conv hStep hEq => .conv (subsetTerm hStep) hEq
  | .app hStep ha => .app (subsetTerm hStep) (.refl ha)
  | .beta hA ht ha => .beta hA ht ha
  | .natrec hF hz hs hStep =>
      .natrec (.refl hF) (.refl hz) (.refl hs) (subsetTerm hStep)
  | .natrecZero hF hz hs => .natrecZero hF hz hs
  | .natrecSucc hn hF hz hs => .natrecSucc hn hF hz hs

/-- Single-step type reduction is included in judgmental type equality (`subset`, Lemma 2.2). -/
theorem subsetType {Γ : Context} {A B : Term} :
    TypeStep Γ A B → TypeEq Γ A B
  | .fromUniv hStep => .fromUniv (subsetTerm hStep)

/-- Multi-step term reduction is included in judgmental equality (`subset*Term`, Lemma 2.2). -/
theorem subsetStarTerm {Γ : Context} {t u A : Term} :
    Star Γ t u A → TermEq Γ t u A
  | .refl ht => .refl ht
  | .step hStep hStar => .trans (subsetTerm hStep) (subsetStarTerm hStar)

/-- Multi-step type reduction is included in judgmental type equality (`subset*`, Lemma 2.2). -/
theorem subsetStar {Γ : Context} {A B : Term} :
    TypeStar Γ A B → TypeEq Γ A B
  | .refl hA => .refl hA
  | .step hStep hStar => .trans (subsetType hStep) (subsetStar hStar)

/-- Left-hand typing extraction from single-step term reduction (`redFirstTerm`, Lemma 2.3). -/
theorem redFirstTerm {Γ : Context} {t u A : Term} :
    Step Γ t u A → HasType Γ t A
  | .conv hStep hEq => .conv (redFirstTerm hStep) hEq
  | .app hStep ha => .app (redFirstTerm hStep) ha
  | .beta hA ht ha => .app (.lam hA ht) ha
  | .natrec hF hz hs hStep => .natrec hF hz hs (redFirstTerm hStep)
  | .natrecZero hF hz hs => .natrec hF hz hs (.zero (wfTerm hz))
  | .natrecSucc hn hF hz hs => .natrec hF hz hs (.succ hn)

/-- Left-hand well-formedness extraction from single-step type reduction (`redFirst`, Lemma 2.3). -/
theorem redFirstType {Γ : Context} {A B : Term} :
    TypeStep Γ A B → TypeWf Γ A
  | .fromUniv hStep => .fromUniv (redFirstTerm hStep)

/-- Left-hand typing extraction from multi-step term reduction (`redFirst*Term`, Lemma 2.3). -/
theorem redFirstStarTerm {Γ : Context} {t u A : Term} :
    Star Γ t u A → HasType Γ t A
  | .refl ht => ht
  | .step hStep _ => redFirstTerm hStep

/-- Left-hand well-formedness extraction from multi-step type reduction (`redFirst*`, Lemma 2.3). -/
theorem redFirstStar {Γ : Context} {A B : Term} :
    TypeStar Γ A B → TypeWf Γ A
  | .refl hA => hA
  | .step hStep _ => redFirstType hStep

/-- No neutral term is well-typed in the empty context (`noNe`). -/
theorem noNe {t A : Term} (ht : HasType [] t A) (hn : Neutral t) : False := by
  have aux : ∀ {Γ : Context} {t A : Term}, HasType Γ t A → Γ = [] → Neutral t → False := by
    intro Γ t A h
    induction h using HasType.indOnly with
    | nat _ => intro _ hn; cases hn
    | pi _ _ _ _ => intro _ hn; cases hn
    | var _ hm =>
        intro hΓ _
        subst hΓ
        cases hm
    | lam _ _ _ => intro _ hn; cases hn
    | app _ _ ihg _ =>
        intro hΓ hn
        cases hn with
        | app hn' => exact ihg hΓ hn'
    | zero _ => intro _ hn; cases hn
    | succ _ _ => intro _ hn; cases hn
    | natrec _ _ _ _ _ _ ihn =>
        intro hΓ hn
        cases hn with
        | natrec hn' => exact ihn hΓ hn'
    | conv _ _ iht =>
        intro hΓ hn
        exact iht hΓ hn
  exact aux ht rfl hn

/-- Neutral terms do not weak-head reduce (`neRedTerm`, Lemma 2.4). -/
theorem neRedTerm {Γ : Context} {t u A : Term} (d : Step Γ t u A) (hn : Neutral t) : False := by
  induction d with
  | conv _ _ ih => exact ih hn
  | app _ _ ih =>
      cases hn with
      | app hn' => exact ih hn'
  | beta _ _ _ =>
      cases hn with
      | app hn' => cases hn'
  | natrec _ _ _ _ ih =>
      cases hn with
      | natrec hn' => exact ih hn'
  | natrecZero _ _ _ =>
      cases hn with
      | natrec hn' => cases hn'
  | natrecSucc _ _ _ _ =>
      cases hn with
      | natrec hn' => cases hn'

/-- Neutral types do not weak-head reduce (`neRed`, Lemma 2.4). -/
theorem neRedType {Γ : Context} {A B : Term} :
    TypeStep Γ A B → Neutral A → False
  | .fromUniv hStep, hn => neRedTerm hStep hn

/-- Weak-head normal forms do not weak-head reduce (`whnfRedTerm`, Lemma 2.4). -/
theorem whnfRedTerm {Γ : Context} {t u A : Term} (d : Step Γ t u A) (hw : Whnf t) : False := by
  induction d with
  | conv _ _ ih => exact ih hw
  | app hStep _ _ =>
      cases hw with
      | neutral hn =>
          cases hn with
          | app hn' => exact neRedTerm hStep hn'
  | beta _ _ _ =>
      cases hw with
      | neutral hn =>
          cases hn with
          | app hn' => cases hn'
  | natrec _ _ _ hStep _ =>
      cases hw with
      | neutral hn =>
          cases hn with
          | natrec hn' => exact neRedTerm hStep hn'
  | natrecZero _ _ _ =>
      cases hw with
      | neutral hn =>
          cases hn with
          | natrec hn' => cases hn'
  | natrecSucc _ _ _ _ =>
      cases hw with
      | neutral hn =>
          cases hn with
          | natrec hn' => cases hn'

/-- Weak-head normal types do not weak-head reduce (`whnfRed`, Lemma 2.4). -/
theorem whnfRedType {Γ : Context} {A B : Term} :
    TypeStep Γ A B → Whnf A → False
  | .fromUniv hStep, hw => whnfRedTerm hStep hw

/-- Multi-step reduction from a term in WHNF is trivial (`whnfRed*Term`, Lemma 2.4). -/
theorem whnfRedStarTerm {Γ : Context} {t u A : Term} :
    Star Γ t u A → Whnf t → t = u
  | .refl _, _ => rfl
  | .step hStep _, hw => False.elim (whnfRedTerm hStep hw)

/-- Multi-step reduction from a type in WHNF is trivial (`whnfRed*`, Lemma 2.4). -/
theorem whnfRedStar {Γ : Context} {A B : Term} :
    TypeStar Γ A B → Whnf A → A = B
  | .refl _, _ => rfl
  | .step hStep _, hw => False.elim (whnfRedType hStep hw)

/-- Determinism of single-step term reduction (`whrDetTerm`, Lemma 2.5). -/
theorem whrDetTerm {Γ : Context} {t u A u' A' : Term}
    (d₁ : Step Γ t u A) (d₂ : Step Γ t u' A') : u = u' := by
  induction d₁ generalizing u' A' with
  | conv _ _ ih => exact ih d₂
  | @app A₀ B₀ f₀ u₀ a₀ d₁ _ ih =>
      have aux : ∀ {t₀ u' A' : Term}, Step Γ t₀ u' A' →
          t₀ = .app f₀ a₀ → Term.app u₀ a₀ = u' := by
        intro t₀ u' A' hStep
        induction hStep with
        | conv _ _ ih₂ => intro heq; exact ih₂ heq
        | app d₂ _ =>
            intro heq
            cases heq
            exact congrArg (fun x ↦ Term.app x a₀) (ih d₂)
        | beta _ _ _ =>
            intro heq
            cases heq
            exact False.elim (whnfRedTerm d₁ .lam)
        | natrec _ _ _ _ => intro heq; cases heq
        | natrecZero _ _ _ => intro heq; cases heq
        | natrecSucc _ _ _ _ => intro heq; cases heq
      exact aux d₂ rfl
  | @beta A₀ B₀ a₀ body₀ _ _ _ =>
      have aux : ∀ {t₀ u' A' : Term}, Step Γ t₀ u' A' →
          t₀ = .app (.lam body₀) a₀ → subst0 body₀ a₀ = u' := by
        intro t₀ u' A' hStep
        induction hStep with
        | conv _ _ ih₂ => intro heq; exact ih₂ heq
        | app d₂ _ =>
            intro heq
            cases heq
            exact False.elim (whnfRedTerm d₂ .lam)
        | beta _ _ _ =>
            intro heq
            cases heq
            rfl
        | natrec _ _ _ _ => intro heq; cases heq
        | natrecZero _ _ _ => intro heq; cases heq
        | natrecSucc _ _ _ _ => intro heq; cases heq
      exact aux d₂ rfl
  | @natrec z₀ s₀ n₀ n'₀ F₀ _ _ _ d₁ ih =>
      have aux : ∀ {t₀ u' A' : Term}, Step Γ t₀ u' A' →
          t₀ = .natrec F₀ z₀ s₀ n₀ → Term.natrec F₀ z₀ s₀ n'₀ = u' := by
        intro t₀ u' A' hStep
        induction hStep with
        | conv _ _ ih₂ => intro heq; exact ih₂ heq
        | app _ _ => intro heq; cases heq
        | beta _ _ _ => intro heq; cases heq
        | natrec _ _ _ d₂ =>
            intro heq
            cases heq
            exact congrArg (Term.natrec F₀ z₀ s₀) (ih d₂)
        | natrecZero _ _ _ =>
            intro heq
            cases heq
            exact False.elim (whnfRedTerm d₁ .zero)
        | natrecSucc _ _ _ _ =>
            intro heq
            cases heq
            exact False.elim (whnfRedTerm d₁ .succ)
      exact aux d₂ rfl
  | @natrecZero z₀ s₀ F₀ _ _ _ =>
      have aux : ∀ {t₀ u' A' : Term}, Step Γ t₀ u' A' →
          t₀ = .natrec F₀ z₀ s₀ .zero → z₀ = u' := by
        intro t₀ u' A' hStep
        induction hStep with
        | conv _ _ ih₂ => intro heq; exact ih₂ heq
        | app _ _ => intro heq; cases heq
        | beta _ _ _ => intro heq; cases heq
        | natrec _ _ _ d₂ =>
            intro heq
            cases heq
            exact False.elim (whnfRedTerm d₂ .zero)
        | natrecZero _ _ _ =>
            intro heq
            cases heq
            rfl
        | natrecSucc _ _ _ _ => intro heq; cases heq
      exact aux d₂ rfl
  | @natrecSucc n₀ z₀ s₀ F₀ _ _ _ _ =>
      have aux : ∀ {t₀ u' A' : Term}, Step Γ t₀ u' A' →
          t₀ = .natrec F₀ z₀ s₀ (.succ n₀) →
          .app (.app s₀ n₀) (.natrec F₀ z₀ s₀ n₀) = u' := by
        intro t₀ u' A' hStep
        induction hStep with
        | conv _ _ ih₂ => intro heq; exact ih₂ heq
        | app _ _ => intro heq; cases heq
        | beta _ _ _ => intro heq; cases heq
        | natrec _ _ _ d₂ =>
            intro heq
            cases heq
            exact False.elim (whnfRedTerm d₂ .succ)
        | natrecZero _ _ _ => intro heq; cases heq
        | natrecSucc _ _ _ _ =>
            intro heq
            cases heq
            rfl
      exact aux d₂ rfl

/-- Determinism of single-step type reduction (`whrDet`, Lemma 2.5). -/
theorem whrDetType {Γ : Context} {A B B' : Term} :
    TypeStep Γ A B → TypeStep Γ A B' → B = B'
  | .fromUniv d₁, .fromUniv d₂ => whrDetTerm d₁ d₂

/-- Confluence toward WHNF for term reduction (`whrDet↘Term`, Lemma 2.5). -/
theorem whrDetWhnfTerm {Γ : Context} {t u A u' : Term}
    (d : TermWhnf Γ t u A) (d' : Star Γ t u' A) : Star Γ u' u A := by
  rcases d with ⟨dStar, hw⟩
  induction d' with
  | refl _ => exact dStar
  | step hStep₂ _ ih =>
      cases dStar with
      | refl _ => exact False.elim (whnfRedTerm hStep₂ hw)
      | step hStep₁ dStar₁ =>
          have heq := whrDetTerm hStep₁ hStep₂
          subst heq
          exact ih dStar₁

/-- Uniqueness of term WHNF (`whrDet*Term`, Lemma 2.5). -/
theorem whrDetStarTerm {Γ : Context} {t u A u' : Term}
    (d₁ : TermWhnf Γ t u A) (d₂ : TermWhnf Γ t u' A) : u = u' := by
  have hStar : Star Γ u' u A := whrDetWhnfTerm d₁ d₂.1
  exact (whnfRedStarTerm hStar d₂.2).symm

/-- Confluence toward WHNF for type reduction. -/
theorem whrDetWhnfType {Γ : Context} {A B B' : Term}
    (d : TypeWhnf Γ A B) (d' : TypeStar Γ A B') : TypeStar Γ B' B := by
  rcases d with ⟨dStar, hw⟩
  induction d' with
  | refl _ => exact dStar
  | step hStep₂ _ ih =>
      cases dStar with
      | refl _ => exact False.elim (whnfRedType hStep₂ hw)
      | step hStep₁ dStar₁ =>
          have heq := whrDetType hStep₁ hStep₂
          subst heq
          exact ih dStar₁

/-- Uniqueness of type WHNF (`whrDet*`, Lemma 2.5). -/
theorem whrDetStar {Γ : Context} {A B B' : Term}
    (d₁ : TypeWhnf Γ A B) (d₂ : TypeWhnf Γ A B') : B = B' := by
  have hStar : TypeStar Γ B' B := whrDetWhnfType d₁ d₂.1
  exact (whnfRedStar hStar d₂.2).symm

/-- Identity bundled type reduction (`idRed:*:`). -/
theorem idRedWf {Γ : Context} {A : Term} (hA : TypeWf Γ A) : TypeStarWf Γ A A :=
  ⟨hA, hA, .refl hA⟩

/-- Identity bundled term reduction (`idRedTerm:*:`). -/
theorem idRedTermWf {Γ : Context} {t A : Term} (ht : HasType Γ t A) : StarWf Γ t t A :=
  ⟨ht, ht, .refl ht⟩

/-- The universe `U` is not a well-typed term (`UnotInA`). -/
theorem UnotInA {Γ : Context} {A : Term} (h : HasType Γ .univ A) : False := by
  have aux : ∀ {Γ : Context} {u A : Term}, HasType Γ u A → u = .univ → False := by
    intro Γ u A ht
    induction ht using HasType.indOnly with
    | nat _ => intro hu; cases hu
    | pi _ _ _ _ => intro hu; cases hu
    | var _ _ => intro hu; cases hu
    | lam _ _ _ => intro hu; cases hu
    | app _ _ _ _ => intro hu; cases hu
    | zero _ => intro hu; cases hu
    | succ _ _ => intro hu; cases hu
    | natrec _ _ _ _ _ _ _ => intro hu; cases hu
    | conv _ _ ih => intro hu; exact ih hu
  exact aux h rfl

theorem UnotInA_subst {Γ : Context} {A B t a : Term}
    (heq : subst0 t a = .univ) (ha : HasType Γ a A) (ht : HasType (A :: Γ) t B) : False := by
  have aux : ∀ {Δ : Context} {t B : Term}, HasType Δ t B →
      subst0 t a = .univ → False := by
    intro Δ t B h
    induction h using HasType.indOnly with
    | nat _ => intro h; cases h
    | pi _ _ _ _ => intro h; cases h
    | @var _ _ x _ _ =>
        intro h
        cases x with
        | zero =>
            change a = .univ at h
            subst h
            exact UnotInA ha
        | succ _ => cases h
    | lam _ _ _ => intro h; cases h
    | app _ _ _ _ => intro h; cases h
    | zero _ => intro h; cases h
    | succ _ _ => intro h; cases h
    | natrec _ _ _ _ _ _ _ => intro h; cases h
    | conv _ _ ih => intro h; exact ih h
  exact aux ht heq

theorem redUStarTerm' {Γ : Context} {A B U' : Term}
    (heq : U' = .univ) (d : Step Γ A U' B) : False := by
  induction d with
  | conv _ _ ih => exact ih heq
  | app _ _ => cases heq
  | beta _ ht ha => exact UnotInA_subst heq ha ht
  | natrec _ _ _ _ => cases heq
  | natrecZero _ hz _ =>
      subst heq
      exact UnotInA hz
  | natrecSucc _ _ _ _ => cases heq

theorem redUStarTerm {Γ : Context} {A B : Term} (d : Star Γ A .univ B) : False := by
  generalize hu : Term.univ = u at d
  induction d with
  | refl ht =>
      subst hu
      exact UnotInA ht
  | step _ _ ih => exact ih hu

/-- No type steps to `U` (`redU`). -/
theorem redU {Γ : Context} {A : Term} : TypeStep Γ A .univ → False
  | .fromUniv d => redUStarTerm' rfl d

/-- Only `U` reduces to `U` (`redU*`). -/
theorem redUStar {Γ : Context} {A : Term} (d : TypeStar Γ A .univ) : A = .univ := by
  have aux : ∀ {A u : Term}, TypeStar Γ A u → u = .univ → A = .univ := by
    intro A u h
    induction h with
    | refl _ => intro hu; exact hu
    | step hStep _ ih =>
        intro hu
        have h' := ih hu
        subst h'
        exact False.elim (redU hStep)
  exact aux d rfl

/-- Weak-head expansion of type equality (`reduction`). -/
theorem reduction {Γ : Context} {A A' B B' : Term}
    (D : TypeStar Γ A A') (D' : TypeStar Γ B B')
    (_whnfA' : Whnf A') (_whnfB' : Whnf B')
    (hEq : TypeEq Γ A' B') : TypeEq Γ A B :=
  .trans (subsetStar D) (.trans hEq (.symm (subsetStar D')))

theorem reduction' {Γ : Context} {A A' B B' : Term}
    (D : TypeStar Γ A A') (D' : TypeStar Γ B B')
    (_whnfA' : Whnf A') (_whnfB' : Whnf B')
    (hEq : TypeEq Γ A B) : TypeEq Γ A' B' :=
  .trans (.symm (subsetStar D)) (.trans hEq (subsetStar D'))

/-- Weak-head expansion of term equality (`reductionₜ`). -/
theorem reductionTerm {Γ : Context} {a a' b b' A B : Term}
    (D : TypeStar Γ A B) (d : Star Γ a a' B) (d' : Star Γ b b' B)
    (_whnfB : Whnf B) (_whnfa' : Whnf a') (_whnfb' : Whnf b')
    (hEq : TermEq Γ a' b' B) : TermEq Γ a b A :=
  .conv (.trans (subsetStarTerm d) (.trans hEq (.symm (subsetStarTerm d'))))
    (.symm (subsetStar D))

theorem reductionTerm' {Γ : Context} {a a' b b' A B : Term}
    (D : TypeStar Γ A B) (d : Star Γ a a' B) (d' : Star Γ b b' B)
    (_whnfB : Whnf B) (_whnfa' : Whnf a') (_whnfb' : Whnf b')
    (hEq : TermEq Γ a b A) : TermEq Γ a' b' B :=
  .trans (.symm (subsetStarTerm d))
    (.trans (.conv hEq (subsetStar D)) (subsetStarTerm d'))

/-- Concatenation of multi-step type reductions (`_⇨*_`). -/
theorem TypeStar.trans {Γ : Context} {A B C : Term} :
    TypeStar Γ A B → TypeStar Γ B C → TypeStar Γ A C
  | .refl _, hBC => hBC
  | .step h₁ h₂, hBC => .step h₁ (h₂.trans hBC)

/-- Concatenation of multi-step term reductions (`_⇨∷*_`). -/
theorem Star.trans {Γ : Context} {t u r A : Term} :
    Star Γ t u A → Star Γ u r A → Star Γ t r A
  | .refl _, hur => hur
  | .step h₁ h₂, hur => .step h₁ (h₂.trans hur)

/-- Conversion of multi-step term reductions (`conv*`). -/
theorem Star.conv {Γ : Context} {t u A B : Term} :
    Star Γ t u A → TypeEq Γ A B → Star Γ t u B
  | .refl ht, hAB => .refl (.conv ht hAB)
  | .step h₁ h₂, hAB => .step (.conv h₁ hAB) (h₂.conv hAB)

/-- Embedding universe term reduction into type reduction (`univ*`). -/
theorem TypeStar.fromUniv {Γ : Context} {A B : Term} (d : Star Γ A B .univ) :
    TypeStar Γ A B := by
  generalize hu : Term.univ = U₀ at d
  induction d with
  | refl hA =>
      subst hu
      exact .refl (.fromUniv hA)
  | step h₁ _ ih =>
      subst hu
      exact .step (.fromUniv h₁) (ih rfl)

/-- Application congruence for multi-step reduction (`app-subst*`). -/
theorem Star.app {Γ : Context} {A B t t' a : Term}
    (d : Star Γ t t' (.pi A B)) (ha : HasType Γ a A) :
    Star Γ (.app t a) (.app t' a) (subst0 B a) := by
  generalize hpi : Term.pi A B = P at d
  induction d with
  | refl ht =>
      subst hpi
      exact .refl (.app ht ha)
  | step h₁ _ ih =>
      subst hpi
      exact .step (.app h₁ ha) (ih rfl)



theorem EqRelSet.neToType (eqrel : EqRelSet) {Γ : Context} {k l : Term}
    (h : eqrel.NeEqRel Γ k l .univ) : eqrel.TypeEqRel Γ k l :=
  eqrel.univ (eqrel.neToTerm h)

/-- Judgmental equality instance of `EqRelSet` (`Definition.Typed.EqRelInstance`). -/
def synEqRel : EqRelSet where
  TypeEqRel := TypeEq
  TermEqRel := TermEq
  NeEqRel := TermEq
  neToTerm h := h
  typeToEq h := h
  termToEq h := h
  univ := .fromUniv
  symmType := .symm
  symmTerm := .symm
  symmNe := .symm
  transType := .trans
  transTerm := .trans
  transNe := .trans
  convTerm := .conv
  convNe := .conv
  wkType := wkTypeEq
  wkTerm := wkTermEq
  wkNe := wkTermEq
  redType := reduction
  redTerm := reductionTerm
  univRefl hΓ := .refl (.univ hΓ)
  natRefl hΓ := .refl (.nat hΓ)
  natTermRefl hΓ := .refl (.nat hΓ)
  piCong := .pi
  piTermCong := .pi
  zeroRefl hΓ := .refl (.zero hΓ)
  succCong := .succ
  etaEq hF hf hg _ _ hfg := .eta hF hf hg hfg
  varRefl := .refl
  appCong := .app
  natrecCong := .natrec

end Abel2018

/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/Conversion.agda, Definition/Conversion/Whnf.agda,
Definition/Conversion/Reduction.agda, Definition/Conversion/Weakening.agda,
plus executable adequacy and fuel stability for Abel2018/Algorithm.lean.
-/

namespace Abel2018



/-- Extraction of neutrality from `ConvNeUp` (`ne~↑`). -/
theorem neConvNeUp {Γ : Context} {t u A : Term} (d : ConvNeUp Γ t u A) :
    Neutral t ∧ Neutral u :=
  ConvNeUp.rec
    (motive_1 := fun _ t u _ _ ↦ Neutral t ∧ Neutral u)
    (motive_2 := fun _ t u A _ ↦ Whnf A ∧ Neutral t ∧ Neutral u)
    (motive_3 := fun _ _ _ _ ↦ True)
    (motive_4 := fun _ _ _ _ ↦ True)
    (motive_5 := fun _ _ _ _ _ ↦ True)
    (motive_6 := fun _ _ _ _ _ ↦ True)
    (fun {_Γ x y _} _ _ ↦ ⟨.var x, .var y⟩)
    (fun _ _ ihk _ ↦ ⟨.app ihk.2.1, .app ihk.2.2⟩)
    (fun _ _ _ _ _ _ _ ihk ↦ ⟨.natrec ihk.2.1, .natrec ihk.2.2⟩)
    (fun _ hw _ ih ↦ ⟨hw, ih⟩)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ ↦ trivial)
    (fun _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ ↦ trivial)
    d

/-- Extraction of WHNF and neutrality from `ConvNeDown` (`ne~↓`). -/
theorem neConvNeDown {Γ : Context} {t u A : Term} :
    ConvNeDown Γ t u A → Whnf A ∧ Neutral t ∧ Neutral u
  | .mk _ hw hne => ⟨hw, neConvNeUp hne⟩

/-- Extraction of WHNF from `ConvTypeDown` (`whnfConv↓`). -/
theorem whnfConvTypeDown {Γ : Context} {A B : Term} :
    ConvTypeDown Γ A B → Whnf A ∧ Whnf B
  | .univRefl _ => ⟨.univ, .univ⟩
  | .natRefl _ => ⟨.nat, .nat⟩
  | .ne hne =>
      let ⟨_, neK, neL⟩ := neConvNeDown hne
      ⟨.neutral neK, .neutral neL⟩
  | .piCong _ _ _ => ⟨.pi, .pi⟩

/-- Extraction of WHNF from `ConvTermDown` (`whnfConv↓Term`). -/
theorem whnfConvTermDown {Γ : Context} {t u A : Term} :
    ConvTermDown Γ t u A → Whnf A ∧ Whnf t ∧ Whnf u
  | .natIns hne =>
      let ⟨_, neK, neL⟩ := neConvNeDown hne
      ⟨.nat, .neutral neK, .neutral neL⟩
  | .neIns _ _ neN hne =>
      let ⟨_, neK, neL⟩ := neConvNeDown hne
      ⟨.neutral neN, .neutral neK, .neutral neL⟩
  | .univ _ _ hAB => ⟨.univ, whnfConvTypeDown hAB⟩
  | .zeroRefl _ => ⟨.nat, .zero, .zero⟩
  | .succCong _ => ⟨.nat, .succ, .succ⟩
  | .etaEq _ _ _ wf wg _ => ⟨.pi, wf, wg⟩

/-- Weak-head expansion of algorithmic type equality (`reductionConv↑`). -/
theorem reductionConvTypeUp {Γ : Context} {A A' B B' : Term}
    (DA : TypeStar Γ A A') (DB : TypeStar Γ B B')
    (whnfA' : Whnf A') (whnfB' : Whnf B')
    (h : ConvTypeUp Γ A' B') : ConvTypeUp Γ A B := by
  rcases h with ⟨DA'', DB'', whnfA'', whnfB'', hDown⟩
  have eqA := whnfRedStar DA'' whnfA'
  have eqB := whnfRedStar DB'' whnfB'
  subst eqA eqB
  exact .mk DA DB whnfA'' whnfB'' hDown

/-- Weak-head expansion of algorithmic term equality (`reductionConv↑Term`). -/
theorem reductionConvTermUp {Γ : Context} {t t' u u' A B : Term}
    (DA : TypeStar Γ A B) (dt : Star Γ t t' B) (du : Star Γ u u' B)
    (whnfB : Whnf B) (whnft' : Whnf t') (whnfu' : Whnf u')
    (h : ConvTermUp Γ t' u' B) : ConvTermUp Γ t u A := by
  rcases h with ⟨DB', dt'', du'', whnfB', whnft'', whnfu'', hDown⟩
  have eqB := whnfRedStar DB' whnfB
  subst eqB
  have eqt := whnfRedStarTerm dt'' whnft'
  have equ := whnfRedStarTerm du'' whnfu'
  subst eqt equ
  exact .mk DA dt du whnfB' whnft'' whnfu'' hDown

private abbrev WkConvNeUpMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → ConvNeUp Δ (wk ρ t) (wk ρ u) (wk ρ A)

private abbrev WkConvNeDownMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → ConvNeDown Δ (wk ρ t) (wk ρ u) (wk ρ A)

private abbrev WkConvTypeUpMotive (Γ : Context) (A B : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → ConvTypeUp Δ (wk ρ A) (wk ρ B)

private abbrev WkConvTypeDownMotive (Γ : Context) (A B : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → ConvTypeDown Δ (wk ρ A) (wk ρ B)

private abbrev WkConvTermUpMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → ConvTermUp Δ (wk ρ t) (wk ρ u) (wk ρ A)

private abbrev WkConvTermDownMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → ConvTermDown Δ (wk ρ t) (wk ρ u) (wk ρ A)

private theorem wkConv_var_case {Γ : Context} {x y : Nat} {A : Term}
    (hx : HasType Γ (.var x) A) (hxy : x = y) :
    WkConvNeUpMotive Γ (.var x) (.var y) A :=
  fun {_Δ ρ} hρ hΔ ↦ .var (wkHasType hρ hΔ hx) (congrArg (wkVar ρ) hxy)

private theorem wkConv_app_case {Γ : Context} {k l t v F G : Term}
    (_hkl : ConvNeDown Γ k l (.pi F G)) (_htv : ConvTermUp Γ t v F)
    (ihkl : WkConvNeDownMotive Γ k l (.pi F G))
    (ihtv : WkConvTermUpMotive Γ t v F) :
    WkConvNeUpMotive Γ (.app k t) (.app l v) (subst0 G t) := by
  intro Δ ρ hρ hΔ
  rw [wk, wk, wk_beta (ρ := ρ) (a := t) G]
  exact .app (ihkl hρ hΔ) (ihtv hρ hΔ)

private theorem wkConv_natrec_case {Γ : Context} {k l h g a₀ b₀ F G : Term}
    (_hFG : ConvTypeUp (.nat :: Γ) F G)
    (_hab : ConvTermUp Γ a₀ b₀ (subst0 F .zero))
    (_hhg : ConvTermUp Γ h g (recStepType F))
    (_hkl : ConvNeDown Γ k l .nat)
    (ihFG : WkConvTypeUpMotive (.nat :: Γ) F G)
    (ihab : WkConvTermUpMotive Γ a₀ b₀ (subst0 F .zero))
    (ihhg : WkConvTermUpMotive Γ h g (recStepType F))
    (ihkl : WkConvNeDownMotive Γ k l .nat) :
    WkConvNeUpMotive Γ (.natrec F a₀ h k) (.natrec G b₀ g l) (subst0 F k) := by
  intro Δ ρ hρ hΔ
  have hρFG : ConvTypeUp (.nat :: Δ) (wk (.lift ρ) F) (wk (.lift ρ) G) :=
    ihFG (WkCtx.lift (A := .nat) hρ) (.cons hΔ (.nat hΔ))
  have hρab : ConvTermUp Δ (wk ρ a₀) (wk ρ b₀) (subst0 (wk (.lift ρ) F) .zero) := by
    have h' := ihab hρ hΔ
    rw [wk_beta (ρ := ρ) (a := .zero) F] at h'
    exact h'
  have hρhg : ConvTermUp Δ (wk ρ h) (wk ρ g) (recStepType (wk (.lift ρ) F)) := by
    have h' := ihhg hρ hΔ
    rw [wk_beta_natrec ρ F] at h'
    exact h'
  have hρkl : ConvNeDown Δ (wk ρ k) (wk ρ l) .nat := ihkl hρ hΔ
  rw [wk, wk, wk_beta (ρ := ρ) (a := k) F]
  exact .natrec hρFG hρab hρhg hρkl

private theorem wkConv_neDown_case {Γ : Context} {k l A B : Term}
    (D : TypeStar Γ A B) (hw : Whnf B) (_hkl : ConvNeUp Γ k l A)
    (ihkl : WkConvNeUpMotive Γ k l A) :
    WkConvNeDownMotive Γ k l B :=
  fun {_Δ ρ} hρ hΔ ↦ .mk (wkTypeStar hρ hΔ D) (hw.wk ρ) (ihkl hρ hΔ)

private theorem wkConv_typeUp_case {Γ : Context} {A B A' B' : Term}
    (DA : TypeStar Γ A A') (DB : TypeStar Γ B B')
    (hwA : Whnf A') (hwB : Whnf B')
    (_hAB : ConvTypeDown Γ A' B')
    (ihAB : WkConvTypeDownMotive Γ A' B') :
    WkConvTypeUpMotive Γ A B :=
  fun {_Δ ρ} hρ hΔ ↦
    .mk (wkTypeStar hρ hΔ DA) (wkTypeStar hρ hΔ DB) (hwA.wk ρ) (hwB.wk ρ) (ihAB hρ hΔ)

private theorem wkConv_univRefl_case {Γ : Context} (_hΓ : CtxWf Γ) :
    WkConvTypeDownMotive Γ .univ .univ :=
  fun _ hΔ ↦ .univRefl hΔ

private theorem wkConv_natRefl_case {Γ : Context} (_hΓ : CtxWf Γ) :
    WkConvTypeDownMotive Γ .nat .nat :=
  fun _ hΔ ↦ .natRefl hΔ

private theorem wkConv_neType_case {Γ : Context} {K L : Term}
    (_hKL : ConvNeDown Γ K L .univ) (ihKL : WkConvNeDownMotive Γ K L .univ) :
    WkConvTypeDownMotive Γ K L :=
  fun hρ hΔ ↦ .ne (ihKL hρ hΔ)

private theorem wkConv_piCong_case {Γ : Context} {F G H E : Term}
    (hF : TypeWf Γ F) (_hFH : ConvTypeUp Γ F H) (_hGE : ConvTypeUp (F :: Γ) G E)
    (ihFH : WkConvTypeUpMotive Γ F H)
    (ihGE : WkConvTypeUpMotive (F :: Γ) G E) :
    WkConvTypeDownMotive Γ (.pi F G) (.pi H E) :=
  fun hρ hΔ ↦
    let hρF := wkTypeWf hρ hΔ hF
    .piCong hρF (ihFH hρ hΔ) (ihGE (.lift hρ) (.cons hΔ hρF))

private theorem wkConv_termUp_case {Γ : Context} {t u A B t' u' : Term}
    (DA : TypeStar Γ A B) (dt : Star Γ t t' B) (du : Star Γ u u' B)
    (hwB : Whnf B) (hwt : Whnf t') (hwu : Whnf u')
    (_htu : ConvTermDown Γ t' u' B)
    (ihtu : WkConvTermDownMotive Γ t' u' B) :
    WkConvTermUpMotive Γ t u A :=
  fun {_Δ ρ} hρ hΔ ↦
    .mk (wkTypeStar hρ hΔ DA) (wkStar hρ hΔ dt) (wkStar hρ hΔ du)
      (hwB.wk ρ) (hwt.wk ρ) (hwu.wk ρ) (ihtu hρ hΔ)

private theorem wkConv_natIns_case {Γ : Context} {k l : Term}
    (_hkl : ConvNeDown Γ k l .nat) (ihkl : WkConvNeDownMotive Γ k l .nat) :
    WkConvTermDownMotive Γ k l .nat :=
  fun hρ hΔ ↦ .natIns (ihkl hρ hΔ)

private theorem wkConv_neIns_case {Γ : Context} {k l M N : Term}
    (hk : HasType Γ k N) (hl : HasType Γ l N) (neN : Neutral N)
    (_hkl : ConvNeDown Γ k l M) (ihkl : WkConvNeDownMotive Γ k l M) :
    WkConvTermDownMotive Γ k l N :=
  fun {_Δ ρ} hρ hΔ ↦
    .neIns (wkHasType hρ hΔ hk) (wkHasType hρ hΔ hl) (neN.wk ρ) (ihkl hρ hΔ)

private theorem wkConv_univ_case {Γ : Context} {A B : Term}
    (hA : HasType Γ A .univ) (hB : HasType Γ B .univ)
    (_hAB : ConvTypeDown Γ A B) (ihAB : WkConvTypeDownMotive Γ A B) :
    WkConvTermDownMotive Γ A B .univ :=
  fun hρ hΔ ↦ .univ (wkHasType hρ hΔ hA) (wkHasType hρ hΔ hB) (ihAB hρ hΔ)

private theorem wkConv_zeroRefl_case {Γ : Context} (_hΓ : CtxWf Γ) :
    WkConvTermDownMotive Γ .zero .zero .nat :=
  fun _ hΔ ↦ .zeroRefl hΔ

private theorem wkConv_succCong_case {Γ : Context} {m n : Term}
    (_hmn : ConvTermUp Γ m n .nat) (ihmn : WkConvTermUpMotive Γ m n .nat) :
    WkConvTermDownMotive Γ (.succ m) (.succ n) .nat :=
  fun hρ hΔ ↦ .succCong (ihmn hρ hΔ)

private theorem wkConv_etaEq_case {Γ : Context} {f g F G : Term}
    (hF : TypeWf Γ F) (hf : HasType Γ f (.pi F G)) (hg : HasType Γ g (.pi F G))
    (hwf : Whnf f) (hwg : Whnf g)
    (_hfg : ConvTermUp (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G)
    (ihfg : WkConvTermUpMotive (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G) :
    WkConvTermDownMotive Γ f g (.pi F G) := by
  intro Δ ρ hρ hΔ
  let hρF := wkTypeWf hρ hΔ hF
  have hfg' : ConvTermUp (wk ρ F :: Δ)
      (.app (wk (.lift ρ) (wk1 f)) (.var 0))
      (.app (wk (.lift ρ) (wk1 g)) (.var 0))
      (wk (.lift ρ) G) :=
    ihfg (.lift hρ) (.cons hΔ hρF)
  rw [← wk1_wk_eq_lift_wk1 ρ f, ← wk1_wk_eq_lift_wk1 ρ g] at hfg'
  exact .etaEq hρF (wkHasType hρ hΔ hf) (wkHasType hρ hΔ hg)
    (hwf.wk ρ) (hwg.wk ρ) hfg'

/-- Weakening of `ConvNeUp` (`wk~↑`). -/
theorem wkConvNeUp {Γ Δ : Context} {t u A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (d : ConvNeUp Γ t u A) :
    ConvNeUp Δ (wk ρ t) (wk ρ u) (wk ρ A) :=
  (ConvNeUp.rec
    (motive_1 := fun Γ t u A _ ↦ WkConvNeUpMotive Γ t u A)
    (motive_2 := fun Γ t u A _ ↦ WkConvNeDownMotive Γ t u A)
    (motive_3 := fun Γ A B _ ↦ WkConvTypeUpMotive Γ A B)
    (motive_4 := fun Γ A B _ ↦ WkConvTypeDownMotive Γ A B)
    (motive_5 := fun Γ t u A _ ↦ WkConvTermUpMotive Γ t u A)
    (motive_6 := fun Γ t u A _ ↦ WkConvTermDownMotive Γ t u A)
    (fun hx hxy ↦ wkConv_var_case hx hxy)
    (fun hkl htv ihkl ihtv ↦ wkConv_app_case hkl htv ihkl ihtv)
    (fun hFG hab hhg hkl ihFG ihab ihhg ihkl ↦
      wkConv_natrec_case hFG hab hhg hkl ihFG ihab ihhg ihkl)
    (fun D hw hkl ihkl ↦ wkConv_neDown_case D hw hkl ihkl)
    (fun DA DB hwA hwB hAB ihAB ↦ wkConv_typeUp_case DA DB hwA hwB hAB ihAB)
    (fun hΓ ↦ wkConv_univRefl_case hΓ)
    (fun hΓ ↦ wkConv_natRefl_case hΓ)
    (fun hKL ihKL ↦ wkConv_neType_case hKL ihKL)
    (fun hF hFH hGE ihFH ihGE ↦ wkConv_piCong_case hF hFH hGE ihFH ihGE)
    (fun DA dt du hwB hwt hwu htu ihtu ↦
      wkConv_termUp_case DA dt du hwB hwt hwu htu ihtu)
    (fun hkl ihkl ↦ wkConv_natIns_case hkl ihkl)
    (fun hk hl neN hkl ihkl ↦ wkConv_neIns_case hk hl neN hkl ihkl)
    (fun hA hB hAB ihAB ↦ wkConv_univ_case hA hB hAB ihAB)
    (fun hΓ ↦ wkConv_zeroRefl_case hΓ)
    (fun hmn ihmn ↦ wkConv_succCong_case hmn ihmn)
    (fun hF hf hg hwf hwg hfg ihfg ↦ wkConv_etaEq_case hF hf hg hwf hwg hfg ihfg)
    d) hρ hΔ

/-- Weakening of `ConvNeDown` (`wk~↓`). -/
theorem wkConvNeDown {Γ Δ : Context} {t u A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) :
    ConvNeDown Γ t u A → ConvNeDown Δ (wk ρ t) (wk ρ u) (wk ρ A)
  | .mk D hw hkl => .mk (wkTypeStar hρ hΔ D) (hw.wk ρ) (wkConvNeUp hρ hΔ hkl)

/-- Weakening of `ConvTypeDown` (`wkConv↓`). -/
theorem wkConvTypeDown {Γ Δ : Context} {A B : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (d : ConvTypeDown Γ A B) :
    ConvTypeDown Δ (wk ρ A) (wk ρ B) :=
  (ConvTypeDown.rec
    (motive_1 := fun Γ t u A _ ↦ WkConvNeUpMotive Γ t u A)
    (motive_2 := fun Γ t u A _ ↦ WkConvNeDownMotive Γ t u A)
    (motive_3 := fun Γ A B _ ↦ WkConvTypeUpMotive Γ A B)
    (motive_4 := fun Γ A B _ ↦ WkConvTypeDownMotive Γ A B)
    (motive_5 := fun Γ t u A _ ↦ WkConvTermUpMotive Γ t u A)
    (motive_6 := fun Γ t u A _ ↦ WkConvTermDownMotive Γ t u A)
    (fun hx hxy ↦ wkConv_var_case hx hxy)
    (fun hkl htv ihkl ihtv ↦ wkConv_app_case hkl htv ihkl ihtv)
    (fun hFG hab hhg hkl ihFG ihab ihhg ihkl ↦
      wkConv_natrec_case hFG hab hhg hkl ihFG ihab ihhg ihkl)
    (fun D hw hkl ihkl ↦ wkConv_neDown_case D hw hkl ihkl)
    (fun DA DB hwA hwB hAB ihAB ↦ wkConv_typeUp_case DA DB hwA hwB hAB ihAB)
    (fun hΓ ↦ wkConv_univRefl_case hΓ)
    (fun hΓ ↦ wkConv_natRefl_case hΓ)
    (fun hKL ihKL ↦ wkConv_neType_case hKL ihKL)
    (fun hF hFH hGE ihFH ihGE ↦ wkConv_piCong_case hF hFH hGE ihFH ihGE)
    (fun DA dt du hwB hwt hwu htu ihtu ↦
      wkConv_termUp_case DA dt du hwB hwt hwu htu ihtu)
    (fun hkl ihkl ↦ wkConv_natIns_case hkl ihkl)
    (fun hk hl neN hkl ihkl ↦ wkConv_neIns_case hk hl neN hkl ihkl)
    (fun hA hB hAB ihAB ↦ wkConv_univ_case hA hB hAB ihAB)
    (fun hΓ ↦ wkConv_zeroRefl_case hΓ)
    (fun hmn ihmn ↦ wkConv_succCong_case hmn ihmn)
    (fun hF hf hg hwf hwg hfg ihfg ↦ wkConv_etaEq_case hF hf hg hwf hwg hfg ihfg)
    d) hρ hΔ

/-- Weakening of `ConvTypeUp` (`wkConv↑`). -/
theorem wkConvTypeUp {Γ Δ : Context} {A B : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) :
    ConvTypeUp Γ A B → ConvTypeUp Δ (wk ρ A) (wk ρ B)
  | .mk DA DB hwA hwB hAB =>
      .mk (wkTypeStar hρ hΔ DA) (wkTypeStar hρ hΔ DB)
        (hwA.wk ρ) (hwB.wk ρ) (wkConvTypeDown hρ hΔ hAB)

/-- Weakening of `ConvTermDown` (`wkConv↓Term`). -/
theorem wkConvTermDown {Γ Δ : Context} {t u A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (d : ConvTermDown Γ t u A) :
    ConvTermDown Δ (wk ρ t) (wk ρ u) (wk ρ A) :=
  (ConvTermDown.rec
    (motive_1 := fun Γ t u A _ ↦ WkConvNeUpMotive Γ t u A)
    (motive_2 := fun Γ t u A _ ↦ WkConvNeDownMotive Γ t u A)
    (motive_3 := fun Γ A B _ ↦ WkConvTypeUpMotive Γ A B)
    (motive_4 := fun Γ A B _ ↦ WkConvTypeDownMotive Γ A B)
    (motive_5 := fun Γ t u A _ ↦ WkConvTermUpMotive Γ t u A)
    (motive_6 := fun Γ t u A _ ↦ WkConvTermDownMotive Γ t u A)
    (fun hx hxy ↦ wkConv_var_case hx hxy)
    (fun hkl htv ihkl ihtv ↦ wkConv_app_case hkl htv ihkl ihtv)
    (fun hFG hab hhg hkl ihFG ihab ihhg ihkl ↦
      wkConv_natrec_case hFG hab hhg hkl ihFG ihab ihhg ihkl)
    (fun D hw hkl ihkl ↦ wkConv_neDown_case D hw hkl ihkl)
    (fun DA DB hwA hwB hAB ihAB ↦ wkConv_typeUp_case DA DB hwA hwB hAB ihAB)
    (fun hΓ ↦ wkConv_univRefl_case hΓ)
    (fun hΓ ↦ wkConv_natRefl_case hΓ)
    (fun hKL ihKL ↦ wkConv_neType_case hKL ihKL)
    (fun hF hFH hGE ihFH ihGE ↦ wkConv_piCong_case hF hFH hGE ihFH ihGE)
    (fun DA dt du hwB hwt hwu htu ihtu ↦
      wkConv_termUp_case DA dt du hwB hwt hwu htu ihtu)
    (fun hkl ihkl ↦ wkConv_natIns_case hkl ihkl)
    (fun hk hl neN hkl ihkl ↦ wkConv_neIns_case hk hl neN hkl ihkl)
    (fun hA hB hAB ihAB ↦ wkConv_univ_case hA hB hAB ihAB)
    (fun hΓ ↦ wkConv_zeroRefl_case hΓ)
    (fun hmn ihmn ↦ wkConv_succCong_case hmn ihmn)
    (fun hF hf hg hwf hwg hfg ihfg ↦ wkConv_etaEq_case hF hf hg hwf hwg hfg ihfg)
    d) hρ hΔ

/-- Weakening of `ConvTermUp` (`wkConv↑Term`). -/
theorem wkConvTermUp {Γ Δ : Context} {t u A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) :
    ConvTermUp Γ t u A → ConvTermUp Δ (wk ρ t) (wk ρ u) (wk ρ A)
  | .mk DA dt du hwB hwt hwu htu =>
      .mk (wkTypeStar hρ hΔ DA) (wkStar hρ hΔ dt) (wkStar hρ hΔ du)
        (hwB.wk ρ) (hwt.wk ρ) (hwu.wk ρ) (wkConvTermDown hρ hΔ htu)

/-!
## Executable Adequacy and Fuel Monotonicity for `Algorithm.lean`
-/

/-- `neutralHead` characterizes `Neutral` exactly. -/
theorem neutralHead_iff_Neutral : ∀ t : Term, neutralHead t = true ↔ Neutral t
  | .univ => ⟨fun h ↦ (by cases h), fun h ↦ (by cases h)⟩
  | .pi _ _ => ⟨fun h ↦ (by cases h), fun h ↦ (by cases h)⟩
  | .nat => ⟨fun h ↦ (by cases h), fun h ↦ (by cases h)⟩
  | .var x => ⟨fun _ ↦ .var x, fun _ ↦ rfl⟩
  | .lam _ => ⟨fun h ↦ (by cases h), fun h ↦ (by cases h)⟩
  | .app k _ => by
      dsimp [neutralHead]
      constructor
      · intro h
        exact .app ((neutralHead_iff_Neutral k).mp h)
      · intro h
        cases h with
        | app hk => exact (neutralHead_iff_Neutral k).mpr hk
  | .zero => ⟨fun h ↦ (by cases h), fun h ↦ (by cases h)⟩
  | .succ _ => ⟨fun h ↦ (by cases h), fun h ↦ (by cases h)⟩
  | .natrec _ _ _ k => by
      dsimp [neutralHead]
      constructor
      · intro h
        exact .natrec ((neutralHead_iff_Neutral k).mp h)
      · intro h
        cases h with
        | natrec hk => exact (neutralHead_iff_Neutral k).mpr hk

/-- `lookupType` characterizes `Member` exactly. -/
theorem lookupType_iff_Member :
    ∀ (Γ : Context) (x : Nat) (A : Term), lookupType Γ x = some A ↔ Member x A Γ
  | [], _, _ => ⟨fun h ↦ (by cases h), fun h ↦ (by cases h)⟩
  | B :: _, 0, A => by
      dsimp [lookupType]
      constructor
      · intro h
        cases h
        exact .here
      · intro h
        cases h
        rfl
  | B :: Γ, x + 1, A => by
      dsimp [lookupType]
      constructor
      · intro h
        cases h' : lookupType Γ x with
        | none => rw [h'] at h; cases h
        | some A₀ =>
            rw [h'] at h
            cases h
            exact .there ((lookupType_iff_Member Γ x A₀).mp h')
      · intro h
        cases h with
        | @there _ A₀ _ _ hm =>
            have h' := (lookupType_iff_Member Γ x A₀).mpr hm
            rw [h']
            rfl

theorem lookupType_hasType {Γ : Context} {x : Nat} {A : Term}
    (hΓ : CtxWf Γ) (hl : lookupType Γ x = some A) : HasType Γ (.var x) A :=
  .var hΓ ((lookupType_iff_Member Γ x A).mp hl)

/-- Every successful result of `whnfFuel` is in `Whnf`. -/
theorem whnfFuel_whnf : ∀ {fuel : Nat} {t u : Term},
    whnfFuel fuel t = some u → Whnf u
  | 0, _, _, h => by cases h
  | fuel + 1, .univ, u, h => by cases h; exact .univ
  | fuel + 1, .pi _ _, u, h => by cases h; exact .pi
  | fuel + 1, .nat, u, h => by cases h; exact .nat
  | fuel + 1, .var x, u, h => by cases h; exact .neutral (.var x)
  | fuel + 1, .lam _, u, h => by cases h; exact .lam
  | fuel + 1, .zero, u, h => by cases h; exact .zero
  | fuel + 1, .succ _, u, h => by cases h; exact .succ
  | fuel + 1, .app f a, u, h => by
      dsimp [whnfFuel] at h
      cases hf : whnfFuel fuel f with
      | none => rw [hf] at h; cases h
      | some f' =>
          rw [hf] at h
          dsimp [Bind.bind, Option.bind] at h
          cases f' with
          | lam body => exact whnfFuel_whnf h
          | univ | pi _ _ | nat | zero | succ _ =>
              dsimp [neutralHead] at h
              cases h
          | var x =>
              dsimp [neutralHead] at h
              cases h
              exact .neutral (.app (.var x))
          | app k v =>
              by_cases hne : neutralHead (Term.app k v) = true
              · rw [if_pos hne] at h
                cases h
                exact .neutral (.app ((neutralHead_iff_Neutral _).mp hne))
              · rw [if_neg hne] at h
                cases h
          | natrec C z s k =>
              by_cases hne : neutralHead (Term.natrec C z s k) = true
              · rw [if_pos hne] at h
                cases h
                exact .neutral (.app ((neutralHead_iff_Neutral _).mp hne))
              · rw [if_neg hne] at h
                cases h
  | fuel + 1, .natrec A z s n, u, h => by
      dsimp [whnfFuel] at h
      cases hn : whnfFuel fuel n with
      | none => rw [hn] at h; cases h
      | some n' =>
          rw [hn] at h
          dsimp [Bind.bind, Option.bind] at h
          cases n' with
          | zero => exact whnfFuel_whnf h
          | succ k => exact whnfFuel_whnf h
          | univ | pi _ _ | nat | lam _ =>
              dsimp [neutralHead] at h
              cases h
          | var x =>
              dsimp [neutralHead] at h
              cases h
              exact .neutral (.natrec (.var x))
          | app k v =>
              by_cases hne : neutralHead (Term.app k v) = true
              · rw [if_pos hne] at h
                cases h
                exact .neutral (.natrec ((neutralHead_iff_Neutral _).mp hne))
              · rw [if_neg hne] at h
                cases h
          | natrec C z' s' k =>
              by_cases hne : neutralHead (Term.natrec C z' s' k) = true
              · rw [if_pos hne] at h
                cases h
                exact .neutral (.natrec ((neutralHead_iff_Neutral _).mp hne))
              · rw [if_neg hne] at h
                cases h

/-- Fuel monotonicity for `whnfFuel`: increasing fuel preserves any successful result. -/
theorem whnfFuel_mono : ∀ {f₁ f₂ : Nat} {t u : Term},
    f₁ ≤ f₂ → whnfFuel f₁ t = some u → whnfFuel f₂ t = some u
  | 0, _, _, _, _, h => by cases h
  | _ + 1, 0, _, _, hle, _ => by cases hle
  | f₁ + 1, f₂ + 1, .univ, _, _, h => h
  | f₁ + 1, f₂ + 1, .pi _ _, _, _, h => h
  | f₁ + 1, f₂ + 1, .nat, _, _, h => h
  | f₁ + 1, f₂ + 1, .var _, _, _, h => h
  | f₁ + 1, f₂ + 1, .lam _, _, _, h => h
  | f₁ + 1, f₂ + 1, .zero, _, _, h => h
  | f₁ + 1, f₂ + 1, .succ _, _, _, h => h
  | f₁ + 1, f₂ + 1, .app f a, u, hle, h => by
      have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
      dsimp [whnfFuel] at h ⊢
      cases hf : whnfFuel f₁ f with
      | none => rw [hf] at h; cases h
      | some f' =>
          rw [hf] at h
          rw [whnfFuel_mono hle' hf]
          dsimp [Bind.bind, Option.bind] at h ⊢
          cases f' with
          | lam body => exact whnfFuel_mono hle' h
          | _ => exact h
  | f₁ + 1, f₂ + 1, .natrec A z s n, u, hle, h => by
      have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
      dsimp [whnfFuel] at h ⊢
      cases hn : whnfFuel f₁ n with
      | none => rw [hn] at h; cases h
      | some n' =>
          rw [hn] at h
          rw [whnfFuel_mono hle' hn]
          dsimp [Bind.bind, Option.bind] at h ⊢
          cases n' with
          | zero => exact whnfFuel_mono hle' h
          | succ k => exact whnfFuel_mono hle' h
          | _ => exact h

/-- Every neutral term evaluates to itself under `whnfFuel` once fuel equals at least its spine depth. -/
theorem whnfFuel_of_Neutral {t : Term} (hn : Neutral t) :
    ∃ fuel, ∀ f, fuel ≤ f → whnfFuel f t = some t := by
  induction hn with
  | var x =>
      refine ⟨1, fun f hf ↦ ?_⟩
      cases f with
      | zero => cases hf
      | succ f => rfl
  | @app k u hk ih =>
      rcases ih with ⟨f₀, ih⟩
      refine ⟨f₀ + 1, fun f hf ↦ ?_⟩
      cases f with
      | zero => cases hf
      | succ f =>
          have hle : f₀ ≤ f := Nat.le_of_succ_le_succ hf
          dsimp [whnfFuel]
          rw [ih f hle]
          dsimp [Bind.bind, Option.bind]
          have hne : neutralHead k = true := (neutralHead_iff_Neutral k).mpr hk
          cases hk with
          | var _ => rfl
          | app _ => simp [hne]
          | natrec _ => simp [hne]
  | @natrec C z s k hk ih =>
      rcases ih with ⟨f₀, ih⟩
      refine ⟨f₀ + 1, fun f hf ↦ ?_⟩
      cases f with
      | zero => cases hf
      | succ f =>
          have hle : f₀ ≤ f := Nat.le_of_succ_le_succ hf
          dsimp [whnfFuel]
          rw [ih f hle]
          dsimp [Bind.bind, Option.bind]
          have hne : neutralHead k = true := (neutralHead_iff_Neutral k).mpr hk
          cases hk with
          | var _ => rfl
          | app _ => simp [hne]
          | natrec _ => simp [hne]

/-- Every WHNF term evaluates to itself under `whnfFuel` for sufficiently large fuel. -/
theorem whnfFuel_of_Whnf {t : Term} (hw : Whnf t) :
    ∃ fuel, ∀ f, fuel ≤ f → whnfFuel f t = some t := by
  cases hw with
  | univ | pi | nat | lam | zero | succ =>
      refine ⟨1, fun f hf ↦ ?_⟩
      cases f with
      | zero => cases hf
      | succ _ => rfl
  | neutral hn => exact whnfFuel_of_Neutral hn

/-- Single-step typed reduction is simulated backwards by `whnfFuel`. -/
theorem whnfFuel_step {Γ : Context} {t t' u A : Term} {fuel : Nat}
    (d : Step Γ t t' A) (hu : whnfFuel fuel t' = some u) :
    whnfFuel (fuel + 1) t = some u := by
  induction d generalizing u fuel with
  | conv _ _ ih => exact ih hu
  | @app _ _ f f' a _ _ ih =>
      cases fuel with
      | zero => cases hu
      | succ f₀ =>
          dsimp [whnfFuel] at hu
          cases hf' : whnfFuel f₀ f' with
          | none => rw [hf'] at hu; cases hu
          | some w =>
              rw [hf'] at hu
              have hf : whnfFuel (f₀ + 1) f = some w := ih hf'
              dsimp [whnfFuel]
              rw [hf]
              dsimp [Bind.bind, Option.bind] at hu ⊢
              cases w with
              | lam body => exact whnfFuel_mono (Nat.le_succ f₀) hu
              | _ => exact hu
  | @beta _ _ a body _ _ _ =>
      dsimp [whnfFuel]
      cases fuel with
      | zero => cases hu
      | succ f₀ =>
          have hbody : whnfFuel (f₀ + 1) (.lam body) = some (.lam body) := rfl
          rw [hbody]
          dsimp [Bind.bind, Option.bind]
          exact hu
  | @natrec z s n n' F _ _ _ _ ih =>
      cases fuel with
      | zero => cases hu
      | succ f₀ =>
          dsimp [whnfFuel] at hu
          cases hn' : whnfFuel f₀ n' with
          | none => rw [hn'] at hu; cases hu
          | some w =>
              rw [hn'] at hu
              have hn : whnfFuel (f₀ + 1) n = some w := ih hn'
              dsimp [whnfFuel]
              rw [hn]
              dsimp [Bind.bind, Option.bind] at hu ⊢
              cases w with
              | zero => exact whnfFuel_mono (Nat.le_succ f₀) hu
              | succ k => exact whnfFuel_mono (Nat.le_succ f₀) hu
              | _ => exact hu
  | @natrecZero z s F _ _ _ =>
      dsimp [whnfFuel]
      cases fuel with
      | zero => cases hu
      | succ f₀ =>
          have hzero : whnfFuel (f₀ + 1) .zero = some .zero := rfl
          rw [hzero]
          dsimp [Bind.bind, Option.bind]
          exact hu
  | @natrecSucc n z s F _ _ _ _ =>
      dsimp [whnfFuel]
      cases fuel with
      | zero => cases hu
      | succ f₀ =>
          have hsucc : whnfFuel (f₀ + 1) (.succ n) = some (.succ n) := rfl
          rw [hsucc]
          dsimp [Bind.bind, Option.bind]
          exact hu

/-- Multi-step typed term reduction to WHNF (`TermWhnf`) is computed by `whnfFuel`. -/
theorem whnfFuel_of_TermWhnf {Γ : Context} {t u A : Term} (h : TermWhnf Γ t u A) :
    ∃ fuel, ∀ f, fuel ≤ f → whnfFuel f t = some u := by
  rcases h with ⟨dStar, hwu⟩
  induction dStar with
  | refl _ => exact whnfFuel_of_Whnf hwu
  | step hStep _ ih =>
      rcases ih hwu with ⟨f₀, ih⟩
      refine ⟨f₀ + 1, fun f hf ↦ ?_⟩
      cases f with
      | zero => cases hf
      | succ f =>
          have hle : f₀ ≤ f := Nat.le_of_succ_le_succ hf
          exact whnfFuel_step hStep (ih f hle)

/-- Multi-step typed type reduction to WHNF (`TypeWhnf`) is computed by `whnfFuel`. -/
theorem whnfFuel_of_TypeWhnf {Γ : Context} {A B : Term} (h : TypeWhnf Γ A B) :
    ∃ fuel, ∀ f, fuel ≤ f → whnfFuel f A = some B := by
  rcases h with ⟨dStar, hwB⟩
  induction dStar with
  | refl _ => exact whnfFuel_of_Whnf hwB
  | step hStep _ ih =>
      cases hStep with
      | fromUniv hStepTerm =>
          rcases ih hwB with ⟨f₀, ih⟩
          refine ⟨f₀ + 1, fun f hf ↦ ?_⟩
          cases f with
          | zero => cases hf
          | succ f =>
              have hle : f₀ ≤ f := Nat.le_of_succ_le_succ hf
              exact whnfFuel_step hStepTerm (ih f hle)

/-- Combined fuel monotonicity for all six comparison functions in `Algorithm.lean`. -/
theorem compare_mono_bundle :
    ∀ f₁ : Nat,
      (∀ {f₂ : Nat} {Γ : Context} {k l : Term} {res : Option Term},
        f₁ ≤ f₂ → compareNeutralUp f₁ Γ k l = some res → compareNeutralUp f₂ Γ k l = some res) ∧
      (∀ {f₂ : Nat} {Γ : Context} {k l : Term} {res : Option Term},
        f₁ ≤ f₂ → compareNeutralDown f₁ Γ k l = some res → compareNeutralDown f₂ Γ k l = some res) ∧
      (∀ {f₂ : Nat} {Γ : Context} {A B : Term} {b : Bool},
        f₁ ≤ f₂ → compareTypeUp f₁ Γ A B = some b → compareTypeUp f₂ Γ A B = some b) ∧
      (∀ {f₂ : Nat} {Γ : Context} {A B : Term} {b : Bool},
        f₁ ≤ f₂ → compareTypeDown f₁ Γ A B = some b → compareTypeDown f₂ Γ A B = some b) ∧
      (∀ {f₂ : Nat} {Γ : Context} {t u A : Term} {b : Bool},
        f₁ ≤ f₂ → compareTermUp f₁ Γ t u A = some b → compareTermUp f₂ Γ t u A = some b) ∧
      (∀ {f₂ : Nat} {Γ : Context} {t u A : Term} {b : Bool},
        f₁ ≤ f₂ → compareTermDown f₁ Γ t u A = some b → compareTermDown f₂ Γ t u A = some b)
  | 0 =>
      ⟨fun _ h ↦ (by cases h),
       fun _ h ↦ (by cases h),
       fun _ h ↦ (by cases h),
       fun _ h ↦ (by cases h),
       fun _ h ↦ (by cases h),
       fun _ h ↦ (by cases h)⟩
  | f₁ + 1 =>
      let ⟨ihNeUp, ihNeDown, ihTyUp, ihTyDown, ihTmUp, ihTmDown⟩ := compare_mono_bundle f₁
      ⟨-- compareNeutralUp
       fun {f₂ Γ k l res} hle h ↦ by
         cases f₂ with
         | zero => cases hle
         | succ f₂ =>
             have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
             cases k <;> cases l <;> try exact h
             case app k t l v =>
               dsimp [compareNeutralUp] at h ⊢
               cases hinf : compareNeutralDown f₁ Γ k l with
               | none => rw [hinf] at h; cases h
               | some inf =>
                   rw [hinf] at h
                   rw [ihNeDown hle' hinf]
                   dsimp [Bind.bind, Option.bind] at h ⊢
                   cases inf with
                   | none => exact h
                   | some T =>
                       cases T with
                       | pi F G =>
                           dsimp at h ⊢
                           cases heq : compareTermUp f₁ Γ t v F with
                           | none => rw [heq] at h; cases h
                           | some b =>
                               rw [heq] at h
                               rw [ihTmUp hle' heq]
                               exact h
                       | _ => exact h
             case natrec F a₀ h₀ k G b₀ g₀ l =>
               dsimp [compareNeutralUp] at h ⊢
               cases hm : compareTypeUp f₁ (.nat :: Γ) F G with
               | none => rw [hm] at h; cases h
               | some bm =>
                   rw [hm] at h
                   rw [ihTyUp hle' hm]
                   dsimp [Bind.bind, Option.bind] at h ⊢
                   cases bm with
                   | false => exact h
                   | true =>
                       dsimp at h ⊢
                       cases hb : compareTermUp f₁ Γ a₀ b₀ (subst0 F .zero) with
                       | none => rw [hb] at h; cases h
                       | some bb =>
                           rw [hb] at h
                           rw [ihTmUp hle' hb]
                           dsimp [Bind.bind, Option.bind] at h ⊢
                           cases bb with
                           | false => exact h
                           | true =>
                               dsimp at h ⊢
                               cases hs : compareTermUp f₁ Γ h₀ g₀ (recStepType F) with
                               | none => rw [hs] at h; cases h
                               | some bs =>
                                   rw [hs] at h
                                   rw [ihTmUp hle' hs]
                                   dsimp [Bind.bind, Option.bind] at h ⊢
                                   cases bs with
                                   | false => exact h
                                   | true =>
                                       dsimp at h ⊢
                                       cases hi : compareNeutralDown f₁ Γ k l with
                                       | none => rw [hi] at h; cases h
                                       | some inf =>
                                           rw [hi] at h
                                           rw [ihNeDown hle' hi]
                                           exact h,
       -- compareNeutralDown
       fun {f₂ Γ k l res} hle h ↦ by
         cases f₂ with
         | zero => cases hle
         | succ f₂ =>
             have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
             dsimp [compareNeutralDown] at h ⊢
             cases hi : compareNeutralUp f₁ Γ k l with
             | none => rw [hi] at h; cases h
             | some inf =>
                 rw [hi] at h
                 rw [ihNeUp hle' hi]
                 dsimp [Bind.bind, Option.bind] at h ⊢
                 cases inf with
                 | none => exact h
                 | some A =>
                     dsimp at h ⊢
                     cases hw : whnfFuel f₁ A with
                     | none => rw [hw] at h; cases h
                     | some B =>
                         rw [hw] at h
                         rw [whnfFuel_mono hle' hw]
                         exact h,
       -- compareTypeUp
       fun {f₂ Γ A B b} hle h ↦ by
         cases f₂ with
         | zero => cases hle
         | succ f₂ =>
             have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
             dsimp [compareTypeUp] at h ⊢
             cases hA : whnfFuel f₁ A with
             | none => rw [hA] at h; cases h
             | some A' =>
                 rw [hA] at h
                 rw [whnfFuel_mono hle' hA]
                 dsimp [Bind.bind, Option.bind] at h ⊢
                 cases hB : whnfFuel f₁ B with
                 | none => rw [hB] at h; cases h
                 | some B' =>
                     rw [hB] at h
                     rw [whnfFuel_mono hle' hB]
                     dsimp [Bind.bind, Option.bind] at h ⊢
                     exact ihTyDown hle' h,
       -- compareTypeDown
       fun {f₂ Γ A B b} hle h ↦ by
         cases f₂ with
         | zero => cases hle
         | succ f₂ =>
             have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
             have hNeCase :
                 (if neutralHead A && neutralHead B then do
                   let inferred ← compareNeutralDown f₁ Γ A B
                   match inferred with
                   | some .univ => some true
                   | _ => some false
                 else some false) = some b →
                 (if neutralHead A && neutralHead B then do
                   let inferred ← compareNeutralDown f₂ Γ A B
                   match inferred with
                   | some .univ => some true
                   | _ => some false
                 else some false) = some b := by
               intro hne
               by_cases hcond : (neutralHead A && neutralHead B) = true
               · rw [if_pos hcond] at hne ⊢
                 cases hi : compareNeutralDown f₁ Γ A B with
                 | none => rw [hi] at hne; cases hne
                 | some inf =>
                     rw [hi] at hne
                     rw [ihNeDown hle' hi]
                     exact hne
               · rw [if_neg hcond] at hne ⊢
                 exact hne
             cases A <;> cases B <;> try exact hNeCase h
             case univ.univ => exact h
             case nat.nat => exact h
             case pi.pi F G H E =>
               dsimp [compareTypeDown] at h ⊢
               cases hd : compareTypeUp f₁ Γ F H with
               | none => rw [hd] at h; cases h
               | some bd =>
                   rw [hd] at h
                   rw [ihTyUp hle' hd]
                   dsimp [Bind.bind, Option.bind] at h ⊢
                   cases bd with
                   | false => exact h
                   | true =>
                       dsimp at h ⊢
                       exact ihTyUp hle' h,
       -- compareTermUp
       fun {f₂ Γ t u A b} hle h ↦ by
         cases f₂ with
         | zero => cases hle
         | succ f₂ =>
             have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
             dsimp [compareTermUp] at h ⊢
             cases hB : whnfFuel f₁ A with
             | none => rw [hB] at h; cases h
             | some B =>
                 rw [hB] at h
                 rw [whnfFuel_mono hle' hB]
                 dsimp [Bind.bind, Option.bind] at h ⊢
                 cases ht : whnfFuel f₁ t with
                 | none => rw [ht] at h; cases h
                 | some t' =>
                     rw [ht] at h
                     rw [whnfFuel_mono hle' ht]
                     dsimp [Bind.bind, Option.bind] at h ⊢
                     cases hu : whnfFuel f₁ u with
                     | none => rw [hu] at h; cases h
                     | some u' =>
                         rw [hu] at h
                         rw [whnfFuel_mono hle' hu]
                         dsimp [Bind.bind, Option.bind] at h ⊢
                         exact ihTmDown hle' h,
       -- compareTermDown
       fun {f₂ Γ t u A b} hle h ↦ by
         cases f₂ with
         | zero => cases hle
         | succ f₂ =>
             have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
             have hNeInsCase :
                 (if neutralHead A && neutralHead t && neutralHead u then do
                   let inferred ← compareNeutralDown f₁ Γ t u
                   some inferred.isSome
                 else some false) = some b →
                 (if neutralHead A && neutralHead t && neutralHead u then do
                   let inferred ← compareNeutralDown f₂ Γ t u
                   some inferred.isSome
                 else some false) = some b := by
               intro hne
               by_cases hcond : (neutralHead A && neutralHead t && neutralHead u) = true
               · rw [if_pos hcond] at hne ⊢
                 cases hi : compareNeutralDown f₁ Γ t u with
                 | none => rw [hi] at hne; cases hne
                 | some inf =>
                     rw [hi] at hne
                     rw [ihNeDown hle' hi]
                     exact hne
               · rw [if_neg hcond] at hne ⊢
                 exact hne
             cases A with
             | univ =>
                 dsimp [compareTermDown] at h ⊢
                 exact ihTyDown hle' h
             | pi F G =>
                 dsimp [compareTermDown] at h ⊢
                 exact ihTmUp hle' h
             | nat =>
                 have hNatNeCase :
                     (if neutralHead t && neutralHead u then do
                       let inferred ← compareNeutralDown f₁ Γ t u
                       match inferred with
                       | some .nat => some true
                       | _ => some false
                     else some false) = some b →
                     (if neutralHead t && neutralHead u then do
                       let inferred ← compareNeutralDown f₂ Γ t u
                       match inferred with
                       | some .nat => some true
                       | _ => some false
                     else some false) = some b := by
                   intro hne
                   by_cases hcond : (neutralHead t && neutralHead u) = true
                   · rw [if_pos hcond] at hne ⊢
                     cases hi : compareNeutralDown f₁ Γ t u with
                     | none => rw [hi] at hne; cases hne
                     | some inf =>
                         rw [hi] at hne
                         rw [ihNeDown hle' hi]
                         exact hne
                   · rw [if_neg hcond] at hne ⊢
                     exact hne
                 cases t <;> cases u <;> try exact hNatNeCase h
                 case zero.zero => exact h
                 case succ.succ m n =>
                   dsimp [compareTermDown] at h ⊢
                   exact ihTmUp hle' h
             | var _ | app _ _ | natrec _ _ _ _ | lam _ | zero | succ _ =>
                 exact hNeInsCase h⟩

theorem compareNeutralUp_mono {f₁ f₂ : Nat} {Γ : Context} {k l : Term} {res : Option Term}
    (hle : f₁ ≤ f₂) (h : compareNeutralUp f₁ Γ k l = some res) :
    compareNeutralUp f₂ Γ k l = some res :=
  (compare_mono_bundle f₁).1 hle h

theorem compareNeutralDown_mono {f₁ f₂ : Nat} {Γ : Context} {k l : Term} {res : Option Term}
    (hle : f₁ ≤ f₂) (h : compareNeutralDown f₁ Γ k l = some res) :
    compareNeutralDown f₂ Γ k l = some res :=
  (compare_mono_bundle f₁).2.1 hle h

theorem compareTypeUp_mono {f₁ f₂ : Nat} {Γ : Context} {A B : Term} {b : Bool}
    (hle : f₁ ≤ f₂) (h : compareTypeUp f₁ Γ A B = some b) :
    compareTypeUp f₂ Γ A B = some b :=
  (compare_mono_bundle f₁).2.2.1 hle h

theorem compareTypeDown_mono {f₁ f₂ : Nat} {Γ : Context} {A B : Term} {b : Bool}
    (hle : f₁ ≤ f₂) (h : compareTypeDown f₁ Γ A B = some b) :
    compareTypeDown f₂ Γ A B = some b :=
  (compare_mono_bundle f₁).2.2.2.1 hle h

theorem compareTermUp_mono {f₁ f₂ : Nat} {Γ : Context} {t u A : Term} {b : Bool}
    (hle : f₁ ≤ f₂) (h : compareTermUp f₁ Γ t u A = some b) :
    compareTermUp f₂ Γ t u A = some b :=
  (compare_mono_bundle f₁).2.2.2.2.1 hle h

theorem compareTermDown_mono {f₁ f₂ : Nat} {Γ : Context} {t u A : Term} {b : Bool}
    (hle : f₁ ≤ f₂) (h : compareTermDown f₁ Γ t u A = some b) :
    compareTermDown f₂ Γ t u A = some b :=
  (compare_mono_bundle f₁).2.2.2.2.2 hle h

/-- Any two successful runs of `compareTypeUp` on the same inputs return the same Boolean. -/
theorem compareTypeUp_unique {f₁ f₂ : Nat} {Γ : Context} {A B : Term} {b₁ b₂ : Bool}
    (h₁ : compareTypeUp f₁ Γ A B = some b₁)
    (h₂ : compareTypeUp f₂ Γ A B = some b₂) : b₁ = b₂ := by
  have hm₁ : compareTypeUp (f₁ + f₂) Γ A B = some b₁ :=
    compareTypeUp_mono (Nat.le_add_right f₁ f₂) h₁
  have hm₂ : compareTypeUp (f₁ + f₂) Γ A B = some b₂ :=
    compareTypeUp_mono (Nat.le_add_left f₂ f₁) h₂
  rw [hm₁] at hm₂
  cases hm₂
  rfl

/-- Any two successful runs of `compareTermUp` on the same inputs return the same Boolean. -/
theorem compareTermUp_unique {f₁ f₂ : Nat} {Γ : Context} {t u A : Term} {b₁ b₂ : Bool}
    (h₁ : compareTermUp f₁ Γ t u A = some b₁)
    (h₂ : compareTermUp f₂ Γ t u A = some b₂) : b₁ = b₂ := by
  have hm₁ : compareTermUp (f₁ + f₂) Γ t u A = some b₁ :=
    compareTermUp_mono (Nat.le_add_right f₁ f₂) h₁
  have hm₂ : compareTermUp (f₁ + f₂) Γ t u A = some b₂ :=
    compareTermUp_mono (Nat.le_add_left f₂ f₁) h₂
  rw [hm₁] at hm₂
  cases hm₂
  rfl

/-- By fuel monotonicity, existence of one correct fuel run implies both convergence and
correctness of every successful run. -/
theorem compareTypeUp_all_runs_correct {Γ : Context} {A B : Term}
    (h : ∃ fuel b, compareTypeUp fuel Γ A B = some b ∧ (b = true ↔ TypeEq Γ A B)) :
    (∃ fuel b, compareTypeUp fuel Γ A B = some b) ∧
    (∀ fuel b, compareTypeUp fuel Γ A B = some b → (b = true ↔ TypeEq Γ A B)) := by
  rcases h with ⟨f₀, b₀, hf₀, hb₀⟩
  refine ⟨⟨f₀, b₀, hf₀⟩, fun f b hf ↦ ?_⟩
  have heq : b = b₀ := compareTypeUp_unique hf hf₀
  subst heq
  exact hb₀

/-- By fuel monotonicity, existence of one correct fuel run implies both convergence and
correctness of every successful run for terms. -/
theorem compareTermUp_all_runs_correct {Γ : Context} {t u A : Term}
    (h : ∃ fuel b, compareTermUp fuel Γ t u A = some b ∧ (b = true ↔ TermEq Γ t u A)) :
    (∃ fuel b, compareTermUp fuel Γ t u A = some b) ∧
    (∀ fuel b, compareTermUp fuel Γ t u A = some b → (b = true ↔ TermEq Γ t u A)) := by
  rcases h with ⟨f₀, b₀, hf₀, hb₀⟩
  refine ⟨⟨f₀, b₀, hf₀⟩, fun f b hf ↦ ?_⟩
  have heq : b = b₀ := compareTermUp_unique hf hf₀
  subst heq
  exact hb₀

end Abel2018

/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/LogicalRelation.agda, Definition/LogicalRelation/ShapeView.agda,
Definition/LogicalRelation/Irrelevance.agda,
Definition/LogicalRelation/Properties/Escape.agda,
Definition/LogicalRelation/Properties/Reflexivity.agda,
Definition/LogicalRelation/Properties/MaybeEmb.agda.
-/

namespace Abel2018

/-!
## Reducibility of Neutrals (`Definition/LogicalRelation.agda` lines 22–80)
-/















/-!
## Reducibility of Natural Numbers (`Definition/LogicalRelation.agda` lines 81–128)
-/









/-- Extraction of `NaturalView` from `NaturalProp` (`natural`). -/
theorem natural_of_NaturalProp {eqrel : EqRelSet} {Γ : Context} {n : Term} :
    NaturalProp eqrel Γ n → NaturalView n
  | .suc _ => .succ
  | .zero => .zero
  | .ne nf => .neutral nf.neK

/-- Extraction of `NaturalView` pair from `NaturalEqProp` (`split`). -/
theorem split_of_NaturalEqProp {eqrel : EqRelSet} {Γ : Context} {a b : Term} :
    NaturalEqProp eqrel Γ a b → NaturalView a ∧ NaturalView b
  | .suc _ => ⟨.succ, .succ⟩
  | .zero => ⟨.zero, .zero⟩
  | .ne nf => ⟨.neutral nf.neK, .neutral nf.neM⟩

/-!
## Type Levels and Logical Relation Bundle (`Definition/LogicalRelation.agda` lines 130–349)
-/

























































/-!
## Smart Constructors for `RedType` and `Π`-types
-/





theorem RedType.U {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context}
    (hU : RedU l Γ) : RedType eqrel l Γ .univ := by
  rcases hU with ⟨l', lt, wf⟩
  exact ⟨_, .U ⟨lt, wf⟩⟩

theorem RedType.nat {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (D : RedNat Γ A) : RedType eqrel l Γ A :=
  ⟨_, .nat D⟩

theorem RedType.ne {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (neA : RedNe eqrel Γ A) : RedType eqrel l Γ A := by
  rcases neA with ⟨K, D, neK, KeqK⟩
  exact ⟨_, .ne (K := K) ⟨D, neK, KeqK⟩⟩

theorem RedType.piAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A F G : Term}
    (piA : RedPiAt eqrel l Γ A F G) : RedType eqrel l Γ A :=
  ⟨_, .pi piA.D piA.hF piA.hG piA.AeqA
    (fun ρ Δ rel ↦ LogRelAt eqrel l Δ (wk ρ F) rel)
    (fun ρ Δ a rel ↦ LogRelAt eqrel l Δ (subst0 (wk (.lift ρ) G) a) rel)
    piA.redF
    (fun _ _ _ h ↦ h)
    piA.redG
    (fun _ _ _ _ h ↦ h)
    piA.Gext⟩

theorem RedType.pi {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (piA : RedPi eqrel l Γ A) : RedType eqrel l Γ A := by
  rcases piA with ⟨F, G, D, hF, hG, AeqA, redF, redG, Gext⟩
  exact RedType.piAt ⟨D, hF, hG, AeqA, redF, redG, Gext⟩

theorem RedType.emb {eqrel : EqRelSet} {l' l : TypeLevel} {Γ : Context} {A : Term}
    (hlt : TypeLevelLT l' l) (hA : RedType eqrel l' Γ A) : RedType eqrel l Γ A := by
  rcases hlt with ⟨⟩
  rcases hA with ⟨rel, hrel⟩
  exact ⟨rel, .emb .zeroLT hrel⟩

/-- Any level can be embedded into level `¹` (`maybeEmb`). -/
theorem maybeEmb {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hA : RedType eqrel l Γ A) : RedType eqrel .one Γ A := by
  cases l with
  | zero => exact RedType.emb .zeroLT hA
  | one => exact hA

/-- Level `⁰` can be embedded into any level `l` (`maybeEmb′`). -/
theorem maybeEmb' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hA : RedType eqrel .zero Γ A) : RedType eqrel l Γ A := by
  cases l with
  | zero => exact hA
  | one => exact RedType.emb .zeroLT hA

/-!
## Irrelevance and Uniqueness of Decoded Relations (`Irrelevance.agda` + `ShapeView.agda`)
-/

/-- Non-embedded characterization of a `LogRelAt` derivation: stripping `.emb` preserves `rel`
and yields one of the four canonical type shapes (`.U`, `.nat`, `.ne`, `.pi`). -/
inductive LogRelShape (eqrel : EqRelSet) : Context → Term → RedRel → Prop where
  | U {l' l : TypeLevel} {Γ : Context} (hU : RedUAt l' l Γ) :
      LogRelShape eqrel Γ .univ (RedURel eqrel (logRelRec eqrel l l' hU.lt) Γ)
  | nat {Γ : Context} {A : Term} (D : RedNat Γ A) :
      LogRelShape eqrel Γ A (RedNatRel eqrel Γ)
  | ne {Γ : Context} {A K : Term} (neA : RedNeAt eqrel Γ A K) :
      LogRelShape eqrel Γ A (RedNeRel eqrel Γ K)
  | pi {l : TypeLevel} {Γ : Context} {A F G : Term}
      (D : TypeStarWf Γ A (.pi F G))
      (hF : TypeWf Γ F)
      (hG : TypeWf (F :: Γ) G)
      (AeqA : eqrel.TypeEqRel Γ (.pi F G) (.pi F G))
      (relF : Wk → Context → RedRel → Prop)
      (relG : Wk → Context → Term → RedRel → Prop)
      (hF_ex : ∀ {ρ Δ}, WkCtx ρ Δ Γ → CtxWf Δ → ∃ rel, relF ρ Δ rel)
      (derivF : ∀ {ρ Δ} (_hρ : WkCtx ρ Δ Γ) (_hΔ : CtxWf Δ) (rel : RedRel),
        relF ρ Δ rel → LogRelAt eqrel l Δ (wk ρ F) rel)
      (hG_ex : ∀ {ρ Δ a}, WkCtx ρ Δ Γ → CtxWf Δ →
        RelFHasTerm relF ρ Δ a → ∃ rel, relG ρ Δ a rel)
      (derivG : ∀ {ρ Δ a} (_hρ : WkCtx ρ Δ Γ) (_hΔ : CtxWf Δ)
        (_ha : RelFHasTerm relF ρ Δ a) (rel : RedRel),
        relG ρ Δ a rel → LogRelAt eqrel l Δ (subst0 (wk (.lift ρ) G) a) rel)
      (Gext : ∀ {ρ Δ a b}, WkCtx ρ Δ Γ → CtxWf Δ →
        RelFHasTerm relF ρ Δ a →
        RelFHasTerm relF ρ Δ b →
        RelFEqTerm relF ρ Δ a b →
        RelGEqType relG ρ Δ a (subst0 (wk (.lift ρ) G) b)) :
      LogRelShape eqrel Γ A (RedPiRel eqrel Γ F G relF relG)

theorem logRelShape_of_LogRelAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    {rel : RedRel} (h : LogRelAt eqrel l Γ A rel) : LogRelShape eqrel Γ A rel := by
  cases h with
  | U hU => exact .U hU
  | nat D => exact .nat D
  | ne neA => exact .ne neA
  | pi D hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext =>
      exact .pi D hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext
  | emb hlt hA =>
      cases hlt
      cases hA with
      | U hU => exact .U hU
      | nat D => exact .nat D
      | ne neA => exact .ne neA
      | pi D hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext =>
          exact .pi D hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext
      | emb hlt' _ => cases hlt'



theorem RedRelEquiv.refl (rel : RedRel) : RedRelEquiv rel rel :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem RedRelEquiv.symm {rel₁ rel₂ : RedRel} (h : RedRelEquiv rel₁ rel₂) :
    RedRelEquiv rel₂ rel₁ :=
  ⟨fun {B} ↦ (h.1 (B := B)).symm,
   fun {t} ↦ (h.2.1 (t := t)).symm,
   fun {t u} ↦ (h.2.2 (t := t) (u := u)).symm⟩

theorem RedRelEquiv.trans {rel₁ rel₂ rel₃ : RedRel}
    (h₁₂ : RedRelEquiv rel₁ rel₂) (h₂₃ : RedRelEquiv rel₂ rel₃) :
    RedRelEquiv rel₁ rel₃ :=
  ⟨fun {B} ↦ (h₁₂.1 (B := B)).trans (h₂₃.1 (B := B)),
   fun {t} ↦ (h₁₂.2.1 (t := t)).trans (h₂₃.2.1 (t := t)),
   fun {t u} ↦ (h₁₂.2.2 (t := t) (u := u)).trans (h₂₃.2.2 (t := t) (u := u))⟩

theorem logRelRec_eq {eqrel : EqRelSet} {l₁ l₂ l₁' l₂' : TypeLevel}
    (lt₁ : TypeLevelLT l₁' l₁) (lt₂ : TypeLevelLT l₂' l₂) :
    logRelRec eqrel l₁ l₁' lt₁ = logRelRec eqrel l₂ l₂' lt₂ := by
  cases lt₁
  cases lt₂
  rfl

/-- Core irrelevance theorem for a single level `l`: any two `RedRel`s derived for the same
type `(Γ, A)` (even at different levels) are equivalent (`RedRelEquiv`). -/
theorem irrelLogRel_step {eqrel : EqRelSet} {l : TypeLevel}
    {rec : ∀ (l' : TypeLevel), TypeLevelLT l' l → Context → Term → RedRel → Prop}
    (hRecEq : ∀ {l₁ l₂ l₂'} (lt₁ : TypeLevelLT l₁ l) (lt₂ : TypeLevelLT l₂' l₂),
      rec l₁ lt₁ = logRelRec eqrel l₂ l₂' lt₂)
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A rel₁ rel₂},
      rec l' hlt Γ A rel₁ → LogRelShape eqrel Γ A rel₂ → RedRelEquiv rel₁ rel₂)
    (_hRecShape : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A rel},
      rec l' hlt Γ A rel → LogRelShape eqrel Γ A rel)
    {Γ : Context} {A : Term} {rel₁ : RedRel}
    (h₁ : LogRel eqrel l rec Γ A rel₁) :
    ∀ {A' : Term} {rel₂ : RedRel}, A = A' → LogRelShape eqrel Γ A' rel₂ → RedRelEquiv rel₁ rel₂ := by
  induction h₁ with
  | @U Γ l₁ hU =>
      intro A' rel₂ hAA' h₂
      subst hAA'
      cases h₂ with
      | U hU₂ =>
          rw [hRecEq hU.lt hU₂.lt]
          exact RedRelEquiv.refl _
      | nat D =>
          have h := whnfRedStar D.reduction .univ
          cases h
      | ne neA =>
          have h := whnfRedStar neA.D.reduction .univ
          subst h
          cases neA.neK
      | pi D =>
          have h := whnfRedStar D.reduction .univ
          cases h
  | @nat Γ A D₁ =>
      intro A' rel₂ hAA' h₂
      subst hAA'
      cases h₂ with
      | U _ =>
          have h := whnfRedStar D₁.reduction .univ
          cases h
      | nat _ => exact RedRelEquiv.refl _
      | ne neB =>
          have h := whrDetStar ⟨D₁.reduction, .nat⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ =>
          have h := whrDetStar ⟨D₁.reduction, .nat⟩ ⟨D₂.reduction, .pi⟩
          cases h
  | @ne Γ A K₁ neA =>
      intro A' rel₂ hAA' h₂
      subst hAA'
      cases h₂ with
      | U _ =>
          have h := whnfRedStar neA.D.reduction .univ
          subst h
          cases neA.neK
      | nat D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .nat⟩ ⟨neA.D.reduction, .neutral neA.neK⟩
          subst h
          cases neA.neK
      | @ne _ _ K₂ neB =>
          have hK : K₁ = K₂ :=
            whrDetStar ⟨neA.D.reduction, .neutral neA.neK⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          rw [hK]
          exact RedRelEquiv.refl _
      | pi D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .pi⟩ ⟨neA.D.reduction, .neutral neA.neK⟩
          subst h
          cases neA.neK
  | @pi Γ A F₁ G₁ D₁ _hF₁ _hG₁ _AeqA₁ relF₁ relG₁ hF_ex₁ _derivF₁ hG_ex₁ _derivG₁ _Gext₁ ihF ihG =>
      intro A' rel₂ hAA' h₂
      subst hAA'
      cases h₂ with
      | U _ =>
          have h := whnfRedStar D₁.reduction .univ
          cases h
      | nat D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D₁.reduction, .pi⟩
          cases h
      | ne neB =>
          have h := whrDetStar ⟨D₁.reduction, .pi⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | @pi l₂ _ _ F₂ G₂ D₂ _ _ _ relF₂ relG₂ hF_ex₂ derivF₂ hG_ex₂ derivG₂ _ =>
          have hPi : Term.pi F₁ G₁ = Term.pi F₂ G₂ :=
            whrDetStar ⟨D₁.reduction, .pi⟩ ⟨D₂.reduction, .pi⟩
          injection hPi with hF₁₂ hG₁₂
          subst hF₁₂ hG₁₂
          have hFeqType : ∀ {ρ Δ B} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ),
              RelFEqType relF₁ ρ Δ B ↔ RelFEqType relF₂ ρ Δ B := by
            intro ρ Δ B hρ hΔ
            constructor
            · rintro ⟨r₁, hr₁, hB⟩
              rcases hF_ex₂ hρ hΔ with ⟨r₂, hr₂⟩
              have heq := ihF hρ hΔ r₁ hr₁ rfl (logRelShape_of_LogRelAt (derivF₂ hρ hΔ r₂ hr₂))
              exact ⟨r₂, hr₂, heq.1.mp hB⟩
            · rintro ⟨r₂, hr₂, hB⟩
              rcases hF_ex₁ hρ hΔ with ⟨r₁, hr₁⟩
              have heq := ihF hρ hΔ r₁ hr₁ rfl (logRelShape_of_LogRelAt (derivF₂ hρ hΔ r₂ hr₂))
              exact ⟨r₁, hr₁, heq.1.mpr hB⟩
          have hFhasTerm : ∀ {ρ Δ a} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ),
              RelFHasTerm relF₁ ρ Δ a ↔ RelFHasTerm relF₂ ρ Δ a := by
            intro ρ Δ a hρ hΔ
            constructor
            · rintro ⟨r₁, hr₁, ha⟩
              rcases hF_ex₂ hρ hΔ with ⟨r₂, hr₂⟩
              have heq := ihF hρ hΔ r₁ hr₁ rfl (logRelShape_of_LogRelAt (derivF₂ hρ hΔ r₂ hr₂))
              exact ⟨r₂, hr₂, heq.2.1.mp ha⟩
            · rintro ⟨r₂, hr₂, ha⟩
              rcases hF_ex₁ hρ hΔ with ⟨r₁, hr₁⟩
              have heq := ihF hρ hΔ r₁ hr₁ rfl (logRelShape_of_LogRelAt (derivF₂ hρ hΔ r₂ hr₂))
              exact ⟨r₁, hr₁, heq.2.1.mpr ha⟩
          have hFeqTerm : ∀ {ρ Δ a b} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ),
              RelFEqTerm relF₁ ρ Δ a b ↔ RelFEqTerm relF₂ ρ Δ a b := by
            intro ρ Δ a b hρ hΔ
            constructor
            · rintro ⟨r₁, hr₁, hab⟩
              rcases hF_ex₂ hρ hΔ with ⟨r₂, hr₂⟩
              have heq := ihF hρ hΔ r₁ hr₁ rfl (logRelShape_of_LogRelAt (derivF₂ hρ hΔ r₂ hr₂))
              exact ⟨r₂, hr₂, heq.2.2.mp hab⟩
            · rintro ⟨r₂, hr₂, hab⟩
              rcases hF_ex₁ hρ hΔ with ⟨r₁, hr₁⟩
              have heq := ihF hρ hΔ r₁ hr₁ rfl (logRelShape_of_LogRelAt (derivF₂ hρ hΔ r₂ hr₂))
              exact ⟨r₁, hr₁, heq.2.2.mpr hab⟩
          have hGeqType : ∀ {ρ Δ a B} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ)
              (ha₁ : RelFHasTerm relF₁ ρ Δ a),
              RelGEqType relG₁ ρ Δ a B ↔ RelGEqType relG₂ ρ Δ a B := by
            intro ρ Δ a B hρ hΔ ha₁
            have ha₂ : RelFHasTerm relF₂ ρ Δ a := (hFhasTerm hρ hΔ).mp ha₁
            constructor
            · rintro ⟨s₁, hs₁, hB⟩
              rcases hG_ex₂ hρ hΔ ha₂ with ⟨s₂, hs₂⟩
              have heq := ihG hρ hΔ ha₁ s₁ hs₁ rfl
                (logRelShape_of_LogRelAt (derivG₂ hρ hΔ ha₂ s₂ hs₂))
              exact ⟨s₂, hs₂, heq.1.mp hB⟩
            · rintro ⟨s₂, hs₂, hB⟩
              rcases hG_ex₁ hρ hΔ ha₁ with ⟨s₁, hs₁⟩
              have heq := ihG hρ hΔ ha₁ s₁ hs₁ rfl
                (logRelShape_of_LogRelAt (derivG₂ hρ hΔ ha₂ s₂ hs₂))
              exact ⟨s₁, hs₁, heq.1.mpr hB⟩
          have hGhasTerm : ∀ {ρ Δ a t} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ)
              (ha₁ : RelFHasTerm relF₁ ρ Δ a),
              RelGHasTerm relG₁ ρ Δ a t ↔ RelGHasTerm relG₂ ρ Δ a t := by
            intro ρ Δ a t hρ hΔ ha₁
            have ha₂ : RelFHasTerm relF₂ ρ Δ a := (hFhasTerm hρ hΔ).mp ha₁
            constructor
            · rintro ⟨s₁, hs₁, ht⟩
              rcases hG_ex₂ hρ hΔ ha₂ with ⟨s₂, hs₂⟩
              have heq := ihG hρ hΔ ha₁ s₁ hs₁ rfl
                (logRelShape_of_LogRelAt (derivG₂ hρ hΔ ha₂ s₂ hs₂))
              exact ⟨s₂, hs₂, heq.2.1.mp ht⟩
            · rintro ⟨s₂, hs₂, ht⟩
              rcases hG_ex₁ hρ hΔ ha₁ with ⟨s₁, hs₁⟩
              have heq := ihG hρ hΔ ha₁ s₁ hs₁ rfl
                (logRelShape_of_LogRelAt (derivG₂ hρ hΔ ha₂ s₂ hs₂))
              exact ⟨s₁, hs₁, heq.2.1.mpr ht⟩
          have hGeqTerm : ∀ {ρ Δ a t u} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ)
              (ha₁ : RelFHasTerm relF₁ ρ Δ a),
              RelGEqTerm relG₁ ρ Δ a t u ↔ RelGEqTerm relG₂ ρ Δ a t u := by
            intro ρ Δ a t u hρ hΔ ha₁
            have ha₂ : RelFHasTerm relF₂ ρ Δ a := (hFhasTerm hρ hΔ).mp ha₁
            constructor
            · rintro ⟨s₁, hs₁, htu⟩
              rcases hG_ex₂ hρ hΔ ha₂ with ⟨s₂, hs₂⟩
              have heq := ihG hρ hΔ ha₁ s₁ hs₁ rfl
                (logRelShape_of_LogRelAt (derivG₂ hρ hΔ ha₂ s₂ hs₂))
              exact ⟨s₂, hs₂, heq.2.2.mp htu⟩
            · rintro ⟨s₂, hs₂, htu⟩
              rcases hG_ex₁ hρ hΔ ha₁ with ⟨s₁, hs₁⟩
              have heq := ihG hρ hΔ ha₁ s₁ hs₁ rfl
                (logRelShape_of_LogRelAt (derivG₂ hρ hΔ ha₂ s₂ hs₂))
              exact ⟨s₁, hs₁, heq.2.2.mpr htu⟩
          have hPiTermIff : ∀ {t},
              RedPiTerm eqrel Γ F₁ G₁ relF₁ relG₁ t ↔ RedPiTerm eqrel Γ F₁ G₁ relF₂ relG₂ t := by
            intro t
            constructor
            · rintro ⟨f, d, funcF, feqf, appEq, appTerm⟩
              refine ⟨f, d, funcF, feqf, ?_, ?_⟩
              · intro ρ Δ a b hρ hΔ ha₂ hb₂ hab₂
                have ha₁ := (hFhasTerm hρ hΔ).mpr ha₂
                have hb₁ := (hFhasTerm hρ hΔ).mpr hb₂
                have hab₁ := (hFeqTerm hρ hΔ).mpr hab₂
                exact (hGeqTerm hρ hΔ ha₁).mp (appEq hρ hΔ ha₁ hb₁ hab₁)
              · intro ρ Δ a hρ hΔ ha₂
                have ha₁ := (hFhasTerm hρ hΔ).mpr ha₂
                exact (hGhasTerm hρ hΔ ha₁).mp (appTerm hρ hΔ ha₁)
            · rintro ⟨f, d, funcF, feqf, appEq, appTerm⟩
              refine ⟨f, d, funcF, feqf, ?_, ?_⟩
              · intro ρ Δ a b hρ hΔ ha₁ hb₁ hab₁
                have ha₂ := (hFhasTerm hρ hΔ).mp ha₁
                have hb₂ := (hFhasTerm hρ hΔ).mp hb₁
                have hab₂ := (hFeqTerm hρ hΔ).mp hab₁
                exact (hGeqTerm hρ hΔ ha₁).mpr (appEq hρ hΔ ha₂ hb₂ hab₂)
              · intro ρ Δ a hρ hΔ ha₁
                have ha₂ := (hFhasTerm hρ hΔ).mp ha₁
                exact (hGhasTerm hρ hΔ ha₁).mpr (appTerm hρ hΔ ha₂)
          refine ⟨?_, hPiTermIff, ?_⟩
          · intro B
            constructor
            · rintro ⟨F', G', D', AeqB, FeqF', GeqG'⟩
              refine ⟨F', G', D', AeqB,
                fun hρ hΔ ↦ (hFeqType hρ hΔ).mp (FeqF' hρ hΔ),
                fun hρ hΔ ha₂ ↦ ?_⟩
              have ha₁ := (hFhasTerm hρ hΔ).mpr ha₂
              exact (hGeqType hρ hΔ ha₁).mp (GeqG' hρ hΔ ha₁)
            · rintro ⟨F', G', D', AeqB, FeqF', GeqG'⟩
              refine ⟨F', G', D', AeqB,
                fun hρ hΔ ↦ (hFeqType hρ hΔ).mpr (FeqF' hρ hΔ),
                fun hρ hΔ ha₁ ↦ ?_⟩
              have ha₂ := (hFhasTerm hρ hΔ).mp ha₁
              exact (hGeqType hρ hΔ ha₁).mpr (GeqG' hρ hΔ ha₂)
          · intro t u
            constructor
            · rintro ⟨f, g, d, d', funcF, funcG, feqg, ht, hu, appEq⟩
              refine ⟨f, g, d, d', funcF, funcG, feqg,
                hPiTermIff.mp ht, hPiTermIff.mp hu, fun hρ hΔ ha₂ ↦ ?_⟩
              have ha₁ := (hFhasTerm hρ hΔ).mpr ha₂
              exact (hGeqTerm hρ hΔ ha₁).mp (appEq hρ hΔ ha₁)
            · rintro ⟨f, g, d, d', funcF, funcG, feqg, ht, hu, appEq⟩
              refine ⟨f, g, d, d', funcF, funcG, feqg,
                hPiTermIff.mpr ht, hPiTermIff.mpr hu, fun hρ hΔ ha₁ ↦ ?_⟩
              have ha₂ := (hFhasTerm hρ hΔ).mp ha₁
              exact (hGeqTerm hρ hΔ ha₁).mpr (appEq hρ hΔ ha₂)
  | @emb Γ A l' rel hlt hA =>
      intro A' rel₂ hAA' h₂
      subst hAA'
      exact ihRec l' hlt hA h₂

/-- Full irrelevance theorem across all levels `l₁, l₂`: any two `RedRel`s derived for the same
type `(Γ, A)` are equivalent (`RedRelEquiv`). -/
theorem irrelLogRel {eqrel : EqRelSet} {l₁ l₂ : TypeLevel} {Γ : Context} {A : Term}
    {rel₁ rel₂ : RedRel}
    (h₁ : LogRelAt eqrel l₁ Γ A rel₁)
    (h₂ : LogRelAt eqrel l₂ Γ A rel₂) :
    RedRelEquiv rel₁ rel₂ := by
  have h0 : ∀ {Γ A rel₁ rel₂},
      LogRelAt eqrel .zero Γ A rel₁ → LogRelShape eqrel Γ A rel₂ → RedRelEquiv rel₁ rel₂ :=
    fun h₁ h₂s ↦ irrelLogRel_step (l := .zero) (rec := logRelRec eqrel .zero)
      (fun lt₁ _ ↦ nomatch lt₁)
      (fun _ hlt ↦ nomatch hlt)
      (fun _ hlt ↦ nomatch hlt)
      h₁ rfl h₂s
  cases l₁ with
  | zero => exact h0 h₁ (logRelShape_of_LogRelAt h₂)
  | one =>
      exact irrelLogRel_step (l := .one) (rec := logRelRec eqrel .one)
        (fun lt₁ lt₂ ↦ logRelRec_eq lt₁ lt₂)
        (fun _ hlt _ _ _ _ h₁' h₂s ↦ by cases hlt; exact h0 h₁' h₂s)
        (fun _ hlt _ _ _ h₁' ↦ by cases hlt; exact logRelShape_of_LogRelAt h₁')
        h₁ rfl (logRelShape_of_LogRelAt h₂)

/-!
## Irrelevance Corollaries (`Definition/LogicalRelation/Irrelevance.agda`)
-/

/-- Irrelevance for propositionally equal types (`irrelevance′`). -/
theorem irrelevance' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A A' : Term}
    (h : A = A') (p : RedType eqrel l Γ A) : RedType eqrel l Γ A' :=
  h ▸ p

/-- Irrelevance for propositionally equal contexts and types (`irrelevanceΓ′`). -/
theorem irrelevanceΓ' {eqrel : EqRelSet} {l : TypeLevel} {Γ Γ' : Context} {A A' : Term}
    (hΓ : Γ = Γ') (hA : A = A') (p : RedType eqrel l Γ A) : RedType eqrel l Γ' A' := by
  subst hΓ hA
  exact p

/-- Irrelevance for reducible type equality (`irrelevanceEq`). -/
theorem irrelevanceEq {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A B : Term}
    (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ A)
    (hAB : RedEq p B) : RedEq q B := by
  rcases hAB with ⟨rel₁, h₁, hB⟩
  rcases q with ⟨rel₂, h₂⟩
  exact ⟨rel₂, h₂, (irrelLogRel h₁ h₂).1.mp hB⟩

/-- Irrelevance for reducible type equality with equal left types (`irrelevanceEq′`). -/
theorem irrelevanceEq' {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A A' B : Term}
    (hA : A = A') (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ A')
    (hAB : RedEq p B) : RedEq q B := by
  subst hA
  exact irrelevanceEq p q hAB

/-- Irrelevance for reducible type equality with equal left and right types (`irrelevanceEq″`). -/
theorem irrelevanceEq'' {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A A' B B' : Term}
    (hA : A = A') (hB : B = B') (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ A')
    (hAB : RedEq p B) : RedEq q B' := by
  subst hA hB
  exact irrelevanceEq p q hAB

/-- Irrelevance for reducible type equality with equal right types (`irrelevanceEqR′`). -/
theorem irrelevanceEqR' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B B' : Term}
    (hB : B = B') (p : RedType eqrel l Γ A) (hAB : RedEq p B) : RedEq p B' :=
  hB ▸ hAB

/-- Irrelevance for reducible terms (`irrelevanceTerm`). -/
theorem irrelevanceTerm {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A t : Term}
    (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ A)
    (ht : RedTerm p t) : RedTerm q t := by
  rcases ht with ⟨rel₁, h₁, ht⟩
  rcases q with ⟨rel₂, h₂⟩
  exact ⟨rel₂, h₂, (irrelLogRel h₁ h₂).2.1.mp ht⟩

/-- Irrelevance for reducible terms with equal types (`irrelevanceTerm′`). -/
theorem irrelevanceTerm' {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A A' t : Term}
    (hA : A = A') (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ A')
    (ht : RedTerm p t) : RedTerm q t := by
  subst hA
  exact irrelevanceTerm p q ht

/-- Irrelevance for reducible terms with equal types and terms (`irrelevanceTerm″`). -/
theorem irrelevanceTerm'' {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A A' t t' : Term}
    (hA : A = A') (htEq : t = t') (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ A')
    (ht : RedTerm p t) : RedTerm q t' := by
  subst hA htEq
  exact irrelevanceTerm p q ht

/-- Irrelevance for reducible terms with equal contexts, types, and terms (`irrelevanceTermΓ″`). -/
theorem irrelevanceTermΓ'' {eqrel : EqRelSet} {l l' : TypeLevel} {Γ Γ' : Context} {A A' t t' : Term}
    (hΓ : Γ = Γ') (hA : A = A') (htEq : t = t')
    (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ' A')
    (ht : RedTerm p t) : RedTerm q t' := by
  subst hΓ hA htEq
  exact irrelevanceTerm p q ht

/-- Irrelevance for reducible term equality (`irrelevanceEqTerm`). -/
theorem irrelevanceEqTerm {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A t u : Term}
    (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ A)
    (htu : RedTermEq p t u) : RedTermEq q t u := by
  rcases htu with ⟨rel₁, h₁, htu⟩
  rcases q with ⟨rel₂, h₂⟩
  exact ⟨rel₂, h₂, (irrelLogRel h₁ h₂).2.2.mp htu⟩

/-- Irrelevance for reducible term equality with equal types (`irrelevanceEqTerm′`). -/
theorem irrelevanceEqTerm' {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A A' t u : Term}
    (hA : A = A') (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ A')
    (htu : RedTermEq p t u) : RedTermEq q t u := by
  subst hA
  exact irrelevanceEqTerm p q htu

/-- Irrelevance for reducible term equality with equal terms and types (`irrelevanceEqTerm″`). -/
theorem irrelevanceEqTerm'' {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context}
    {A A' t t' u u' : Term}
    (htEq : t = t') (huEq : u = u') (hA : A = A')
    (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ A')
    (htu : RedTermEq p t u) : RedTermEq q t' u' := by
  subst htEq huEq hA
  exact irrelevanceEqTerm p q htu

/-!
## Constructor-Specific Characterizations of `RedEq`, `RedTerm`, `RedTermEq`
-/

theorem RedEq_of_LogRelAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B : Term}
    {rel : RedRel} (h : LogRelAt eqrel l Γ A rel) (p : RedType eqrel l Γ A) :
    RedEq p B ↔ rel.eqType B := by
  constructor
  · rintro ⟨rel', h', hB⟩
    exact (irrelLogRel h' h).1.mp hB
  · intro hB
    exact ⟨rel, h, hB⟩

theorem RedTerm_of_LogRelAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t : Term}
    {rel : RedRel} (h : LogRelAt eqrel l Γ A rel) (p : RedType eqrel l Γ A) :
    RedTerm p t ↔ rel.hasTerm t := by
  constructor
  · rintro ⟨rel', h', ht⟩
    exact (irrelLogRel h' h).2.1.mp ht
  · intro ht
    exact ⟨rel, h, ht⟩

theorem RedTermEq_of_LogRelAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t u : Term}
    {rel : RedRel} (h : LogRelAt eqrel l Γ A rel) (p : RedType eqrel l Γ A) :
    RedTermEq p t u ↔ rel.eqTerm t u := by
  constructor
  · rintro ⟨rel', h', htu⟩
    exact (irrelLogRel h' h).2.2.mp htu
  · intro htu
    exact ⟨rel, h, htu⟩

/-!
## Escape Lemmas (`Definition/LogicalRelation/Properties/Escape.agda`)
-/

/-- Reducible types are syntactically well-formed (`escape`). -/
theorem escape {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (p : RedType eqrel l Γ A) : TypeWf Γ A := by
  rcases p with ⟨rel, h⟩
  cases logRelShape_of_LogRelAt h with
  | U hU => exact .univ hU.wf
  | nat D => exact D.source
  | ne neA => exact neA.D.source
  | pi D => exact D.source

/-- Reducible type equality implies `eqrel.TypeEqRel` (`escapeEq`). -/
theorem escapeEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B : Term}
    (p : RedType eqrel l Γ A) (hAB : RedEq p B) : eqrel.TypeEqRel Γ A B := by
  rcases hAB with ⟨rel, h, hB⟩
  cases logRelShape_of_LogRelAt h with
  | U hU =>
      change B = .univ at hB
      subst hB
      exact eqrel.univRefl hU.wf
  | nat D =>
      change TypeStar Γ B .nat at hB
      exact eqrel.redType D.reduction hB .nat .nat (eqrel.natRefl (wfType D.source))
  | ne neA =>
      rcases hB with ⟨M, D', neM, KeqM⟩
      exact eqrel.redType neA.D.reduction D'.reduction (.neutral neA.neK) (.neutral neM)
        (eqrel.neToType KeqM)
  | pi D _ _ _ _ _ _ _ _ _ _ =>
      rcases hB with ⟨F', G', D', AeqB, _, _⟩
      exact eqrel.redType D.reduction D' .pi .pi AeqB

/-- Reducible terms are syntactically well-typed (`escapeTerm`). -/
theorem escapeTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t : Term}
    (p : RedType eqrel l Γ A) (ht : RedTerm p t) : HasType Γ t A := by
  rcases ht with ⟨rel, h, ht⟩
  cases logRelShape_of_LogRelAt h with
  | U _ =>
      rcases ht with ⟨_, d, _, _, _⟩
      exact d.source
  | nat D =>
      rcases ht with ⟨_, _, d, _, _⟩
      exact .conv d.source (.symm (subsetStar D.reduction))
  | ne neA =>
      rcases ht with ⟨_, d, _⟩
      exact .conv d.source (.symm (subsetStar neA.D.reduction))
  | pi D _ _ _ _ _ _ _ _ _ _ =>
      rcases ht with ⟨_, d, _, _, _, _⟩
      exact .conv d.source (.symm (subsetStar D.reduction))

/-- Reducible term equality implies `eqrel.TermEqRel` (`escapeTermEq`). -/
theorem escapeTermEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t u : Term}
    (p : RedType eqrel l Γ A) (htu : RedTermEq p t u) : eqrel.TermEqRel Γ t u A := by
  rcases htu with ⟨rel, h, htu⟩
  cases logRelShape_of_LogRelAt h with
  | U hU =>
      rcases htu with ⟨A₀, B₀, d, d', typeA, typeB, AeqB, _, _, _, _⟩
      exact eqrel.redTerm (.refl (.univ hU.wf)) d.reduction d'.reduction
        .univ typeA.toWhnf typeB.toWhnf AeqB
  | nat D =>
      rcases htu with ⟨_, _, k, k', d, d', keqk', prop⟩
      have ⟨natK, natK'⟩ := split_of_NaturalEqProp prop
      exact eqrel.redTerm D.reduction d.reduction d'.reduction .nat natK.toWhnf natK'.toWhnf keqk'
  | ne neA =>
      rcases htu with ⟨k, m, d, d', nf⟩
      exact eqrel.redTerm neA.D.reduction d.reduction d'.reduction
        (.neutral neA.neK) (.neutral nf.neK) (.neutral nf.neM)
        (eqrel.neToTerm nf.keqm)
  | pi D _ _ _ _ _ _ _ _ _ _ =>
      rcases htu with ⟨f, g, d, d', funcF, funcG, feqg, _, _, _⟩
      exact eqrel.redTerm D.reduction d.reduction d'.reduction
        .pi funcF.toWhnf funcG.toWhnf feqg

/-!
## Shape Elimination Lemmas (`Definition/LogicalRelation/ShapeView.agda` lines 58–108)
-/

/-- Elimination for `U` (`U-elim`). -/
theorem elimU {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context}
    (p : RedType eqrel l Γ .univ) : RedU .one Γ := by
  rcases p with ⟨rel, h⟩
  cases logRelShape_of_LogRelAt h with
  | U hU =>
      cases hU with
      | mk lt wf =>
          cases lt
          exact ⟨.zero, .zeroLT, wf⟩
  | nat D =>
      have h := whnfRedStar D.reduction .univ
      cases h
  | ne neA =>
      have h := whnfRedStar neA.D.reduction .univ
      subst h
      cases neA.neK
  | pi D =>
      have h := whnfRedStar D.reduction .univ
      cases h

/-- Elimination for `ℕ` (`ℕ-elim′`). -/
theorem elimNat' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (D : TypeStar Γ A .nat) (p : RedType eqrel l Γ A) : RedNat Γ A := by
  rcases p with ⟨rel, h⟩
  cases logRelShape_of_LogRelAt h with
  | U _ =>
      have h := whnfRedStar D .univ
      cases h
  | nat D' => exact D'
  | ne neA =>
      have h := whrDetStar ⟨D, .nat⟩ ⟨neA.D.reduction, .neutral neA.neK⟩
      subst h
      cases neA.neK
  | pi D' =>
      have h := whrDetStar ⟨D, .nat⟩ ⟨D'.reduction, .pi⟩
      cases h

theorem elimNat {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context}
    (p : RedType eqrel l Γ .nat) : RedNat Γ .nat :=
  elimNat' (.refl (escape p)) p

/-- Elimination for neutral types with explicit WHNF `K` (`ne-elim′`). -/
theorem elimNeAt' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A K : Term}
    (D : TypeStar Γ A K) (neK : Neutral K) (p : RedType eqrel l Γ A) : RedNeAt eqrel Γ A K := by
  rcases p with ⟨rel, h⟩
  cases logRelShape_of_LogRelAt h with
  | U _ =>
      have h := whnfRedStar D .univ
      subst h
      cases neK
  | nat D' =>
      have h := whrDetStar ⟨D'.reduction, .nat⟩ ⟨D, .neutral neK⟩
      subst h
      cases neK
  | @ne _ _ K₀ neA =>
      have hK : K₀ = K :=
        whrDetStar ⟨neA.D.reduction, .neutral neA.neK⟩ ⟨D, .neutral neK⟩
      subst hK
      exact neA
  | pi D' =>
      have h := whrDetStar ⟨D'.reduction, .pi⟩ ⟨D, .neutral neK⟩
      subst h
      cases neK

/-- Elimination for neutral types (`ne-elim′`). -/
theorem elimNe' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A K : Term}
    (D : TypeStar Γ A K) (neK : Neutral K) (p : RedType eqrel l Γ A) : RedNe eqrel Γ A := by
  have neA := elimNeAt' D neK p
  exact ⟨K, neA.D, neA.neK, neA.KeqK⟩

theorem elimNe {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {K : Term}
    (neK : Neutral K) (p : RedType eqrel l Γ K) : RedNe eqrel Γ K :=
  elimNe' (.refl (escape p)) neK p

/-- Elimination for `Π`-types with explicit domain `F` and codomain `G` (`Π-elim′`). -/
theorem elimPiAt' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A F G : Term}
    (D : TypeStar Γ A (.pi F G)) (p : RedType eqrel l Γ A) :
    ∃ l₀, RedPiAt eqrel l₀ Γ A F G := by
  rcases p with ⟨rel, h⟩
  cases logRelShape_of_LogRelAt h with
  | U _ =>
      have h := whnfRedStar D .univ
      cases h
  | nat D' =>
      have h := whrDetStar ⟨D'.reduction, .nat⟩ ⟨D, .pi⟩
      cases h
  | ne neA =>
      have h := whrDetStar ⟨D, .pi⟩ ⟨neA.D.reduction, .neutral neA.neK⟩
      subst h
      cases neA.neK
  | @pi l₀ _ _ F₀ G₀ D' hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext =>
      have hPi : Term.pi F₀ G₀ = Term.pi F G :=
        whrDetStar ⟨D'.reduction, .pi⟩ ⟨D, .pi⟩
      injection hPi with hF₀ hG₀
      subst hF₀ hG₀
      refine ⟨l₀, ⟨D', hF, hG, AeqA, ?_, ?_, ?_⟩⟩
      · intro ρ Δ hρ hΔ
        rcases hF_ex hρ hΔ with ⟨r, hr⟩
        exact ⟨r, derivF hρ hΔ r hr⟩
      · intro ρ Δ a hρ hΔ ha
        have ha' : RelFHasTerm relF ρ Δ a := by
          rcases hF_ex hρ hΔ with ⟨r, hr⟩
          have hrAt := derivF hρ hΔ r hr
          exact ⟨r, hr, (RedTerm_of_LogRelAt hrAt _).mp ha⟩
        rcases hG_ex hρ hΔ ha' with ⟨s, hs⟩
        exact ⟨s, derivG hρ hΔ ha' s hs⟩
      · intro ρ Δ a b hρ hΔ ha hb hab
        have ha' : RelFHasTerm relF ρ Δ a := by
          rcases hF_ex hρ hΔ with ⟨r, hr⟩
          exact ⟨r, hr, (RedTerm_of_LogRelAt (derivF hρ hΔ r hr) _).mp ha⟩
        have hb' : RelFHasTerm relF ρ Δ b := by
          rcases hF_ex hρ hΔ with ⟨r, hr⟩
          exact ⟨r, hr, (RedTerm_of_LogRelAt (derivF hρ hΔ r hr) _).mp hb⟩
        have hab' : RelFEqTerm relF ρ Δ a b := by
          rcases hF_ex hρ hΔ with ⟨r, hr⟩
          exact ⟨r, hr, (RedTermEq_of_LogRelAt (derivF hρ hΔ r hr) _).mp hab⟩
        rcases Gext hρ hΔ ha' hb' hab' with ⟨s, hs, hB⟩
        exact ⟨s, derivG hρ hΔ ha' s hs, hB⟩

/-- Elimination for `Π`-types (`Π-elim′`). -/
theorem elimPi' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A F G : Term}
    (D : TypeStar Γ A (.pi F G)) (p : RedType eqrel l Γ A) :
    ∃ l₀, RedPi eqrel l₀ Γ A := by
  rcases elimPiAt' D p with ⟨l₀, piA⟩
  exact ⟨l₀, ⟨F, G, piA.D, piA.hF, piA.hG, piA.AeqA, piA.redF, piA.redG, piA.Gext⟩⟩

theorem elimPi {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G : Term}
    (p : RedType eqrel l Γ (.pi F G)) : ∃ l₀, RedPi eqrel l₀ Γ (.pi F G) :=
  elimPi' (.refl (escape p)) p

/-!
## Reflexivity (`Definition/LogicalRelation/Properties/Reflexivity.agda`)
-/

/-- Reflexivity of `NaturalProp` (`reflNatural-prop`). -/
theorem reflNaturalProp {eqrel : EqRelSet} {Γ : Context} {n : Term}
    (h : NaturalProp eqrel Γ n) : NaturalEqProp eqrel Γ n n :=
  @NaturalProp.rec eqrel Γ
    (fun t _ ↦ RedNatTermEq eqrel Γ t t)
    (fun n _ ↦ NaturalEqProp eqrel Γ n n)
    (fun t n d neqn _ ih ↦ .mk t t n n d d neqn ih)
    (fun _ ih ↦ .suc ih)
    .zero
    (fun nf ↦ .ne ⟨nf.neK, nf.neK, nf.keqk⟩)
    n h

theorem reflLogRel_step {eqrel : EqRelSet} {l : TypeLevel}
    {rec : ∀ (l' : TypeLevel), TypeLevelLT l' l → Context → Term → RedRel → Prop}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A rel},
      rec l' hlt Γ A rel → rel.eqType A ∧ (∀ {t}, rel.hasTerm t → rel.eqTerm t t))
    {Γ : Context} {A : Term} {rel : RedRel}
    (h : LogRel eqrel l rec Γ A rel) :
    rel.eqType A ∧ (∀ {t}, rel.hasTerm t → rel.eqTerm t t) := by
  induction h with
  | @U _ l' hU =>
      refine ⟨rfl, ?_⟩
      rintro t ⟨A₀, d, typeA, AeqA, relt, ht⟩
      have ⟨hReflEq, _⟩ := ihRec l' hU.lt ht
      exact ⟨A₀, A₀, d, d, typeA, typeA, AeqA, relt, ht, ⟨relt, ht⟩, hReflEq⟩
  | nat D =>
      refine ⟨D.reduction, ?_⟩
      rintro t ⟨_, n, d, neqn, prop⟩
      exact .mk t t n n d d neqn (reflNaturalProp prop)
  | @ne _ _ K neA =>
      refine ⟨⟨K, neA.D, neA.neK, neA.KeqK⟩, ?_⟩
      rintro t ⟨k, d, nf⟩
      exact ⟨k, k, d, d, ⟨nf.neK, nf.neK, nf.keqk⟩⟩
  | @pi Γ A F G D _hF _hG AeqA relF relG hF_ex _derivF hG_ex _derivG _Gext ihF ihG =>
      refine ⟨⟨F, G, D.reduction, AeqA, ?_, ?_⟩, ?_⟩
      · intro ρ Δ hρ hΔ
        rcases hF_ex hρ hΔ with ⟨r, hr⟩
        exact ⟨r, hr, (ihF hρ hΔ r hr).1⟩
      · intro ρ Δ a hρ hΔ ha
        rcases hG_ex hρ hΔ ha with ⟨s, hs⟩
        exact ⟨s, hs, (ihG hρ hΔ ha s hs).1⟩
      · rintro t ht
        rcases ht with ⟨f, d, funcF, feqf, appEq, appTerm⟩
        refine ⟨f, f, d, d, funcF, funcF, feqf,
          ⟨f, d, funcF, feqf, appEq, appTerm⟩,
          ⟨f, d, funcF, feqf, appEq, appTerm⟩, ?_⟩
        intro ρ Δ a hρ hΔ ha
        have haa : RelFEqTerm relF ρ Δ a a := by
          rcases ha with ⟨r, hr, ha'⟩
          exact ⟨r, hr, (ihF hρ hΔ r hr).2 ha'⟩
        exact appEq hρ hΔ ha ha haa
  | @emb _ _ l' _ hlt hA => exact ihRec l' hlt hA

theorem reflLogRelAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term} {rel : RedRel}
    (h : LogRelAt eqrel l Γ A rel) :
    rel.eqType A ∧ (∀ {t}, rel.hasTerm t → rel.eqTerm t t) := by
  have h0 : ∀ {Γ A rel},
      LogRelAt eqrel .zero Γ A rel → rel.eqType A ∧ (∀ {t}, rel.hasTerm t → rel.eqTerm t t) :=
    fun h ↦ reflLogRel_step (l := .zero) (rec := logRelRec eqrel .zero) (fun _ hlt ↦ nomatch hlt) h
  cases l with
  | zero => exact h0 h
  | one =>
      exact reflLogRel_step (l := .one) (rec := logRelRec eqrel .one)
        (fun _ hlt _ _ _ h' ↦ by cases hlt; exact h0 h') h

/-- Reflexivity of reducible type equality (`reflEq`). -/
theorem reflEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (p : RedType eqrel l Γ A) : RedEq p A := by
  rcases p with ⟨rel, h⟩
  exact ⟨rel, h, (reflLogRelAt h).1⟩

/-- Reflexivity of reducible term equality (`reflEqTerm`). -/
theorem reflEqTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t : Term}
    (p : RedType eqrel l Γ A) (ht : RedTerm p t) : RedTermEq p t t := by
  rcases ht with ⟨rel, h, ht⟩
  exact ⟨rel, h, (reflLogRelAt h).2 ht⟩

end Abel2018

/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/LogicalRelation/Weakening.agda,
Definition/LogicalRelation/Properties/Conversion.agda,
Definition/LogicalRelation/Properties/Symmetry.agda,
Definition/LogicalRelation/Properties/Transitivity.agda,
Definition/LogicalRelation/Properties/Universe.agda,
Definition/LogicalRelation/Properties/Neutral.agda,
Definition/LogicalRelation/Properties/Reduction.agda,
Definition/LogicalRelation/Properties/Successor.agda,
Definition/LogicalRelation/Application.agda.
-/

namespace Abel2018

/-!
## Weakening of the Logical Relation (`Definition/LogicalRelation/Weakening.agda`)
-/

theorem wkTermNe {eqrel : EqRelSet} {ρ : Wk} {Γ Δ : Context} {k A : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (nf : RedNeNf eqrel Γ k A) :
    RedNeNf eqrel Δ (wk ρ k) (wk ρ A) :=
  ⟨nf.neK.wk ρ, wkHasType hρ hΔ nf.hk, eqrel.wkNe hρ hΔ nf.keqk⟩

theorem wkEqTermNe {eqrel : EqRelSet} {ρ : Wk} {Γ Δ : Context} {k m A : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (nf : RedNeNfEq eqrel Γ k m A) :
    RedNeNfEq eqrel Δ (wk ρ k) (wk ρ m) (wk ρ A) :=
  ⟨nf.neK.wk ρ, nf.neM.wk ρ, eqrel.wkNe hρ hΔ nf.keqm⟩

theorem wkTermNat {eqrel : EqRelSet} {ρ : Wk} {Γ Δ : Context} {t : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (ht : RedNatTerm eqrel Γ t) :
    RedNatTerm eqrel Δ (wk ρ t) :=
  @RedNatTerm.rec eqrel Γ
    (fun t _ ↦ RedNatTerm eqrel Δ (wk ρ t))
    (fun n _ ↦ NaturalProp eqrel Δ (wk ρ n))
    (fun t n d neqn _ ih ↦
      .mk (wk ρ t) (wk ρ n) (wkStarWf hρ hΔ d) (eqrel.wkTerm hρ hΔ neqn) ih)
    (fun _ ih ↦ .suc ih)
    .zero
    (fun nf ↦ .ne (wkTermNe hρ hΔ nf))
    t ht

theorem wkNaturalProp {eqrel : EqRelSet} {ρ : Wk} {Γ Δ : Context} {n : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (hn : NaturalProp eqrel Γ n) :
    NaturalProp eqrel Δ (wk ρ n) :=
  @NaturalProp.rec eqrel Γ
    (fun t _ ↦ RedNatTerm eqrel Δ (wk ρ t))
    (fun n _ ↦ NaturalProp eqrel Δ (wk ρ n))
    (fun t n d neqn _ ih ↦
      .mk (wk ρ t) (wk ρ n) (wkStarWf hρ hΔ d) (eqrel.wkTerm hρ hΔ neqn) ih)
    (fun _ ih ↦ .suc ih)
    .zero
    (fun nf ↦ .ne (wkTermNe hρ hΔ nf))
    n hn

theorem wkEqTermNat {eqrel : EqRelSet} {ρ : Wk} {Γ Δ : Context} {t u : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (htu : RedNatTermEq eqrel Γ t u) :
    RedNatTermEq eqrel Δ (wk ρ t) (wk ρ u) :=
  @RedNatTermEq.rec eqrel Γ
    (fun t u _ ↦ RedNatTermEq eqrel Δ (wk ρ t) (wk ρ u))
    (fun k k' _ ↦ NaturalEqProp eqrel Δ (wk ρ k) (wk ρ k'))
    (fun t u k k' d d' keqk' _ ih ↦
      .mk (wk ρ t) (wk ρ u) (wk ρ k) (wk ρ k')
        (wkStarWf hρ hΔ d) (wkStarWf hρ hΔ d')
        (eqrel.wkTerm hρ hΔ keqk') ih)
    (fun _ ih ↦ .suc ih)
    .zero
    (fun nf ↦ .ne (wkEqTermNe hρ hΔ nf))
    t u htu

theorem wkNaturalEqProp {eqrel : EqRelSet} {ρ : Wk} {Γ Δ : Context} {k k' : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (hk : NaturalEqProp eqrel Γ k k') :
    NaturalEqProp eqrel Δ (wk ρ k) (wk ρ k') :=
  @NaturalEqProp.rec eqrel Γ
    (fun t u _ ↦ RedNatTermEq eqrel Δ (wk ρ t) (wk ρ u))
    (fun k k' _ ↦ NaturalEqProp eqrel Δ (wk ρ k) (wk ρ k'))
    (fun t u k k' d d' keqk' _ ih ↦
      .mk (wk ρ t) (wk ρ u) (wk ρ k) (wk ρ k')
        (wkStarWf hρ hΔ d) (wkStarWf hρ hΔ d')
        (eqrel.wkTerm hρ hΔ keqk') ih)
    (fun _ ih ↦ .suc ih)
    .zero
    (fun nf ↦ .ne (wkEqTermNe hρ hΔ nf))
    k k' hk

/-- Single-level weakening step for `LogRelAt`. -/
theorem wkLogRel_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {ρ Γ Δ A rel},
      WkCtx ρ Δ Γ → CtxWf Δ →
      logRelRec eqrel l l' hlt Γ A rel →
      ∃ rel', logRelRec eqrel l l' hlt Δ (wk ρ A) rel' ∧
        (∀ {B}, rel.eqType B → rel'.eqType (wk ρ B)) ∧
        (∀ {t}, rel.hasTerm t → rel'.hasTerm (wk ρ t)) ∧
        (∀ {t u}, rel.eqTerm t u → rel'.eqTerm (wk ρ t) (wk ρ u)))
    {Γ : Context} {A : Term} {rel : RedRel}
    (hA : LogRelAt eqrel l Γ A rel) :
    ∀ {ρ : Wk} {Δ : Context}, WkCtx ρ Δ Γ → CtxWf Δ →
      ∃ rel', LogRelAt eqrel l Δ (wk ρ A) rel' ∧
        (∀ {B}, rel.eqType B → rel'.eqType (wk ρ B)) ∧
        (∀ {t}, rel.hasTerm t → rel'.hasTerm (wk ρ t)) ∧
        (∀ {t u}, rel.eqTerm t u → rel'.eqTerm (wk ρ t) (wk ρ u)) := by
  induction hA with
  | @U Γ l' hU =>
      intro ρ Δ hρ hΔ
      refine ⟨RedURel eqrel (logRelRec eqrel l l' hU.lt) Δ, .U ⟨hU.lt, hΔ⟩, ?_, ?_, ?_⟩
      · intro B hB
        change B = .univ at hB
        subst hB
        rfl
      · rintro t ⟨A₀, d, typeA, AeqA, relt, ht⟩
        rcases ihRec l' hU.lt hρ hΔ ht with ⟨relt', ht', _, _, _⟩
        exact ⟨wk ρ A₀, wkStarWf hρ hΔ d, typeA.wk ρ,
          eqrel.wkTerm hρ hΔ AeqA, ⟨relt', ht'⟩⟩
      · rintro t u ⟨A₀, B₀, d, d', typeA, typeB, AeqB, relt, ht, ⟨relu, hu⟩, tequ⟩
        rcases ihRec l' hU.lt hρ hΔ ht with ⟨relt', ht', hEq, _, _⟩
        rcases ihRec l' hU.lt hρ hΔ hu with ⟨relu', hu', _, _, _⟩
        exact ⟨wk ρ A₀, wk ρ B₀, wkStarWf hρ hΔ d, wkStarWf hρ hΔ d',
          typeA.wk ρ, typeB.wk ρ,
          eqrel.wkTerm hρ hΔ AeqB, relt', ht', ⟨relu', hu'⟩, hEq tequ⟩
  | @nat Γ A D =>
      intro ρ Δ hρ hΔ
      refine ⟨RedNatRel eqrel Δ, .nat (wkTypeStarWf hρ hΔ D), ?_, ?_, ?_⟩
      · intro B hB
        exact wkTypeStar hρ hΔ hB
      · intro t ht
        exact wkTermNat hρ hΔ ht
      · intro t u htu
        exact wkEqTermNat hρ hΔ htu
  | @ne Γ A K neA =>
      intro ρ Δ hρ hΔ
      refine ⟨RedNeRel eqrel Δ (wk ρ K),
        .ne ⟨wkTypeStarWf hρ hΔ neA.D, neA.neK.wk ρ, eqrel.wkNe hρ hΔ neA.KeqK⟩,
        ?_, ?_, ?_⟩
      · rintro B ⟨M, D', neM, KeqM⟩
        exact ⟨wk ρ M, wkTypeStarWf hρ hΔ D', neM.wk ρ, eqrel.wkNe hρ hΔ KeqM⟩
      · rintro t ⟨k, d, nf⟩
        exact ⟨wk ρ k, wkStarWf hρ hΔ d, wkTermNe hρ hΔ nf⟩
      · rintro t u ⟨k, m, d, d', nf⟩
        exact ⟨wk ρ k, wk ρ m, wkStarWf hρ hΔ d, wkStarWf hρ hΔ d',
          wkEqTermNe hρ hΔ nf⟩
  | @pi Γ A F G D hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext _ihF _ihG =>
      intro ρ Δ hρ hΔ
      have hρF : TypeWf Δ (wk ρ F) := wkTypeWf hρ hΔ hF
      have hρG : TypeWf (wk ρ F :: Δ) (wk (.lift ρ) G) :=
        wkTypeWf (.lift hρ) (.cons hΔ hρF) hG
      let relF' : Wk → Context → RedRel → Prop :=
        fun ρ₁ Δ₁ rel ↦ relF (compWk ρ₁ ρ) Δ₁ rel
      let relG' : Wk → Context → Term → RedRel → Prop :=
        fun ρ₁ Δ₁ a rel ↦ relG (compWk ρ₁ ρ) Δ₁ a rel
      refine ⟨RedPiRel eqrel Δ (wk ρ F) (wk (.lift ρ) G) relF' relG',
        .pi (wkTypeStarWf hρ hΔ D) hρF hρG (eqrel.wkType hρ hΔ AeqA)
          relF' relG'
          (fun hρ₁ hΔ₁ ↦ hF_ex (hρ₁.comp hρ) hΔ₁)
          (fun hρ₁ hΔ₁ r hr ↦ by
            rw [wk_comp]
            exact derivF (hρ₁.comp hρ) hΔ₁ r hr)
          (fun hρ₁ hΔ₁ ha ↦ hG_ex (hρ₁.comp hρ) hΔ₁ ha)
          (fun {ρ₁ Δ₁ a} hρ₁ hΔ₁ ha s hs ↦ by
            rw [← wk_comp_subst]
            exact derivG (hρ₁.comp hρ) hΔ₁ ha s hs)
          (fun {ρ₁ Δ₁ a b} hρ₁ hΔ₁ ha hb hab ↦ by
            rw [← wk_comp_subst]
            exact Gext (hρ₁.comp hρ) hΔ₁ ha hb hab),
        ?_, ?_, ?_⟩
      · rintro B ⟨F', G', D', AeqB, FeqF', GeqG'⟩
        refine ⟨wk ρ F', wk (.lift ρ) G', wkTypeStar hρ hΔ D', eqrel.wkType hρ hΔ AeqB,
          fun {ρ₁ Δ₁} hρ₁ hΔ₁ ↦ ?_,
          fun {ρ₁ Δ₁ a} hρ₁ hΔ₁ ha ↦ ?_⟩
        · rw [wk_comp]
          exact FeqF' (hρ₁.comp hρ) hΔ₁
        · rw [← wk_comp_subst]
          exact GeqG' (hρ₁.comp hρ) hΔ₁ ha
      · rintro t ⟨f, d, funcF, feqf, appEq, appTerm⟩
        refine ⟨wk ρ f, wkStarWf hρ hΔ d, funcF.wk ρ,
          eqrel.wkTerm hρ hΔ feqf,
          fun {ρ₁ Δ₁ a b} hρ₁ hΔ₁ ha hb hab ↦ ?_,
          fun {ρ₁ Δ₁ a} hρ₁ hΔ₁ ha ↦ ?_⟩
        · rw [wk_comp]
          exact appEq (hρ₁.comp hρ) hΔ₁ ha hb hab
        · rw [wk_comp]
          exact appTerm (hρ₁.comp hρ) hΔ₁ ha
      · rintro t u ⟨f, g, d, d', funcF, funcG, feqg, ht, hu, appEq⟩
        have hPiTerm : ∀ {t},
            RedPiTerm eqrel Γ F G relF relG t →
            RedPiTerm eqrel Δ (wk ρ F) (wk (.lift ρ) G) relF' relG' (wk ρ t) := by
          rintro t ⟨f₀, d₀, funcF₀, feqf₀, appEq₀, appTerm₀⟩
          refine ⟨wk ρ f₀, wkStarWf hρ hΔ d₀, funcF₀.wk ρ,
            eqrel.wkTerm hρ hΔ feqf₀,
            fun {ρ₁ Δ₁ a b} hρ₁ hΔ₁ ha hb hab ↦ ?_,
            fun {ρ₁ Δ₁ a} hρ₁ hΔ₁ ha ↦ ?_⟩
          · rw [wk_comp]
            exact appEq₀ (hρ₁.comp hρ) hΔ₁ ha hb hab
          · rw [wk_comp]
            exact appTerm₀ (hρ₁.comp hρ) hΔ₁ ha
        refine ⟨wk ρ f, wk ρ g, wkStarWf hρ hΔ d, wkStarWf hρ hΔ d',
          funcF.wk ρ, funcG.wk ρ,
          eqrel.wkTerm hρ hΔ feqg, hPiTerm ht, hPiTerm hu,
          fun {ρ₁ Δ₁ a} hρ₁ hΔ₁ ha ↦ ?_⟩
        rw [wk_comp, wk_comp]
        exact appEq (hρ₁.comp hρ) hΔ₁ ha
  | @emb Γ A l' rel hlt hA =>
      intro ρ Δ hρ hΔ
      rcases ihRec l' hlt hρ hΔ hA with ⟨rel', hA', hEq, hTerm, hEqTerm⟩
      exact ⟨rel', .emb hlt hA', hEq, hTerm, hEqTerm⟩

theorem wkLogRelAt {eqrel : EqRelSet} {l : TypeLevel} {ρ : Wk} {Γ Δ : Context} {A : Term}
    {rel : RedRel} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ)
    (hA : LogRelAt eqrel l Γ A rel) :
    ∃ rel', LogRelAt eqrel l Δ (wk ρ A) rel' ∧
      (∀ {B}, rel.eqType B → rel'.eqType (wk ρ B)) ∧
      (∀ {t}, rel.hasTerm t → rel'.hasTerm (wk ρ t)) ∧
      (∀ {t u}, rel.eqTerm t u → rel'.eqTerm (wk ρ t) (wk ρ u)) := by
  have h0 : ∀ {ρ Γ Δ A rel}, WkCtx ρ Δ Γ → CtxWf Δ →
      LogRelAt eqrel .zero Γ A rel →
      ∃ rel', LogRelAt eqrel .zero Δ (wk ρ A) rel' ∧
        (∀ {B}, rel.eqType B → rel'.eqType (wk ρ B)) ∧
        (∀ {t}, rel.hasTerm t → rel'.hasTerm (wk ρ t)) ∧
        (∀ {t u}, rel.eqTerm t u → rel'.eqTerm (wk ρ t) (wk ρ u)) :=
    fun hρ hΔ hA₀ ↦
      wkLogRel_step (l := .zero) (fun _ hlt ↦ nomatch hlt) hA₀ hρ hΔ
  cases l with
  | zero => exact h0 hρ hΔ hA
  | one =>
      exact wkLogRel_step (l := .one)
        (fun _ hlt _ _ _ _ _ hρ' hΔ' hA₀ ↦ by
          cases hlt
          exact h0 hρ' hΔ' hA₀)
        hA hρ hΔ

/-- Weakening of reducible types (`wk`). -/
theorem wkRed {eqrel : EqRelSet} {l : TypeLevel} {ρ : Wk} {Γ Δ : Context} {A : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (p : RedType eqrel l Γ A) :
    RedType eqrel l Δ (wk ρ A) := by
  rcases p with ⟨rel, hA⟩
  rcases wkLogRelAt hρ hΔ hA with ⟨rel', hA', _⟩
  exact ⟨rel', hA'⟩

/-- Weakening of reducible type equality (`wkEq`). -/
theorem wkRedEq {eqrel : EqRelSet} {l : TypeLevel} {ρ : Wk} {Γ Δ : Context} {A B : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (p : RedType eqrel l Γ A)
    (hAB : RedEq p B) : RedEq (wkRed hρ hΔ p) (wk ρ B) := by
  rcases hAB with ⟨rel, hA, hB⟩
  rcases wkLogRelAt hρ hΔ hA with ⟨rel', hA', hEq, _, _⟩
  exact ⟨rel', hA', hEq hB⟩

/-- Weakening of reducible terms (`wkTerm`). -/
theorem wkRedTerm {eqrel : EqRelSet} {l : TypeLevel} {ρ : Wk} {Γ Δ : Context} {A t : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (p : RedType eqrel l Γ A)
    (ht : RedTerm p t) : RedTerm (wkRed hρ hΔ p) (wk ρ t) := by
  rcases ht with ⟨rel, hA, ht⟩
  rcases wkLogRelAt hρ hΔ hA with ⟨rel', hA', _, hTerm, _⟩
  exact ⟨rel', hA', hTerm ht⟩

/-- Weakening of reducible term equality (`wkEqTerm`). -/
theorem wkRedTermEq {eqrel : EqRelSet} {l : TypeLevel} {ρ : Wk} {Γ Δ : Context} {A t u : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (p : RedType eqrel l Γ A)
    (htu : RedTermEq p t u) : RedTermEq (wkRed hρ hΔ p) (wk ρ t) (wk ρ u) := by
  rcases htu with ⟨rel, hA, htu⟩
  rcases wkLogRelAt hρ hΔ hA with ⟨rel', hA', _, _, hEqTerm⟩
  exact ⟨rel', hA', hEqTerm htu⟩

/-!
## Conversion of the Logical Relation (`Definition/LogicalRelation/Properties/Conversion.agda`)
-/

/-- Conversion of syntactic multi-step term reduction closures (`convRed:*:`). -/
theorem convStarWf {Γ : Context} {t u A B : Term}
    (d : StarWf Γ t u A) (hAB : TypeEq Γ A B) : StarWf Γ t u B :=
  ⟨.conv d.source hAB, .conv d.target hAB, d.reduction.conv hAB⟩

/-- Single-level conversion step for `LogRelAt`. -/
theorem convLogRel_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A B relA relB},
      logRelRec eqrel l l' hlt Γ A relA → LogRelShape eqrel Γ B relB → relA.eqType B →
      (∀ {t}, (relA.hasTerm t ↔ relB.hasTerm t)) ∧
      (∀ {t u}, (relA.eqTerm t u ↔ relB.eqTerm t u)))
    {Γ : Context} {A : Term} {relA : RedRel}
    (hA : LogRelAt eqrel l Γ A relA) :
    ∀ {B : Term} {relB : RedRel},
      LogRelShape eqrel Γ B relB →
      relA.eqType B →
      (∀ {t}, (relA.hasTerm t ↔ relB.hasTerm t)) ∧
      (∀ {t u}, (relA.eqTerm t u ↔ relB.eqTerm t u)) := by
  induction hA with
  | @U Γ l₁ hU =>
      intro B relB hB hAB
      change B = .univ at hAB
      subst hAB
      cases hB with
      | U hU₂ =>
          rw [logRelRec_eq hU.lt hU₂.lt]
          exact ⟨fun {_} ↦ Iff.rfl, fun {_ _} ↦ Iff.rfl⟩
      | nat D =>
          have h := whnfRedStar D.reduction .univ
          cases h
      | ne neB =>
          have h := whnfRedStar neB.D.reduction .univ
          subst h
          cases neB.neK
      | pi D =>
          have h := whnfRedStar D.reduction .univ
          cases h
  | @nat Γ A D₁ =>
      intro B relB hB hAB
      change TypeStar Γ B .nat at hAB
      cases hB with
      | U _ =>
          have h := whnfRedStar hAB .univ
          cases h
      | nat _ =>
          exact ⟨fun {_} ↦ Iff.rfl, fun {_ _} ↦ Iff.rfl⟩
      | ne neB =>
          have h := whrDetStar ⟨hAB, .nat⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ =>
          have h := whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .pi⟩
          cases h
  | @ne Γ A K₁ neA =>
      intro B relB hB hAB
      rcases hAB with ⟨M, D', neM, KeqM⟩
      cases hB with
      | U _ =>
          have h := whnfRedStar D'.reduction .univ
          subst h
          cases neM
      | nat D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D'.reduction, .neutral neM⟩
          subst h
          cases neM
      | @ne _ _ K₂ neB =>
          have hMK₂ : M = K₂ :=
            whrDetStar ⟨D'.reduction, .neutral neM⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst hMK₂
          have hK₁K₂ : TypeEq Γ K₁ M := eqrel.typeToEq (eqrel.neToType KeqM)
          refine ⟨?_, ?_⟩
          · intro t
            constructor
            · rintro ⟨k, d, nf⟩
              exact ⟨k, convStarWf d hK₁K₂,
                ⟨nf.neK, .conv nf.hk hK₁K₂, eqrel.convNe nf.keqk hK₁K₂⟩⟩
            · rintro ⟨k, d, nf⟩
              exact ⟨k, convStarWf d (.symm hK₁K₂),
                ⟨nf.neK, .conv nf.hk (.symm hK₁K₂), eqrel.convNe nf.keqk (.symm hK₁K₂)⟩⟩
          · intro t u
            constructor
            · rintro ⟨k, m, d, d'', nf⟩
              exact ⟨k, m, convStarWf d hK₁K₂, convStarWf d'' hK₁K₂,
                ⟨nf.neK, nf.neM, eqrel.convNe nf.keqm hK₁K₂⟩⟩
            · rintro ⟨k, m, d, d'', nf⟩
              exact ⟨k, m, convStarWf d (.symm hK₁K₂), convStarWf d'' (.symm hK₁K₂),
                ⟨nf.neK, nf.neM, eqrel.convNe nf.keqm (.symm hK₁K₂)⟩⟩
      | pi D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .pi⟩ ⟨D'.reduction, .neutral neM⟩
          subst h
          cases neM
  | @pi Γ A F₁ G₁ D₁ _hF₁ _hG₁ _AeqA₁ relF₁ relG₁ hF_ex₁ derivF₁ hG_ex₁ derivG₁ _Gext₁ ihF ihG =>
      intro B relB hB hAB
      rcases hAB with ⟨F', G', D', AeqB, FeqF', GeqG'⟩
      cases hB with
      | U _ =>
          have h := whnfRedStar D' .univ
          cases h
      | nat D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D', .pi⟩
          cases h
      | ne neB =>
          have h := whrDetStar ⟨D', .pi⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | @pi l₂ _ _ F₂ G₂ D₂ _ _ _ relF₂ relG₂ hF_ex₂ derivF₂ hG_ex₂ derivG₂ _ =>
          have hPi : Term.pi F₂ G₂ = Term.pi F' G' :=
            whrDetStar ⟨D₂.reduction, .pi⟩ ⟨D', .pi⟩
          injection hPi with hF₂ hG₂
          subst hF₂ hG₂
          have hPiEq : TypeEq Γ (.pi F₁ G₁) (.pi F₂ G₂) := eqrel.typeToEq AeqB
          have hF_conv : ∀ {ρ Δ} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ),
              (∀ {a}, RelFHasTerm relF₁ ρ Δ a ↔ RelFHasTerm relF₂ ρ Δ a) ∧
              (∀ {a b}, RelFEqTerm relF₁ ρ Δ a b ↔ RelFEqTerm relF₂ ρ Δ a b) := by
            intro ρ Δ hρ hΔ
            rcases FeqF' hρ hΔ with ⟨r₁, hr₁, hF₁₂⟩
            rcases hF_ex₂ hρ hΔ with ⟨r₂, hr₂⟩
            have hAt₁ := derivF₁ hρ hΔ r₁ hr₁
            have hAt₂ := derivF₂ hρ hΔ r₂ hr₂
            have hConv := ihF hρ hΔ r₁ hr₁ (logRelShape_of_LogRelAt hAt₂) hF₁₂
            refine ⟨?_, ?_⟩
            · intro a
              constructor
              · rintro ⟨r₁', hr₁', ha⟩
                have ha₁ := (irrelLogRel (derivF₁ hρ hΔ r₁' hr₁') hAt₁).2.1.mp ha
                exact ⟨r₂, hr₂, hConv.1.mp ha₁⟩
              · rintro ⟨r₂', hr₂', ha⟩
                have ha₂ := (irrelLogRel (derivF₂ hρ hΔ r₂' hr₂') hAt₂).2.1.mp ha
                exact ⟨r₁, hr₁, hConv.1.mpr ha₂⟩
            · intro a b
              constructor
              · rintro ⟨r₁', hr₁', hab⟩
                have hab₁ := (irrelLogRel (derivF₁ hρ hΔ r₁' hr₁') hAt₁).2.2.mp hab
                exact ⟨r₂, hr₂, hConv.2.mp hab₁⟩
              · rintro ⟨r₂', hr₂', hab⟩
                have hab₂ := (irrelLogRel (derivF₂ hρ hΔ r₂' hr₂') hAt₂).2.2.mp hab
                exact ⟨r₁, hr₁, hConv.2.mpr hab₂⟩
          have hG_conv : ∀ {ρ Δ a} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ)
              (ha₁ : RelFHasTerm relF₁ ρ Δ a),
              (∀ {t}, RelGHasTerm relG₁ ρ Δ a t ↔ RelGHasTerm relG₂ ρ Δ a t) ∧
              (∀ {t u}, RelGEqTerm relG₁ ρ Δ a t u ↔ RelGEqTerm relG₂ ρ Δ a t u) := by
            intro ρ Δ a hρ hΔ ha₁
            have ha₂ : RelFHasTerm relF₂ ρ Δ a := (hF_conv hρ hΔ).1.mp ha₁
            rcases GeqG' hρ hΔ ha₁ with ⟨s₁, hs₁, hG₁₂⟩
            rcases hG_ex₂ hρ hΔ ha₂ with ⟨s₂, hs₂⟩
            have hAt₁ := derivG₁ hρ hΔ ha₁ s₁ hs₁
            have hAt₂ := derivG₂ hρ hΔ ha₂ s₂ hs₂
            have hConv := ihG hρ hΔ ha₁ s₁ hs₁ (logRelShape_of_LogRelAt hAt₂) hG₁₂
            refine ⟨?_, ?_⟩
            · intro t
              constructor
              · rintro ⟨s₁', hs₁', ht⟩
                have ht₁ := (irrelLogRel (derivG₁ hρ hΔ ha₁ s₁' hs₁') hAt₁).2.1.mp ht
                exact ⟨s₂, hs₂, hConv.1.mp ht₁⟩
              · rintro ⟨s₂', hs₂', ht⟩
                have ht₂ := (irrelLogRel (derivG₂ hρ hΔ ha₂ s₂' hs₂') hAt₂).2.1.mp ht
                exact ⟨s₁, hs₁, hConv.1.mpr ht₂⟩
            · intro t u
              constructor
              · rintro ⟨s₁', hs₁', htu⟩
                have htu₁ := (irrelLogRel (derivG₁ hρ hΔ ha₁ s₁' hs₁') hAt₁).2.2.mp htu
                exact ⟨s₂, hs₂, hConv.2.mp htu₁⟩
              · rintro ⟨s₂', hs₂', htu⟩
                have htu₂ := (irrelLogRel (derivG₂ hρ hΔ ha₂ s₂' hs₂') hAt₂).2.2.mp htu
                exact ⟨s₁, hs₁, hConv.2.mpr htu₂⟩
          have hPiTermIff : ∀ {t},
              RedPiTerm eqrel Γ F₁ G₁ relF₁ relG₁ t ↔ RedPiTerm eqrel Γ F₂ G₂ relF₂ relG₂ t := by
            intro t
            constructor
            · rintro ⟨f, d, funcF, feqf, appEq, appTerm⟩
              refine ⟨f, convStarWf d hPiEq, funcF, eqrel.convTerm feqf hPiEq,
                fun {ρ Δ a b} hρ hΔ ha₂ hb₂ hab₂ ↦ ?_,
                fun {ρ Δ a} hρ hΔ ha₂ ↦ ?_⟩
              · have ha₁ := (hF_conv hρ hΔ).1.mpr ha₂
                have hb₁ := (hF_conv hρ hΔ).1.mpr hb₂
                have hab₁ := (hF_conv hρ hΔ).2.mpr hab₂
                exact (hG_conv hρ hΔ ha₁).2.mp (appEq hρ hΔ ha₁ hb₁ hab₁)
              · have ha₁ := (hF_conv hρ hΔ).1.mpr ha₂
                exact (hG_conv hρ hΔ ha₁).1.mp (appTerm hρ hΔ ha₁)
            · rintro ⟨f, d, funcF, feqf, appEq, appTerm⟩
              refine ⟨f, convStarWf d (.symm hPiEq), funcF, eqrel.convTerm feqf (.symm hPiEq),
                fun {ρ Δ a b} hρ hΔ ha₁ hb₁ hab₁ ↦ ?_,
                fun {ρ Δ a} hρ hΔ ha₁ ↦ ?_⟩
              · have ha₂ := (hF_conv hρ hΔ).1.mp ha₁
                have hb₂ := (hF_conv hρ hΔ).1.mp hb₁
                have hab₂ := (hF_conv hρ hΔ).2.mp hab₁
                exact (hG_conv hρ hΔ ha₁).2.mpr (appEq hρ hΔ ha₂ hb₂ hab₂)
              · have ha₂ := (hF_conv hρ hΔ).1.mp ha₁
                exact (hG_conv hρ hΔ ha₁).1.mpr (appTerm hρ hΔ ha₂)
          refine ⟨hPiTermIff, ?_⟩
          intro t u
          constructor
          · rintro ⟨f, g, d, d'', funcF, funcG, feqg, ht, hu, appEq⟩
            refine ⟨f, g, convStarWf d hPiEq, convStarWf d'' hPiEq, funcF, funcG,
              eqrel.convTerm feqg hPiEq, hPiTermIff.mp ht, hPiTermIff.mp hu,
              fun {ρ Δ a} hρ hΔ ha₂ ↦ ?_⟩
            have ha₁ := (hF_conv hρ hΔ).1.mpr ha₂
            exact (hG_conv hρ hΔ ha₁).2.mp (appEq hρ hΔ ha₁)
          · rintro ⟨f, g, d, d'', funcF, funcG, feqg, ht, hu, appEq⟩
            refine ⟨f, g, convStarWf d (.symm hPiEq), convStarWf d'' (.symm hPiEq), funcF, funcG,
              eqrel.convTerm feqg (.symm hPiEq), hPiTermIff.mpr ht, hPiTermIff.mpr hu,
              fun {ρ Δ a} hρ hΔ ha₁ ↦ ?_⟩
            have ha₂ := (hF_conv hρ hΔ).1.mp ha₁
            exact (hG_conv hρ hΔ ha₁).2.mpr (appEq hρ hΔ ha₂)
  | @emb Γ A l' relA hlt hA =>
      intro B relB hB hAB
      exact ihRec l' hlt hA hB hAB

theorem convLogRelAt {eqrel : EqRelSet} {l₁ l₂ : TypeLevel} {Γ : Context} {A B : Term}
    {relA relB : RedRel}
    (hA : LogRelAt eqrel l₁ Γ A relA)
    (hB : LogRelAt eqrel l₂ Γ B relB)
    (hAB : relA.eqType B) :
    (∀ {t}, (relA.hasTerm t ↔ relB.hasTerm t)) ∧
    (∀ {t u}, (relA.eqTerm t u ↔ relB.eqTerm t u)) := by
  have h0 : ∀ {Γ A B relA relB},
      LogRelAt eqrel .zero Γ A relA → LogRelShape eqrel Γ B relB → relA.eqType B →
      (∀ {t}, (relA.hasTerm t ↔ relB.hasTerm t)) ∧
      (∀ {t u}, (relA.eqTerm t u ↔ relB.eqTerm t u)) :=
    fun hA₀ hBs hAB₀ ↦
      convLogRel_step (l := .zero) (fun _ hlt ↦ nomatch hlt) hA₀ hBs hAB₀
  cases l₁ with
  | zero => exact h0 hA (logRelShape_of_LogRelAt hB) hAB
  | one =>
      exact convLogRel_step (l := .one)
        (fun _ hlt _ _ _ _ _ hA₀ hBs hAB₀ ↦ by cases hlt; exact h0 hA₀ hBs hAB₀)
        hA (logRelShape_of_LogRelAt hB) hAB

/-- Left-to-right term conversion (`convTerm₁`). -/
theorem convTerm₁ {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A B t : Term}
    (pA : RedType eqrel l Γ A) (pB : RedType eqrel l' Γ B)
    (hAB : RedEq pA B) (ht : RedTerm pA t) : RedTerm pB t := by
  rcases hAB with ⟨relA, hA, hEqB⟩
  rcases pB with ⟨relB, hB⟩
  rcases ht with ⟨relA', hA', ht⟩
  have htA : relA.hasTerm t := (irrelLogRel hA' hA).2.1.mp ht
  exact ⟨relB, hB, (convLogRelAt hA hB hEqB).1.mp htA⟩

/-- Right-to-left term conversion (`convTerm₂`). -/
theorem convTerm₂ {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A B t : Term}
    (pA : RedType eqrel l Γ A) (pB : RedType eqrel l' Γ B)
    (hAB : RedEq pA B) (ht : RedTerm pB t) : RedTerm pA t := by
  rcases hAB with ⟨relA, hA, hEqB⟩
  rcases ht with ⟨relB, hB, ht⟩
  exact ⟨relA, hA, (convLogRelAt hA hB hEqB).1.mpr ht⟩

/-- Right-to-left term conversion with propositionally equal right types (`convTerm₂′`). -/
theorem convTerm₂' {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A B B' t : Term}
    (hBB' : B = B') (pA : RedType eqrel l Γ A) (pB : RedType eqrel l' Γ B)
    (hAB' : RedEq pA B') (ht : RedTerm pB t) : RedTerm pA t := by
  subst hBB'
  exact convTerm₂ pA pB hAB' ht

/-- Left-to-right term equality conversion (`convEqTerm₁`). -/
theorem convEqTerm₁ {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A B t u : Term}
    (pA : RedType eqrel l Γ A) (pB : RedType eqrel l' Γ B)
    (hAB : RedEq pA B) (htu : RedTermEq pA t u) : RedTermEq pB t u := by
  rcases hAB with ⟨relA, hA, hEqB⟩
  rcases pB with ⟨relB, hB⟩
  rcases htu with ⟨relA', hA', htu⟩
  have htuA : relA.eqTerm t u := (irrelLogRel hA' hA).2.2.mp htu
  exact ⟨relB, hB, (convLogRelAt hA hB hEqB).2.mp htuA⟩

/-- Right-to-left term equality conversion (`convEqTerm₂`). -/
theorem convEqTerm₂ {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A B t u : Term}
    (pA : RedType eqrel l Γ A) (pB : RedType eqrel l' Γ B)
    (hAB : RedEq pA B) (htu : RedTermEq pB t u) : RedTermEq pA t u := by
  rcases hAB with ⟨relA, hA, hEqB⟩
  rcases htu with ⟨relB, hB, htu⟩
  exact ⟨relA, hA, (convLogRelAt hA hB hEqB).2.mpr htu⟩

/-!
## Symmetry of the Logical Relation (`Definition/LogicalRelation/Properties/Symmetry.agda`)
-/

/-- Single-level symmetry step for `LogRelAt` type equality. -/
theorem symLogRel_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A B relA relB},
      logRelRec eqrel l l' hlt Γ A relA → LogRelShape eqrel Γ B relB →
      relA.eqType B → relB.eqType A)
    {Γ : Context} {A : Term} {relA : RedRel}
    (hA : LogRelAt eqrel l Γ A relA) :
    ∀ {B : Term} {relB : RedRel},
      LogRelShape eqrel Γ B relB → relA.eqType B → relB.eqType A := by
  induction hA with
  | @U Γ l₁ hU =>
      intro B relB hB hAB
      change B = .univ at hAB
      subst hAB
      cases hB with
      | U _ => rfl
      | nat D => cases whnfRedStar D.reduction .univ
      | ne neB =>
          have h := whnfRedStar neB.D.reduction .univ
          subst h
          cases neB.neK
      | pi D => cases whnfRedStar D.reduction .univ
  | @nat Γ A D₁ =>
      intro B relB hB hAB
      change TypeStar Γ B .nat at hAB
      cases hB with
      | U _ => cases whnfRedStar hAB .univ
      | nat _ => exact D₁.reduction
      | ne neB =>
          have h := whrDetStar ⟨hAB, .nat⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ => cases whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .pi⟩
  | @ne Γ A K₁ neA =>
      intro B relB hB hAB
      rcases hAB with ⟨M, D', neM, KeqM⟩
      cases hB with
      | U _ =>
          have h := whnfRedStar D'.reduction .univ
          subst h
          cases neM
      | nat D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D'.reduction, .neutral neM⟩
          subst h
          cases neM
      | @ne _ _ K₂ neB =>
          have hMK₂ : M = K₂ :=
            whrDetStar ⟨D'.reduction, .neutral neM⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst hMK₂
          exact ⟨K₁, neA.D, neA.neK, eqrel.symmNe KeqM⟩
      | pi D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .pi⟩ ⟨D'.reduction, .neutral neM⟩
          subst h
          cases neM
  | @pi Γ A F₁ G₁ D₁ _hF₁ _hG₁ _AeqA₁ relF₁ relG₁ _hF_ex₁ derivF₁ _hG_ex₁ _derivG₁ _Gext₁ ihF ihG =>
      intro B relB hB hAB
      rcases hAB with ⟨F', G', D', AeqB, FeqF', GeqG'⟩
      cases hB with
      | U _ => cases whnfRedStar D' .univ
      | nat D₂ => cases whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D', .pi⟩
      | ne neB =>
          have h := whrDetStar ⟨D', .pi⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | @pi l₂ _ _ F₂ G₂ D₂ _ _ _ relF₂ relG₂ hF_ex₂ derivF₂ hG_ex₂ derivG₂ _ =>
          have hPi : Term.pi F₂ G₂ = Term.pi F' G' :=
            whrDetStar ⟨D₂.reduction, .pi⟩ ⟨D', .pi⟩
          injection hPi with hF₂ hG₂
          subst hF₂ hG₂
          refine ⟨F₁, G₁, D₁.reduction, eqrel.symmType AeqB,
            fun {ρ Δ} hρ hΔ ↦ ?_,
            fun {ρ Δ a} hρ hΔ ha₂ ↦ ?_⟩
          · rcases FeqF' hρ hΔ with ⟨r₁, hr₁, hF₁₂⟩
            rcases hF_ex₂ hρ hΔ with ⟨r₂, hr₂⟩
            have hAt₂ := derivF₂ hρ hΔ r₂ hr₂
            exact ⟨r₂, hr₂, ihF hρ hΔ r₁ hr₁ (logRelShape_of_LogRelAt hAt₂) hF₁₂⟩
          · rcases FeqF' hρ hΔ with ⟨r₁, hr₁, hF₁₂⟩
            rcases ha₂ with ⟨r₂, hr₂, ha₂'⟩
            have hAt₁ := derivF₁ hρ hΔ r₁ hr₁
            have hAt₂ := derivF₂ hρ hΔ r₂ hr₂
            have ha₁ : RelFHasTerm relF₁ ρ Δ a :=
              ⟨r₁, hr₁, (convLogRelAt hAt₁ hAt₂ hF₁₂).1.mpr ha₂'⟩
            rcases GeqG' hρ hΔ ha₁ with ⟨s₁, hs₁, hG₁₂⟩
            rcases hG_ex₂ hρ hΔ ⟨r₂, hr₂, ha₂'⟩ with ⟨s₂, hs₂⟩
            have hGAt₂ := derivG₂ hρ hΔ ⟨r₂, hr₂, ha₂'⟩ s₂ hs₂
            exact ⟨s₂, hs₂, ihG hρ hΔ ha₁ s₁ hs₁ (logRelShape_of_LogRelAt hGAt₂) hG₁₂⟩
  | @emb Γ A l' relA hlt hA =>
      intro B relB hB hAB
      exact ihRec l' hlt hA hB hAB

theorem symLogRelAt {eqrel : EqRelSet} {l₁ l₂ : TypeLevel} {Γ : Context} {A B : Term}
    {relA relB : RedRel}
    (hA : LogRelAt eqrel l₁ Γ A relA)
    (hB : LogRelAt eqrel l₂ Γ B relB)
    (hAB : relA.eqType B) : relB.eqType A := by
  have h0 : ∀ {Γ A B relA relB},
      LogRelAt eqrel .zero Γ A relA → LogRelShape eqrel Γ B relB →
      relA.eqType B → relB.eqType A :=
    fun hA₀ hBs hAB₀ ↦
      symLogRel_step (l := .zero) (fun _ hlt ↦ nomatch hlt) hA₀ hBs hAB₀
  cases l₁ with
  | zero => exact h0 hA (logRelShape_of_LogRelAt hB) hAB
  | one =>
      exact symLogRel_step (l := .one)
        (fun _ hlt _ _ _ _ _ hA₀ hBs hAB₀ ↦ by cases hlt; exact h0 hA₀ hBs hAB₀)
        hA (logRelShape_of_LogRelAt hB) hAB

/-- Symmetry of reducible type equality (`symEq`). -/
theorem symEq {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A B : Term}
    (pA : RedType eqrel l Γ A) (pB : RedType eqrel l' Γ B)
    (hAB : RedEq pA B) : RedEq pB A := by
  rcases hAB with ⟨relA, hA, hEqB⟩
  rcases pB with ⟨relB, hB⟩
  exact ⟨relB, hB, symLogRelAt hA hB hEqB⟩

theorem symNeutralTerm {eqrel : EqRelSet} {Γ : Context} {k m A : Term}
    (nf : RedNeNfEq eqrel Γ k m A) : RedNeNfEq eqrel Γ m k A :=
  ⟨nf.neM, nf.neK, eqrel.symmNe nf.keqm⟩

theorem symEqTermNat {eqrel : EqRelSet} {Γ : Context} {t u : Term}
    (htu : RedNatTermEq eqrel Γ t u) : RedNatTermEq eqrel Γ u t :=
  @RedNatTermEq.rec eqrel Γ
    (fun t u _ ↦ RedNatTermEq eqrel Γ u t)
    (fun k k' _ ↦ NaturalEqProp eqrel Γ k' k)
    (fun t u k k' d d' keqk' _ ih ↦
      .mk u t k' k d' d (eqrel.symmTerm keqk') ih)
    (fun _ ih ↦ .suc ih)
    .zero
    (fun nf ↦ .ne (symNeutralTerm nf))
    t u htu

theorem symNaturalProp {eqrel : EqRelSet} {Γ : Context} {k k' : Term}
    (hk : NaturalEqProp eqrel Γ k k') : NaturalEqProp eqrel Γ k' k :=
  @NaturalEqProp.rec eqrel Γ
    (fun t u _ ↦ RedNatTermEq eqrel Γ u t)
    (fun k k' _ ↦ NaturalEqProp eqrel Γ k' k)
    (fun t u k k' d d' keqk' _ ih ↦
      .mk u t k' k d' d (eqrel.symmTerm keqk') ih)
    (fun _ ih ↦ .suc ih)
    .zero
    (fun nf ↦ .ne (symNeutralTerm nf))
    k k' hk

theorem symEqTerm_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A rel t u},
      logRelRec eqrel l l' hlt Γ A rel → rel.eqTerm t u → rel.eqTerm u t)
    (hSymType : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A B relA relB},
      logRelRec eqrel l l' hlt Γ A relA → logRelRec eqrel l l' hlt Γ B relB →
      relA.eqType B → relB.eqType A)
    {Γ : Context} {A : Term} {rel : RedRel}
    (hA : LogRelAt eqrel l Γ A rel) :
    ∀ {t u : Term}, rel.eqTerm t u → rel.eqTerm u t := by
  induction hA with
  | @U Γ l' hU =>
      rintro t u ⟨A₀, B₀, d, d', typeA, typeB, AeqB, relt, ht, ⟨relu, hu⟩, tequ⟩
      exact ⟨B₀, A₀, d', d, typeB, typeA, eqrel.symmTerm AeqB, relu, hu, ⟨relt, ht⟩,
        hSymType l' hU.lt ht hu tequ⟩
  | @nat Γ A _ =>
      intro t u htu
      exact symEqTermNat htu
  | @ne Γ A K _ =>
      rintro t u ⟨k, m, d, d', nf⟩
      exact ⟨m, k, d', d, symNeutralTerm nf⟩
  | @pi Γ A F G _ _ _ _ relF relG _ _ _ _ _ _ihF ihG =>
      rintro t u ⟨f, g, d, d', funcF, funcG, feqg, ht, hu, appEq⟩
      refine ⟨g, f, d', d, funcG, funcF, eqrel.symmTerm feqg, hu, ht,
        fun {ρ Δ a} hρ hΔ ha ↦ ?_⟩
      rcases appEq hρ hΔ ha with ⟨s, hs, hfg⟩
      exact ⟨s, hs, ihG hρ hΔ ha s hs hfg⟩
  | @emb Γ A l' rel hlt hA =>
      intro t u htu
      exact ihRec l' hlt hA htu

/-- Symmetry of reducible term equality (`symEqTerm`). -/
theorem symEqTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t u : Term}
    (pA : RedType eqrel l Γ A) (htu : RedTermEq pA t u) : RedTermEq pA u t := by
  rcases htu with ⟨rel, hA, htu⟩
  have h0 : ∀ {Γ A rel t u},
      LogRelAt eqrel .zero Γ A rel → rel.eqTerm t u → rel.eqTerm u t :=
    fun hA₀ htu₀ ↦
      symEqTerm_step (l := .zero) (fun _ hlt ↦ nomatch hlt) (fun _ hlt ↦ nomatch hlt) hA₀ htu₀
  cases l with
  | zero => exact ⟨rel, hA, h0 hA htu⟩
  | one =>
      refine ⟨rel, hA, symEqTerm_step (l := .one) ?_ ?_ hA htu⟩
      · intro _ hlt _ _ _ _ _ hA₀ htu₀
        cases hlt
        exact h0 hA₀ htu₀
      · intro _ hlt _ _ _ _ _ hA₀ hB₀ hAB₀
        cases hlt
        exact symLogRelAt (l₁ := .zero) (l₂ := .zero) hA₀ hB₀ hAB₀

/-!
## Transitivity of the Logical Relation (`Definition/LogicalRelation/Properties/Transitivity.agda`)
-/

/-- Single-level transitivity step for `LogRelAt` type equality. -/
theorem transLogRel_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A B C relA relB},
      logRelRec eqrel l l' hlt Γ A relA → LogRelShape eqrel Γ B relB →
      relA.eqType B → relB.eqType C → relA.eqType C)
    {Γ : Context} {A : Term} {relA : RedRel}
    (hA : LogRelAt eqrel l Γ A relA) :
    ∀ {B C : Term} {relB : RedRel},
      LogRelShape eqrel Γ B relB → relA.eqType B → relB.eqType C → relA.eqType C := by
  induction hA with
  | @U Γ l₁ _ =>
      intro B C relB hB hAB hBC
      change B = .univ at hAB
      subst hAB
      cases hB with
      | U _ => exact hBC
      | nat D => cases whnfRedStar D.reduction .univ
      | ne neB =>
          have h := whnfRedStar neB.D.reduction .univ
          subst h
          cases neB.neK
      | pi D => cases whnfRedStar D.reduction .univ
  | @nat Γ A _ =>
      intro B C relB hB hAB hBC
      change TypeStar Γ B .nat at hAB
      cases hB with
      | U _ => cases whnfRedStar hAB .univ
      | nat _ => exact hBC
      | ne neB =>
          have h := whrDetStar ⟨hAB, .nat⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ => cases whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .pi⟩
  | @ne Γ A K₁ _ =>
      intro B C relB hB hAB hBC
      rcases hAB with ⟨M, D', neM, KeqM⟩
      cases hB with
      | U _ =>
          have h := whnfRedStar D'.reduction .univ
          subst h
          cases neM
      | nat D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D'.reduction, .neutral neM⟩
          subst h
          cases neM
      | @ne _ _ K₂ neB =>
          have hMK₂ : M = K₂ :=
            whrDetStar ⟨D'.reduction, .neutral neM⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst hMK₂
          rcases hBC with ⟨M₁, D'', neM₁, K₂eqM₁⟩
          exact ⟨M₁, D'', neM₁, eqrel.transNe KeqM K₂eqM₁⟩
      | pi D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .pi⟩ ⟨D'.reduction, .neutral neM⟩
          subst h
          cases neM
  | @pi Γ A F₁ G₁ _ _hF₁ _hG₁ _AeqA₁ relF₁ relG₁ _hF_ex₁ derivF₁ _hG_ex₁ _derivG₁ _Gext₁ ihF ihG =>
      intro B C relB hB hAB hBC
      rcases hAB with ⟨F', G', D', AeqB, FeqF', GeqG'⟩
      cases hB with
      | U _ => cases whnfRedStar D' .univ
      | nat D₂ => cases whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D', .pi⟩
      | ne neB =>
          have h := whrDetStar ⟨D', .pi⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | @pi l₂ _ _ F₂ G₂ D₂ _ _ _ relF₂ relG₂ _hF_ex₂ derivF₂ _hG_ex₂ derivG₂ _ =>
          have hPi : Term.pi F₂ G₂ = Term.pi F' G' :=
            whrDetStar ⟨D₂.reduction, .pi⟩ ⟨D', .pi⟩
          injection hPi with hF₂ hG₂
          subst hF₂ hG₂
          rcases hBC with ⟨F'', G'', D'', BeqC, FeqF'', GeqG''⟩
          refine ⟨F'', G'', D'', eqrel.transType AeqB BeqC,
            fun {ρ Δ} hρ hΔ ↦ ?_,
            fun {ρ Δ a} hρ hΔ ha₁ ↦ ?_⟩
          · rcases FeqF' hρ hΔ with ⟨r₁, hr₁, hF₁₂⟩
            rcases FeqF'' hρ hΔ with ⟨r₂, hr₂, hF₂₃⟩
            have hAt₂ := derivF₂ hρ hΔ r₂ hr₂
            exact ⟨r₁, hr₁, ihF hρ hΔ r₁ hr₁ (logRelShape_of_LogRelAt hAt₂) hF₁₂ hF₂₃⟩
          · rcases FeqF' hρ hΔ with ⟨r₁, hr₁, hF₁₂⟩
            rcases FeqF'' hρ hΔ with ⟨r₂, hr₂, _⟩
            rcases ha₁ with ⟨r₁', hr₁', ha₁'⟩
            have hAt₁ := derivF₁ hρ hΔ r₁ hr₁
            have hAt₁' := derivF₁ hρ hΔ r₁' hr₁'
            have hAt₂ := derivF₂ hρ hΔ r₂ hr₂
            have ha₁_r₁ : r₁.hasTerm a := (irrelLogRel hAt₁' hAt₁).2.1.mp ha₁'
            have ha₂ : RelFHasTerm relF₂ ρ Δ a :=
              ⟨r₂, hr₂, (convLogRelAt hAt₁ hAt₂ hF₁₂).1.mp ha₁_r₁⟩
            rcases GeqG' hρ hΔ ⟨r₁', hr₁', ha₁'⟩ with ⟨s₁, hs₁, hG₁₂⟩
            rcases GeqG'' hρ hΔ ha₂ with ⟨s₂, hs₂, hG₂₃⟩
            have hGAt₂ := derivG₂ hρ hΔ ha₂ s₂ hs₂
            exact ⟨s₁, hs₁, ihG hρ hΔ ⟨r₁', hr₁', ha₁'⟩ s₁ hs₁ (logRelShape_of_LogRelAt hGAt₂) hG₁₂ hG₂₃⟩
  | @emb Γ A l' relA hlt hA =>
      intro B C relB hB hAB hBC
      exact ihRec l' hlt hA hB hAB hBC

theorem transLogRelAt {eqrel : EqRelSet} {l₁ l₂ : TypeLevel} {Γ : Context} {A B C : Term}
    {relA relB : RedRel}
    (hA : LogRelAt eqrel l₁ Γ A relA)
    (hB : LogRelAt eqrel l₂ Γ B relB)
    (hAB : relA.eqType B)
    (hBC : relB.eqType C) : relA.eqType C := by
  have h0 : ∀ {Γ A B C relA relB},
      LogRelAt eqrel .zero Γ A relA → LogRelShape eqrel Γ B relB →
      relA.eqType B → relB.eqType C → relA.eqType C :=
    fun hA₀ hBs hAB₀ hBC₀ ↦
      transLogRel_step (l := .zero) (fun _ hlt ↦ nomatch hlt) hA₀ hBs hAB₀ hBC₀
  cases l₁ with
  | zero => exact h0 hA (logRelShape_of_LogRelAt hB) hAB hBC
  | one =>
      exact transLogRel_step (l := .one)
        (fun _ hlt _ _ _ _ _ _ hA₀ hBs hAB₀ hBC₀ ↦ by cases hlt; exact h0 hA₀ hBs hAB₀ hBC₀)
        hA (logRelShape_of_LogRelAt hB) hAB hBC

/-- Transitivity of reducible type equality (`transEq`). -/
theorem transEq {eqrel : EqRelSet} {l l' l'' : TypeLevel} {Γ : Context} {A B C : Term}
    (pA : RedType eqrel l Γ A) (pB : RedType eqrel l' Γ B) (_pC : RedType eqrel l'' Γ C)
    (hAB : RedEq pA B) (hBC : RedEq pB C) : RedEq pA C := by
  rcases hAB with ⟨relA, hA, hEqB⟩
  rcases hBC with ⟨relB, hB, hEqC⟩
  exact ⟨relA, hA, transLogRelAt hA hB hEqB hEqC⟩

/-- Transitivity of reducible type equality with propositionally equal types (`transEq′`). -/
theorem transEq' {eqrel : EqRelSet} {l l' l'' : TypeLevel} {Γ : Context} {A B B' C C' : Term}
    (hBB' : B = B') (hCC' : C = C')
    (pA : RedType eqrel l Γ A) (pB : RedType eqrel l' Γ B) (pC : RedType eqrel l'' Γ C)
    (hAB' : RedEq pA B') (hBC' : RedEq pB C') : RedEq pA C := by
  subst hBB' hCC'
  exact transEq pA pB pC hAB' hBC'

theorem transEqTermNe {eqrel : EqRelSet} {Γ : Context} {n n' n'' A : Term}
    (nf₁ : RedNeNfEq eqrel Γ n n' A) (nf₂ : RedNeNfEq eqrel Γ n' n'' A) :
    RedNeNfEq eqrel Γ n n'' A :=
  ⟨nf₁.neK, nf₂.neM, eqrel.transNe nf₁.keqm nf₂.keqm⟩

theorem transEqTermNat {eqrel : EqRelSet} {Γ : Context} {n n' n'' : Term}
    (h₁ : RedNatTermEq eqrel Γ n n') (h₂ : RedNatTermEq eqrel Γ n' n'') :
    RedNatTermEq eqrel Γ n n'' :=
  @RedNatTermEq.rec eqrel Γ
    (fun n n' _ ↦ ∀ {n''}, RedNatTermEq eqrel Γ n' n'' → RedNatTermEq eqrel Γ n n'')
    (fun k k' _ ↦ ∀ {k''}, NaturalEqProp eqrel Γ k' k'' → NaturalEqProp eqrel Γ k k'')
    (fun t u k k' d d' keqk' prop ih {n''} h₂ ↦ by
      cases h₂ with
      | mk _ _ k₁ k'' d₁ d'' k₁eqk'' prop₁ =>
          have ⟨_, natK'⟩ := split_of_NaturalEqProp prop
          have ⟨natK₁, _⟩ := split_of_NaturalEqProp prop₁
          have hk₁ : k₁ = k' :=
            whrDetStarTerm ⟨d₁.reduction, natK₁.toWhnf⟩ ⟨d'.reduction, natK'.toWhnf⟩
          subst hk₁
          exact .mk t n'' k k'' d d'' (eqrel.transTerm keqk' k₁eqk'') (ih prop₁))
    (fun {a b} _ ih {k''} hk₂ ↦ by
      cases hk₂ with
      | suc h₂' => exact .suc (ih h₂')
      | ne nf => cases nf.neK)
    (fun {k''} hk₂ ↦ hk₂)
    (fun {a b} nf₁ {k''} hk₂ ↦ by
      cases hk₂ with
      | suc _ => cases nf₁.neM
      | zero => exact .ne nf₁
      | ne nf₂ => exact .ne (transEqTermNe nf₁ nf₂))
    n n' h₁ (n'' := n'') h₂

theorem transNaturalProp {eqrel : EqRelSet} {Γ : Context} {k k' k'' : Term}
    (h₁ : NaturalEqProp eqrel Γ k k') (h₂ : NaturalEqProp eqrel Γ k' k'') :
    NaturalEqProp eqrel Γ k k'' := by
  cases h₁ with
  | suc h₁' =>
      cases h₂ with
      | suc h₂' => exact .suc (transEqTermNat h₁' h₂')
      | ne nf => cases nf.neK
  | zero => exact h₂
  | ne nf₁ =>
      cases h₂ with
      | suc _ => cases nf₁.neM
      | zero => exact .ne nf₁
      | ne nf₂ => exact .ne (transEqTermNe nf₁ nf₂)

theorem transEqTerm_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A rel t u v},
      logRelRec eqrel l l' hlt Γ A rel → rel.eqTerm t u → rel.eqTerm u v → rel.eqTerm t v)
    (hTransType : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A B C relA relB relB'},
      logRelRec eqrel l l' hlt Γ A relA →
      logRelRec eqrel l l' hlt Γ B relB →
      logRelRec eqrel l l' hlt Γ B relB' →
      relA.eqType B → relB'.eqType C → relA.eqType C)
    {Γ : Context} {A : Term} {rel : RedRel}
    (hA : LogRelAt eqrel l Γ A rel) :
    ∀ {t u v : Term}, rel.eqTerm t u → rel.eqTerm u v → rel.eqTerm t v := by
  induction hA with
  | @U Γ l' hU =>
      rintro t u v
        ⟨A₀, B₀, d, d', typeA, typeB, AeqB, relt, ht, ⟨relu, hu⟩, tequ⟩
        ⟨A₁, B₁, d₁, d₁', typeA₁, typeB₁, A₁eqB₁, relu', hu', ⟨relv, hv⟩, ueqv⟩
      have hBA₁ : B₀ = A₁ :=
        whrDetStarTerm ⟨d'.reduction, typeB.toWhnf⟩ ⟨d₁.reduction, typeA₁.toWhnf⟩
      subst hBA₁
      exact ⟨A₀, B₁, d, d₁', typeA, typeB₁, eqrel.transTerm AeqB A₁eqB₁,
        relt, ht, ⟨relv, hv⟩, hTransType l' hU.lt ht hu hu' tequ ueqv⟩
  | @nat Γ A _ =>
      intro t u v htu huv
      exact transEqTermNat htu huv
  | @ne Γ A K _ =>
      rintro t u v ⟨k, m, d, d', nf₁⟩ ⟨k₁, m₁, d₁, d'', nf₂⟩
      have hk₁m : k₁ = m :=
        whrDetStarTerm ⟨d₁.reduction, .neutral nf₂.neK⟩ ⟨d'.reduction, .neutral nf₁.neM⟩
      subst hk₁m
      exact ⟨k, m₁, d, d'', transEqTermNe nf₁ nf₂⟩
  | @pi Γ A F G _ _ _ _ relF relG _ _ _ derivG _ _ihF ihG =>
      rintro t u v
        ⟨f, g, d, d', funcF, funcG, feqg, ht, _hu, appEq₁⟩
        ⟨f₁, g₁, d₁, d₁', funcF₁, funcG₁, f₁eqg₁, _hu', hv, appEq₂⟩
      have hf₁g : f₁ = g :=
        whrDetStarTerm ⟨d₁.reduction, funcF₁.toWhnf⟩ ⟨d'.reduction, funcG.toWhnf⟩
      subst hf₁g
      refine ⟨f, g₁, d, d₁', funcF, funcG₁, eqrel.transTerm feqg f₁eqg₁, ht, hv,
        fun {ρ Δ a} hρ hΔ ha ↦ ?_⟩
      rcases appEq₁ hρ hΔ ha with ⟨s₁, hs₁, hfg⟩
      rcases appEq₂ hρ hΔ ha with ⟨s₂, hs₂, hgg₁⟩
      have hGAt₁ := derivG hρ hΔ ha s₁ hs₁
      have hGAt₂ := derivG hρ hΔ ha s₂ hs₂
      have hgg₁' : s₁.eqTerm (.app (wk ρ f₁) a) (.app (wk ρ g₁) a) :=
        (irrelLogRel hGAt₂ hGAt₁).2.2.mp hgg₁
      exact ⟨s₁, hs₁, ihG hρ hΔ ha s₁ hs₁ hfg hgg₁'⟩
  | @emb Γ A l' rel hlt hA =>
      intro t u v htu huv
      exact ihRec l' hlt hA htu huv

/-- Transitivity of reducible term equality (`transEqTerm`). -/
theorem transEqTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t u v : Term}
    (pA : RedType eqrel l Γ A)
    (htu : RedTermEq pA t u) (huv : RedTermEq pA u v) : RedTermEq pA t v := by
  rcases htu with ⟨rel, hA, htu⟩
  rcases huv with ⟨rel', hA', huv⟩
  have huv_rel : rel.eqTerm u v := (irrelLogRel hA' hA).2.2.mp huv
  have h0 : ∀ {Γ A rel t u v},
      LogRelAt eqrel .zero Γ A rel → rel.eqTerm t u → rel.eqTerm u v → rel.eqTerm t v :=
    fun hA₀ htu₀ huv₀ ↦
      transEqTerm_step (l := .zero) (fun _ hlt ↦ nomatch hlt) (fun _ hlt ↦ nomatch hlt)
        hA₀ htu₀ huv₀
  cases l with
  | zero => exact ⟨rel, hA, h0 hA htu huv_rel⟩
  | one =>
      refine ⟨rel, hA, transEqTerm_step (l := .one) ?_ ?_ hA htu huv_rel⟩
      · intro _ hlt _ _ _ _ _ _ hA₀ htu₀ huv₀
        cases hlt
        exact h0 hA₀ htu₀ huv₀
      · intro _ hlt _ _ _ _ _ _ _ hA₀ hB₀ hB₀' hAB₀ hBC₀
        cases hlt
        have hBC₀' := (irrelLogRel (l₁ := .zero) (l₂ := .zero) hB₀' hB₀).1.mp hBC₀
        exact transLogRelAt (l₁ := .zero) (l₂ := .zero) hA₀ hB₀ hAB₀ hBC₀'

/-!
## Universe Properties (`Definition/LogicalRelation/Properties/Universe.agda`)
-/

/-- Reducible terms of type `U` are reducible types at level `⁰` (`univEq`). -/
theorem univEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (pU : RedType eqrel l Γ .univ) (hA : RedTerm pU A) : RedType eqrel .zero Γ A := by
  rcases hA with ⟨rel, hU, hA⟩
  cases logRelShape_of_LogRelAt hU with
  | @U l' l₀ _ hUAt =>
      rcases hA with ⟨A₀, _d, _typeA, _AeqA, relA, hrelA⟩
      cases hUAt.lt
      exact ⟨relA, hrelA⟩
  | nat D => cases whnfRedStar D.reduction .univ
  | ne neA =>
      have h := whnfRedStar neA.D.reduction .univ
      subst h
      cases neA.neK
  | pi D => cases whnfRedStar D.reduction .univ

/-- Reducible term equality of type `U` is reducible type equality (`univEqEq`). -/
theorem univEqEq {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A B : Term}
    (pU : RedType eqrel l Γ .univ) (pA : RedType eqrel l' Γ A)
    (hAB : RedTermEq pU A B) : RedEq pA B := by
  rcases hAB with ⟨rel, hU, hAB⟩
  cases logRelShape_of_LogRelAt hU with
  | @U l₁ l₀ _ hUAt =>
      rcases hAB with ⟨A₀, B₀, _d, _d', _typeA, _typeB, _AeqB, relt, ht, _hu, tequ⟩
      cases hUAt.lt
      exact irrelevanceEq ⟨relt, ht⟩ pA ⟨relt, ht, tequ⟩
  | nat D => cases whnfRedStar D.reduction .univ
  | ne neA =>
      have h := whnfRedStar neA.D.reduction .univ
      subst h
      cases neA.neK
  | pi D => cases whnfRedStar D.reduction .univ

/-!
## Neutral Properties (`Definition/LogicalRelation/Properties/Neutral.agda`)
-/

/-- Neutral reflexive types are reducible (`neu`). -/
theorem neu {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (neA : Neutral A) (hA : TypeWf Γ A) (AeqA : eqrel.NeEqRel Γ A A .univ) :
    RedType eqrel l Γ A :=
  RedType.ne ⟨A, idRedWf hA, neA, AeqA⟩

/-- Neutrally equal types are of reducible equality (`neuEq`). -/
theorem neuEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B : Term}
    (pA : RedType eqrel l Γ A) (neA : Neutral A) (neB : Neutral B)
    (hA : TypeWf Γ A) (hB : TypeWf Γ B) (AeqB : eqrel.NeEqRel Γ A B .univ) :
    RedEq pA B := by
  have neA_at : RedNeAt eqrel Γ A A := elimNeAt' (.refl hA) neA pA
  have hAt : LogRelAt eqrel l Γ A (RedNeRel eqrel Γ A) := .ne neA_at
  exact (RedEq_of_LogRelAt hAt pA).mpr ⟨B, idRedWf hB, neB, AeqB⟩

/-- Single-level neutral term / neutral term equality reflection step. -/
theorem neuLogRel_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A rel},
      logRelRec eqrel l l' hlt Γ A rel →
      (∀ {n}, Neutral n → HasType Γ n A → eqrel.NeEqRel Γ n n A → rel.hasTerm n) ∧
      (∀ {n n'}, Neutral n → Neutral n' → HasType Γ n A → HasType Γ n' A →
        eqrel.NeEqRel Γ n n' A → rel.eqTerm n n'))
    {Γ : Context} {A : Term} {rel : RedRel}
    (hA : LogRelAt eqrel l Γ A rel) :
    (∀ {n}, Neutral n → HasType Γ n A → eqrel.NeEqRel Γ n n A → rel.hasTerm n) ∧
    (∀ {n n'}, Neutral n → Neutral n' → HasType Γ n A → HasType Γ n' A →
      eqrel.NeEqRel Γ n n' A → rel.eqTerm n n') := by
  induction hA with
  | @U Γ l' hU =>
      refine ⟨?_, ?_⟩
      · intro n neN hn n_eq_n
        cases hU.lt
        exact ⟨n, idRedTermWf hn, .neutral neN, eqrel.neToTerm n_eq_n,
          ⟨RedNeRel eqrel Γ n, .ne ⟨idRedWf (.fromUniv hn), neN, n_eq_n⟩⟩⟩
      · intro n n' neN neN' hn hn' n_eq_n'
        cases hU.lt
        have n_eq_n := eqrel.transNe n_eq_n' (eqrel.symmNe n_eq_n')
        have n'_eq_n' := eqrel.transNe (eqrel.symmNe n_eq_n') n_eq_n'
        have hn_rel : LogRelAt eqrel .zero Γ n (RedNeRel eqrel Γ n) :=
          .ne ⟨idRedWf (.fromUniv hn), neN, n_eq_n⟩
        have hn'_rel : LogRelAt eqrel .zero Γ n' (RedNeRel eqrel Γ n') :=
          .ne ⟨idRedWf (.fromUniv hn'), neN', n'_eq_n'⟩
        exact ⟨n, n', idRedTermWf hn, idRedTermWf hn',
          .neutral neN, .neutral neN', eqrel.neToTerm n_eq_n',
          RedNeRel eqrel Γ n, hn_rel, ⟨RedNeRel eqrel Γ n', hn'_rel⟩,
          ⟨n', idRedWf (.fromUniv hn'), neN', n_eq_n'⟩⟩
  | @nat Γ A D =>
      have hANat : TypeEq Γ A .nat := subsetStar D.reduction
      refine ⟨?_, ?_⟩
      · intro n neN hn n_eq_n
        have hn' : HasType Γ n .nat := .conv hn hANat
        have n_eq_n' : eqrel.NeEqRel Γ n n .nat := eqrel.convNe n_eq_n hANat
        exact .mk n n (idRedTermWf hn') (eqrel.neToTerm n_eq_n')
          (.ne ⟨neN, hn', n_eq_n'⟩)
      · intro n n' neN neN' hn hn' n_eq_n'
        have hn_nat : HasType Γ n .nat := .conv hn hANat
        have hn'_nat : HasType Γ n' .nat := .conv hn' hANat
        have n_eq_n'_nat : eqrel.NeEqRel Γ n n' .nat := eqrel.convNe n_eq_n' hANat
        exact .mk n n' n n' (idRedTermWf hn_nat) (idRedTermWf hn'_nat)
          (eqrel.neToTerm n_eq_n'_nat) (.ne ⟨neN, neN', n_eq_n'_nat⟩)
  | @ne Γ A K neA =>
      have hAK : TypeEq Γ A K := subsetStar neA.D.reduction
      refine ⟨?_, ?_⟩
      · intro n neN hn n_eq_n
        have hn' : HasType Γ n K := .conv hn hAK
        exact ⟨n, idRedTermWf hn', ⟨neN, hn', eqrel.convNe n_eq_n hAK⟩⟩
      · intro n n' neN neN' hn hn' n_eq_n'
        exact ⟨n, n', idRedTermWf (.conv hn hAK), idRedTermWf (.conv hn' hAK),
          ⟨neN, neN', eqrel.convNe n_eq_n' hAK⟩⟩
  | @pi Γ A F G D _hF _hG _AeqA relF relG _hF_ex derivF hG_ex derivG Gext _ihF ihG =>
      have hAPi : TypeEq Γ A (.pi F G) := subsetStar D.reduction
      have hNeuTerm : ∀ {n}, Neutral n → HasType Γ n A → eqrel.NeEqRel Γ n n A →
          RedPiTerm eqrel Γ F G relF relG n := by
        intro n neN hn n_eq_n
        have hnPi : HasType Γ n (.pi F G) := .conv hn hAPi
        have neqPi : eqrel.NeEqRel Γ n n (.pi F G) := eqrel.convNe n_eq_n hAPi
        refine ⟨n, idRedTermWf hnPi, .neutral neN, eqrel.neToTerm neqPi,
          fun {ρ Δ a b} hρ hΔ ha hb hab ↦ ?_,
          fun {ρ Δ a} hρ hΔ ha ↦ ?_⟩
        · rcases ha with ⟨r_a, hr_a, ha_term⟩
          rcases hb with ⟨r_b, hr_b, hb_term⟩
          rcases hab with ⟨r_ab, hr_ab, hab_eq⟩
          have hFAt_a := derivF hρ hΔ r_a hr_a
          have hFAt_b := derivF hρ hΔ r_b hr_b
          have hFAt_ab := derivF hρ hΔ r_ab hr_ab
          have ha_syn : HasType Δ a (wk ρ F) :=
            escapeTerm ⟨r_a, hFAt_a⟩ ⟨r_a, hFAt_a, ha_term⟩
          have hb_syn : HasType Δ b (wk ρ F) :=
            escapeTerm ⟨r_b, hFAt_b⟩ ⟨r_b, hFAt_b, hb_term⟩
          have hab_syn : eqrel.TermEqRel Δ a b (wk ρ F) :=
            escapeTermEq ⟨r_ab, hFAt_ab⟩ ⟨r_ab, hFAt_ab, hab_eq⟩
          rcases hG_ex hρ hΔ ⟨r_a, hr_a, ha_term⟩ with ⟨s_a, hs_a⟩
          rcases hG_ex hρ hΔ ⟨r_b, hr_b, hb_term⟩ with ⟨s_b, hs_b⟩
          have hGAt_a := derivG hρ hΔ ⟨r_a, hr_a, ha_term⟩ s_a hs_a
          have hGAt_b := derivG hρ hΔ ⟨r_b, hr_b, hb_term⟩ s_b hs_b
          have hGext := Gext hρ hΔ ⟨r_a, hr_a, ha_term⟩ ⟨r_b, hr_b, hb_term⟩ ⟨r_ab, hr_ab, hab_eq⟩
          rcases hGext with ⟨s_ext, hs_ext, hGaGb⟩
          have hGAt_ext := derivG hρ hΔ ⟨r_a, hr_a, ha_term⟩ s_ext hs_ext
          have hGbGa : s_b.eqType (subst0 (wk (.lift ρ) G) a) :=
            symLogRelAt hGAt_ext hGAt_b hGaGb
          have hGbGa_syn : TypeEq Δ (subst0 (wk (.lift ρ) G) b) (subst0 (wk (.lift ρ) G) a) :=
            eqrel.typeToEq (escapeEq ⟨s_b, hGAt_b⟩ ⟨s_b, hGAt_b, hGbGa⟩)
          have hρn : HasType Δ (wk ρ n) (.pi (wk ρ F) (wk (.lift ρ) G)) :=
            wkHasType hρ hΔ hnPi
          have hAppA : HasType Δ (.app (wk ρ n) a) (subst0 (wk (.lift ρ) G) a) :=
            .app hρn ha_syn
          have hAppB : HasType Δ (.app (wk ρ n) b) (subst0 (wk (.lift ρ) G) a) :=
            .conv (.app hρn hb_syn) hGbGa_syn
          have hNeApp : eqrel.NeEqRel Δ (.app (wk ρ n) a) (.app (wk ρ n) b)
              (subst0 (wk (.lift ρ) G) a) :=
            eqrel.appCong (eqrel.wkNe hρ hΔ neqPi) hab_syn
          exact ⟨s_a, hs_a,
            (ihG hρ hΔ ⟨r_a, hr_a, ha_term⟩ s_a hs_a).2
              (.app (neN.wk ρ)) (.app (neN.wk ρ))
              hAppA hAppB hNeApp⟩
        · rcases ha with ⟨r_a, hr_a, ha_term⟩
          have hFAt_a := derivF hρ hΔ r_a hr_a
          have ha_syn : HasType Δ a (wk ρ F) :=
            escapeTerm ⟨r_a, hFAt_a⟩ ⟨r_a, hFAt_a, ha_term⟩
          have haa_syn : eqrel.TermEqRel Δ a a (wk ρ F) :=
            escapeTermEq ⟨r_a, hFAt_a⟩ (reflEqTerm ⟨r_a, hFAt_a⟩ ⟨r_a, hFAt_a, ha_term⟩)
          rcases hG_ex hρ hΔ ⟨r_a, hr_a, ha_term⟩ with ⟨s_a, hs_a⟩
          have hρn : HasType Δ (wk ρ n) (.pi (wk ρ F) (wk (.lift ρ) G)) :=
            wkHasType hρ hΔ hnPi
          have hAppA : HasType Δ (.app (wk ρ n) a) (subst0 (wk (.lift ρ) G) a) :=
            .app hρn ha_syn
          have hNeApp : eqrel.NeEqRel Δ (.app (wk ρ n) a) (.app (wk ρ n) a)
              (subst0 (wk (.lift ρ) G) a) :=
            eqrel.appCong (eqrel.wkNe hρ hΔ neqPi) haa_syn
          exact ⟨s_a, hs_a,
            (ihG hρ hΔ ⟨r_a, hr_a, ha_term⟩ s_a hs_a).1
              (.app (neN.wk ρ)) hAppA hNeApp⟩
      refine ⟨hNeuTerm, ?_⟩
      intro n n' neN neN' hn hn' n_eq_n'
      have hnPi : HasType Γ n (.pi F G) := .conv hn hAPi
      have hn'Pi : HasType Γ n' (.pi F G) := .conv hn' hAPi
      have neqPi : eqrel.NeEqRel Γ n n' (.pi F G) := eqrel.convNe n_eq_n' hAPi
      have n_eq_n : eqrel.NeEqRel Γ n n A :=
        eqrel.transNe n_eq_n' (eqrel.symmNe n_eq_n')
      have n'_eq_n' : eqrel.NeEqRel Γ n' n' A :=
        eqrel.transNe (eqrel.symmNe n_eq_n') n_eq_n'
      refine ⟨n, n', idRedTermWf hnPi, idRedTermWf hn'Pi,
        .neutral neN, .neutral neN', eqrel.neToTerm neqPi,
        hNeuTerm neN hn n_eq_n, hNeuTerm neN' hn' n'_eq_n',
        fun {ρ Δ a} hρ hΔ ha ↦ ?_⟩
      rcases ha with ⟨r_a, hr_a, ha_term⟩
      have hFAt_a := derivF hρ hΔ r_a hr_a
      have ha_syn : HasType Δ a (wk ρ F) :=
        escapeTerm ⟨r_a, hFAt_a⟩ ⟨r_a, hFAt_a, ha_term⟩
      have haa_syn : eqrel.TermEqRel Δ a a (wk ρ F) :=
        escapeTermEq ⟨r_a, hFAt_a⟩ (reflEqTerm ⟨r_a, hFAt_a⟩ ⟨r_a, hFAt_a, ha_term⟩)
      rcases hG_ex hρ hΔ ⟨r_a, hr_a, ha_term⟩ with ⟨s_a, hs_a⟩
      have hρn : HasType Δ (wk ρ n) (.pi (wk ρ F) (wk (.lift ρ) G)) := wkHasType hρ hΔ hnPi
      have hρn' : HasType Δ (wk ρ n') (.pi (wk ρ F) (wk (.lift ρ) G)) := wkHasType hρ hΔ hn'Pi
      exact ⟨s_a, hs_a,
        (ihG hρ hΔ ⟨r_a, hr_a, ha_term⟩ s_a hs_a).2
          (.app (neN.wk ρ)) (.app (neN'.wk ρ))
          (.app hρn ha_syn) (.app hρn' ha_syn)
          (eqrel.appCong (eqrel.wkNe hρ hΔ neqPi) haa_syn)⟩
  | @emb Γ A l' rel hlt hA =>
      exact ihRec l' hlt hA

theorem neuLogRelAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term} {rel : RedRel}
    (hA : LogRelAt eqrel l Γ A rel) :
    (∀ {n}, Neutral n → HasType Γ n A → eqrel.NeEqRel Γ n n A → rel.hasTerm n) ∧
    (∀ {n n'}, Neutral n → Neutral n' → HasType Γ n A → HasType Γ n' A →
      eqrel.NeEqRel Γ n n' A → rel.eqTerm n n') := by
  have h0 : ∀ {Γ A rel},
      LogRelAt eqrel .zero Γ A rel →
      (∀ {n}, Neutral n → HasType Γ n A → eqrel.NeEqRel Γ n n A → rel.hasTerm n) ∧
      (∀ {n n'}, Neutral n → Neutral n' → HasType Γ n A → HasType Γ n' A →
        eqrel.NeEqRel Γ n n' A → rel.eqTerm n n') :=
    fun hA₀ ↦ neuLogRel_step (l := .zero) (fun _ hlt ↦ nomatch hlt) hA₀
  cases l with
  | zero => exact h0 hA
  | one =>
      exact neuLogRel_step (l := .one)
        (fun _ hlt _ _ _ hA₀ ↦ by cases hlt; exact h0 hA₀) hA

/-- Neutral reflexive terms are reducible (`neuTerm`). -/
theorem neuTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A n : Term}
    (pA : RedType eqrel l Γ A) (neN : Neutral n)
    (hn : HasType Γ n A) (n_eq_n : eqrel.NeEqRel Γ n n A) : RedTerm pA n := by
  rcases pA with ⟨rel, hA⟩
  exact ⟨rel, hA, (neuLogRelAt hA).1 neN hn n_eq_n⟩

/-- Neutrally equal terms are of reducible equality (`neuEqTerm`). -/
theorem neuEqTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A n n' : Term}
    (pA : RedType eqrel l Γ A) (neN : Neutral n) (neN' : Neutral n')
    (hn : HasType Γ n A) (hn' : HasType Γ n' A)
    (n_eq_n' : eqrel.NeEqRel Γ n n' A) : RedTermEq pA n n' := by
  rcases pA with ⟨rel, hA⟩
  exact ⟨rel, hA, (neuLogRelAt hA).2 neN neN' hn hn' n_eq_n'⟩

/-!
## Weak Head Expansion (`Definition/LogicalRelation/Properties/Reduction.agda`)
-/

/-- Single-level weak-head expansion step for `LogRelAt` types (`redSubst*`). -/
theorem redSubstStar_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A B rel},
      TypeStar Γ A B → logRelRec eqrel l l' hlt Γ B rel →
      logRelRec eqrel l l' hlt Γ A rel ∧ rel.eqType B)
    {Γ : Context} {B : Term} {rel : RedRel}
    (hB : LogRelAt eqrel l Γ B rel) :
    ∀ {A : Term}, TypeStar Γ A B → LogRelAt eqrel l Γ A rel ∧ rel.eqType B := by
  induction hB with
  | @U Γ l' hU =>
      intro A D
      have hAU : A = .univ := redUStar D
      subst hAU
      exact ⟨.U hU, rfl⟩
  | @nat Γ B D' =>
      intro A D
      have hA : TypeWf Γ A := redFirstStar D
      exact ⟨.nat ⟨hA, D'.target, D.trans D'.reduction⟩, D'.reduction⟩
  | @ne Γ B K neB =>
      intro A D
      have hA : TypeWf Γ A := redFirstStar D
      exact ⟨.ne ⟨⟨hA, neB.D.target, D.trans neB.D.reduction⟩, neB.neK, neB.KeqK⟩,
        ⟨K, neB.D, neB.neK, neB.KeqK⟩⟩
  | @pi Γ B F G D' hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext _ihF _ihG =>
      intro A D
      have hA : TypeWf Γ A := redFirstStar D
      refine ⟨.pi ⟨hA, D'.target, D.trans D'.reduction⟩
          hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext,
        ⟨F, G, D'.reduction, AeqA,
          fun {ρ Δ} hρ hΔ ↦ ?_,
          fun {ρ Δ a} hρ hΔ ha ↦ ?_⟩⟩
      · rcases hF_ex hρ hΔ with ⟨r, hr⟩
        exact ⟨r, hr, (reflLogRelAt (derivF hρ hΔ r hr)).1⟩
      · rcases hG_ex hρ hΔ ha with ⟨s, hs⟩
        exact ⟨s, hs, (reflLogRelAt (derivG hρ hΔ ha s hs)).1⟩
  | @emb Γ B l' rel hlt hB =>
      intro A D
      rcases ihRec l' hlt D hB with ⟨hA, hEq⟩
      exact ⟨.emb hlt hA, hEq⟩

theorem redSubstStarAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B : Term} {rel : RedRel}
    (D : TypeStar Γ A B) (hB : LogRelAt eqrel l Γ B rel) :
    LogRelAt eqrel l Γ A rel ∧ rel.eqType B := by
  have h0 : ∀ {Γ A B rel}, TypeStar Γ A B → LogRelAt eqrel .zero Γ B rel →
      LogRelAt eqrel .zero Γ A rel ∧ rel.eqType B :=
    fun D₀ hB₀ ↦ redSubstStar_step (l := .zero) (fun _ hlt ↦ nomatch hlt) hB₀ D₀
  cases l with
  | zero => exact h0 D hB
  | one =>
      exact redSubstStar_step (l := .one)
        (fun _ hlt _ _ _ _ D₀ hB₀ ↦ by cases hlt; exact h0 D₀ hB₀) hB D

/-- Weak head expansion of reducible types (`redSubst*`). -/
theorem redSubstStar {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B : Term}
    (D : TypeStar Γ A B) (pB : RedType eqrel l Γ B) :
    ∃ (pA : RedType eqrel l Γ A), RedEq pA B := by
  rcases pB with ⟨rel, hB⟩
  rcases redSubstStarAt D hB with ⟨hA, hEq⟩
  exact ⟨⟨rel, hA⟩, ⟨rel, hA, hEq⟩⟩

/-- Weak head expansion of reducible terms (`redSubst*Term`). -/
theorem redSubstStarTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t u : Term}
    (d_tu : Star Γ t u A) (pA : RedType eqrel l Γ A) (hu : RedTerm pA u) :
    RedTerm pA t ∧ RedTermEq pA t u := by
  rcases hu with ⟨rel, hA, hu⟩
  cases logRelShape_of_LogRelAt hA with
  | @U l' l₀ _ hU =>
      rcases hu with ⟨A₀, d, typeA, AeqA, rel_u, hrel_u⟩
      cases hU.lt
      have ht_wf : HasType Γ t .univ := redFirstStarTerm d_tu
      have d' : StarWf Γ t A₀ .univ := ⟨ht_wf, d.target, d_tu.trans d.reduction⟩
      have ⟨hrel_t, hEq_tu⟩ := redSubstStarAt (.fromUniv d_tu) hrel_u
      exact ⟨⟨_, hA, ⟨A₀, d', typeA, AeqA, ⟨rel_u, hrel_t⟩⟩⟩,
        ⟨_, hA, ⟨A₀, A₀, d', d, typeA, typeA, AeqA, rel_u, hrel_t, ⟨rel_u, hrel_u⟩, hEq_tu⟩⟩⟩
  | nat D =>
      rcases hu with ⟨_, n, d, neqn, prop⟩
      have hANat : TypeEq Γ A .nat := subsetStar D.reduction
      have ht_nat : HasType Γ t .nat := .conv (redFirstStarTerm d_tu) hANat
      have d_tu_nat : Star Γ t u .nat := d_tu.conv hANat
      have d' : StarWf Γ t n .nat := ⟨ht_nat, d.target, d_tu_nat.trans d.reduction⟩
      exact ⟨⟨_, hA, .mk t n d' neqn prop⟩,
        ⟨_, hA, .mk t u n n d' d neqn (reflNaturalProp prop)⟩⟩
  | @ne _ _ K neA =>
      rcases hu with ⟨k, d, nf⟩
      have hAK : TypeEq Γ A K := subsetStar neA.D.reduction
      have ht_K : HasType Γ t K := .conv (redFirstStarTerm d_tu) hAK
      have d_tu_K : Star Γ t u K := d_tu.conv hAK
      have d' : StarWf Γ t k K := ⟨ht_K, d.target, d_tu_K.trans d.reduction⟩
      exact ⟨⟨_, hA, ⟨k, d', nf⟩⟩,
        ⟨_, hA, ⟨k, k, d', d, ⟨nf.neK, nf.neK, nf.keqk⟩⟩⟩⟩
  | @pi l₀ _ _ F G D _hF _hG _AeqA relF relG _hF_ex _derivF _hG_ex derivG _Gext =>
      rcases hu with ⟨f, d, funcF, feqf, appEq, appTerm⟩
      have hAPi : TypeEq Γ A (.pi F G) := subsetStar D.reduction
      have ht_Pi : HasType Γ t (.pi F G) := .conv (redFirstStarTerm d_tu) hAPi
      have d_tu_Pi : Star Γ t u (.pi F G) := d_tu.conv hAPi
      have d' : StarWf Γ t f (.pi F G) := ⟨ht_Pi, d.target, d_tu_Pi.trans d.reduction⟩
      have ht_PiTerm : RedPiTerm eqrel Γ F G relF relG t :=
        ⟨f, d', funcF, feqf, appEq, appTerm⟩
      have hu_PiTerm : RedPiTerm eqrel Γ F G relF relG u :=
        ⟨f, d, funcF, feqf, appEq, appTerm⟩
      refine ⟨⟨_, hA, ht_PiTerm⟩,
        ⟨_, hA, ⟨f, f, d', d, funcF, funcF, feqf, ht_PiTerm, hu_PiTerm,
          fun {ρ Δ a} hρ hΔ ha ↦ ?_⟩⟩⟩
      rcases appTerm hρ hΔ ha with ⟨s, hs, hfa⟩
      exact ⟨s, hs, (reflLogRelAt (derivG hρ hΔ ha s hs)).2 hfa⟩

/-- Single-step weak head expansion of reducible types (`redSubst`). -/
theorem redSubst {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B : Term}
    (hAB : TypeStep Γ A B) (pB : RedType eqrel l Γ B) :
    ∃ (pA : RedType eqrel l Γ A), RedEq pA B :=
  redSubstStar (.step hAB (.refl (escape pB))) pB

/-- Single-step weak head expansion of reducible terms (`redSubstTerm`). -/
theorem redSubstTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t u : Term}
    (htu : Step Γ t u A) (pA : RedType eqrel l Γ A) (hu : RedTerm pA u) :
    RedTerm pA t ∧ RedTermEq pA t u :=
  redSubstStarTerm (.step htu (.refl (escapeTerm pA hu))) pA hu

/-!
## Successor Properties (`Definition/LogicalRelation/Properties/Successor.agda`)
-/

/-- Reducible natural numbers construct reducible successors (`sucTerm`). -/
theorem sucTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {n : Term}
    (pNat : RedType eqrel l Γ .nat) (hn : RedTerm pNat n) : RedTerm pNat (.succ n) := by
  have D : RedNat Γ .nat := elimNat pNat
  have hAt : LogRelAt eqrel l Γ .nat (RedNatRel eqrel Γ) := .nat D
  have hn' : RedNatTerm eqrel Γ n := (RedTerm_of_LogRelAt hAt pNat).mp hn
  cases hn' with
  | mk _ k d keqk prop =>
      have natK := natural_of_NaturalProp prop
      have hSuccEq : eqrel.TermEqRel Γ (.succ n) (.succ n) .nat :=
        eqrel.succCong (eqrel.redTerm D.reduction d.reduction d.reduction
          .nat natK.toWhnf natK.toWhnf keqk)
      exact (RedTerm_of_LogRelAt hAt pNat).mpr
        (.mk (.succ n) (.succ n) (idRedTermWf (.succ d.source))
          hSuccEq (.suc (.mk n k d keqk prop)))

/-- Reducible natural number equality constructs reducible successor equality (`sucEqTerm`). -/
theorem sucEqTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {n n' : Term}
    (pNat : RedType eqrel l Γ .nat) (hnn' : RedTermEq pNat n n') :
    RedTermEq pNat (.succ n) (.succ n') := by
  have D : RedNat Γ .nat := elimNat pNat
  have hAt : LogRelAt eqrel l Γ .nat (RedNatRel eqrel Γ) := .nat D
  have hnn'' : RedNatTermEq eqrel Γ n n' := (RedTermEq_of_LogRelAt hAt pNat).mp hnn'
  cases hnn'' with
  | mk _ _ k k' d d' keqk' prop =>
      have ⟨natK, natK'⟩ := split_of_NaturalEqProp prop
      have hSuccEq : eqrel.TermEqRel Γ (.succ n) (.succ n') .nat :=
        eqrel.succCong (eqrel.redTerm D.reduction d.reduction d'.reduction
          .nat natK.toWhnf natK'.toWhnf keqk')
      exact (RedTermEq_of_LogRelAt hAt pNat).mpr
        (.mk (.succ n) (.succ n') (.succ n) (.succ n')
          (idRedTermWf (.succ d.source)) (idRedTermWf (.succ d'.source))
          hSuccEq (.suc (.mk n n' k k' d d' keqk' prop)))

/-!
## Application of Reducible Terms (`Definition/LogicalRelation/Application.agda`)
-/

/-- Application of reducible terms (`appTerm`). -/
theorem appTerm {eqrel : EqRelSet} {l l' l'' : TypeLevel} {Γ : Context} {F G t u : Term}
    (pF : RedType eqrel l'' Γ F)
    (pGu : RedType eqrel l' Γ (subst0 G u))
    (pPi : RedType eqrel l Γ (.pi F G))
    (ht : RedTerm pPi t)
    (hu : RedTerm pF u) :
    RedTerm pGu (.app t u) := by
  rcases elimPiAt' (.refl (escape pPi)) pPi with ⟨l₀, piA⟩
  have hAt : LogRelAt eqrel l₀ Γ (.pi F G)
      (RedPiRel eqrel Γ F G
        (fun ρ Δ rel ↦ LogRelAt eqrel l₀ Δ (wk ρ F) rel)
        (fun ρ Δ a rel ↦ LogRelAt eqrel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel)) :=
    .pi piA.D piA.hF piA.hG piA.AeqA
      (fun ρ Δ rel ↦ LogRelAt eqrel l₀ Δ (wk ρ F) rel)
      (fun ρ Δ a rel ↦ LogRelAt eqrel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel)
      piA.redF (fun _ _ _ h ↦ h) piA.redG (fun _ _ _ _ h ↦ h) piA.Gext
  have htPi := (RedTerm_of_LogRelAt hAt ⟨_, hAt⟩).mp (irrelevanceTerm pPi ⟨_, hAt⟩ ht)
  rcases htPi with ⟨f, d, _funcF, _feqf, _appEq, hAppTerm⟩
  have hΓ : CtxWf Γ := wfType piA.hF
  have hu' : RedTerm (piA.redF .id hΓ) u :=
    irrelevanceTerm' (wk_id F).symm pF (piA.redF .id hΓ) hu
  have hfu : RedTerm (piA.redG .id hΓ hu') (.app (wk .id f) u) :=
    hAppTerm .id hΓ hu'
  have hGeq : subst0 (wk (.lift .id) G) u = subst0 G u := by
    rw [wk_lift_id]
  have hfeq : Term.app (wk .id f) u = Term.app f u := by
    rw [wk_id]
  have hfu' : RedTerm pGu (.app f u) :=
    irrelevanceTerm'' hGeq hfeq (piA.redG .id hΓ hu') pGu hfu
  have hu_syn : HasType Γ u F := escapeTerm pF hu
  exact (redSubstStarTerm (d.reduction.app hu_syn) pGu hfu').1

/-- Application congruence of reducible terms (`app-congTerm`). -/
theorem appCongTerm {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {F G t t' u u' : Term}
    (pF : RedType eqrel l' Γ F)
    (pGu : RedType eqrel l' Γ (subst0 G u))
    (pPi : RedType eqrel l Γ (.pi F G))
    (htt' : RedTermEq pPi t t')
    (hu : RedTerm pF u)
    (hu' : RedTerm pF u')
    (huu' : RedTermEq pF u u') :
    RedTermEq pGu (.app t u) (.app t' u') := by
  rcases elimPiAt' (.refl (escape pPi)) pPi with ⟨l₀, piA⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ rel ↦ LogRelAt eqrel l₀ Δ (wk ρ F) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ a rel ↦ LogRelAt eqrel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel
  have hAt : LogRelAt eqrel l₀ Γ (.pi F G) (RedPiRel eqrel Γ F G relF₀ relG₀) :=
    .pi piA.D piA.hF piA.hG piA.AeqA relF₀ relG₀
      piA.redF (fun _ _ _ h ↦ h) piA.redG (fun _ _ _ _ h ↦ h) piA.Gext
  have pPi₀ : RedType eqrel l₀ Γ (.pi F G) := ⟨_, hAt⟩
  have htt'Pi := (RedTermEq_of_LogRelAt hAt pPi₀).mp (irrelevanceEqTerm pPi pPi₀ htt')
  rcases htt'Pi with ⟨f, g, d, d', funcF, funcG, _feqg, ht_pi, ht'_pi, hAppEq⟩
  rcases ht_pi with ⟨f', d'', funcF', feqf', appEq_f', appTerm_f'⟩
  rcases ht'_pi with ⟨g', d''', funcG', geqg', appEq_g', appTerm_g'⟩
  have hff' : f = f' :=
    whrDetStarTerm ⟨d.reduction, funcF.toWhnf⟩ ⟨d''.reduction, funcF'.toWhnf⟩
  have hgg' : g = g' :=
    whrDetStarTerm ⟨d'.reduction, funcG.toWhnf⟩ ⟨d'''.reduction, funcG'.toWhnf⟩
  subst hff' hgg'
  have hΓ : CtxWf Γ := wfType piA.hF
  have hu_id : RedTerm (piA.redF .id hΓ) u :=
    irrelevanceTerm' (wk_id F).symm pF (piA.redF .id hΓ) hu
  have hu'_id : RedTerm (piA.redF .id hΓ) u' :=
    irrelevanceTerm' (wk_id F).symm pF (piA.redF .id hΓ) hu'
  have huu'_id : RedTermEq (piA.redF .id hΓ) u u' :=
    irrelevanceEqTerm' (wk_id F).symm pF (piA.redF .id hΓ) huu'
  have hGeq_u : subst0 (wk (.lift .id) G) u = subst0 G u := by rw [wk_lift_id]
  have hGeq_u' : subst0 (wk (.lift .id) G) u' = subst0 G u' := by rw [wk_lift_id]
  have pGu' : RedType eqrel l₀ Γ (subst0 G u') :=
    irrelevance' hGeq_u' (piA.redG .id hΓ hu'_id)
  have hGu_eq_Gu' : RedEq pGu (subst0 G u') :=
    irrelevanceEq'' hGeq_u hGeq_u' (piA.redG .id hΓ hu_id) pGu
      (piA.Gext .id hΓ hu_id hu'_id huu'_id)
  have hf_term : RedTerm pPi₀ f :=
    ⟨_, hAt, ⟨f, idRedTermWf d''.target, funcF', feqf', appEq_f', appTerm_f'⟩⟩
  have hg_term : RedTerm pPi₀ g :=
    ⟨_, hAt, ⟨g, idRedTermWf d'''.target, funcG', geqg', appEq_g', appTerm_g'⟩⟩
  have hfu : RedTerm pGu (.app f u) := appTerm pF pGu pPi₀ hf_term hu
  have hgu' : RedTerm pGu' (.app g u') := appTerm pF pGu' pPi₀ hg_term hu'
  have hfu_eq_gu : RedTermEq pGu (.app f u) (.app g u) :=
    irrelevanceEqTerm'' (by rw [wk_id]) (by rw [wk_id]) hGeq_u
      (piA.redG .id hΓ hu_id) pGu (hAppEq .id hΓ hu_id)
  have hgu_eq_gu' : RedTermEq pGu (.app g u) (.app g u') :=
    irrelevanceEqTerm'' (by rw [wk_id]) (by rw [wk_id]) hGeq_u
      (piA.redG .id hΓ hu_id) pGu (appEq_g' .id hΓ hu_id hu'_id huu'_id)
  have htu_eq_fu : RedTermEq pGu (.app t u) (.app f u) :=
    (redSubstStarTerm (d.reduction.app (escapeTerm pF hu)) pGu hfu).2
  have ht'u'_eq_gu' : RedTermEq pGu' (.app t' u') (.app g u') :=
    (redSubstStarTerm (d'.reduction.app (escapeTerm pF hu')) pGu' hgu').2
  have hgu'_eq_t'u' : RedTermEq pGu (.app g u') (.app t' u') :=
    convEqTerm₂ pGu pGu' hGu_eq_Gu' (symEqTerm pGu' ht'u'_eq_gu')
  exact transEqTerm pGu (transEqTerm pGu htu_eq_fu hfu_eq_gu)
    (transEqTerm pGu hgu_eq_gu' hgu'_eq_t'u')

end Abel2018


namespace Abel2018

/-!
# Substitution Validity and Logical Relation Introductions

This module translates:
- `Definition/LogicalRelation/Substitution.agda`
- `Definition/LogicalRelation/Substitution/Irrelevance.agda`
- `Definition/LogicalRelation/Substitution/Reflexivity.agda`
- `Definition/LogicalRelation/Substitution/Weakening.agda`
- `Definition/LogicalRelation/Substitution/Conversion.agda`
- `Definition/LogicalRelation/Substitution/MaybeEmbed.agda`
- `Definition/LogicalRelation/Substitution/Properties.agda`
- `Definition/LogicalRelation/Substitution/Escape.agda`
- `Definition/LogicalRelation/Substitution/Reducibility.agda`
- `Definition/LogicalRelation/Substitution/Reduction.agda`
- `Definition/LogicalRelation/Substitution/Introductions/Universe.agda`
- `Definition/LogicalRelation/Substitution/Introductions/Nat.agda`
- `Definition/LogicalRelation/Substitution/Introductions/SingleSubst.agda`
- `Definition/LogicalRelation/Substitution/Introductions/Pi.agda`
- `Definition/LogicalRelation/Substitution/Introductions/Application.agda`
-/

/-!
## Validity Judgments (`Definition/LogicalRelation/Substitution.agda`)
-/























/-!
## Projections and Constructors for `ValidSubst` and `ValidSubstEq`
-/

theorem ValidSubst.tail {eqrel : EqRelSet} {Δ : Context} {σ : Subst} {A : Term} {Γ : Context}
    (hσ : ValidSubst eqrel Δ σ (A :: Γ)) : ValidSubst eqrel Δ (tailSubst σ) Γ :=
  hσ.1

theorem ValidSubst.head {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} {σ : Subst}
    {A : Term} {Γ : Context}
    (hA : ValidType eqrel l Γ A) (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ (A :: Γ)) :
    RedTerm (hA hΔ hσ.1).red (headSubst σ) := by
  rcases hσ.2 with ⟨_, pA₀, hHead⟩
  exact irrelevanceTerm pA₀ (hA hΔ hσ.1).red hHead

theorem ValidSubst.cons {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} {σ : Subst}
    {A : Term} {Γ : Context}
    (hTail : ValidSubst eqrel Δ (tailSubst σ) Γ)
    (pA : RedType eqrel l Δ (subst (tailSubst σ) A))
    (hHead : RedTerm pA (headSubst σ)) :
    ValidSubst eqrel Δ σ (A :: Γ) :=
  ⟨hTail, l, pA, hHead⟩

theorem ValidSubstEq.tail {eqrel : EqRelSet} {Δ : Context} {σ σ' : Subst} {A : Term} {Γ : Context}
    (hσσ' : ValidSubstEq eqrel Δ σ σ' (A :: Γ)) :
    ValidSubstEq eqrel Δ (tailSubst σ) (tailSubst σ') Γ :=
  hσσ'.1

theorem ValidSubstEq.head {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} {σ σ' : Subst}
    {A : Term} {Γ : Context}
    (hA : ValidType eqrel l Γ A) (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ (A :: Γ))
    (hσσ' : ValidSubstEq eqrel Δ σ σ' (A :: Γ)) :
    RedTermEq (hA hΔ hσ.1).red (headSubst σ) (headSubst σ') := by
  rcases hσσ'.2 with ⟨_, pA₀, hHeadEq⟩
  exact irrelevanceEqTerm pA₀ (hA hΔ hσ.1).red hHeadEq

theorem ValidSubstEq.cons {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} {σ σ' : Subst}
    {A : Term} {Γ : Context}
    (hTailEq : ValidSubstEq eqrel Δ (tailSubst σ) (tailSubst σ') Γ)
    (pA : RedType eqrel l Δ (subst (tailSubst σ) A))
    (hHeadEq : RedTermEq pA (headSubst σ) (headSubst σ')) :
    ValidSubstEq eqrel Δ σ σ' (A :: Γ) :=
  ⟨hTailEq, l, pA, hHeadEq⟩

/-!
## Irrelevance (`Definition/LogicalRelation/Substitution/Irrelevance.agda`)
-/

theorem irrelevanceSubst {eqrel : EqRelSet} {σ : Subst} {Γ Δ : Context}
    (_hΓ _hΓ' : ValidCtx eqrel Γ) (_hΔ _hΔ' : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ) : ValidSubst eqrel Δ σ Γ :=
  hσ

theorem irrelevanceSubst' {eqrel : EqRelSet} {σ : Subst} {Γ Δ Δ' : Context}
    (heq : Δ = Δ') (hσ : ValidSubst eqrel Δ σ Γ) : ValidSubst eqrel Δ' σ Γ := by
  subst heq
  exact hσ

theorem irrelevanceSubstEq {eqrel : EqRelSet} {σ σ' : Subst} {Γ Δ : Context}
    (_hΓ _hΓ' : ValidCtx eqrel Γ) (_hΔ _hΔ' : CtxWf Δ)
    (_hσ _hσ' : ValidSubst eqrel Δ σ Γ)
    (hσσ' : ValidSubstEq eqrel Δ σ σ' Γ) : ValidSubstEq eqrel Δ σ σ' Γ :=
  hσσ'

theorem irrelevanceValid {eqrel : EqRelSet} {l : TypeLevel} {A : Term} {Γ : Context}
    (_hΓ _hΓ' : ValidCtx eqrel Γ)
    (hA : ValidType eqrel l Γ A) : ValidType eqrel l Γ A :=
  hA

/-- Irrelevance of valid types under lifting of equal context types (`irrelevanceLift`). -/
theorem irrelevanceLift {eqrel : EqRelSet} {l : TypeLevel} {A F H : Term} {Γ : Context}
    (hF : ValidType eqrel l Γ F)
    (hH : ValidType eqrel l Γ H)
    (hFH : ValidTypeEq hF H)
    (hA : ValidType eqrel l (F :: Γ) A) :
    ValidType eqrel l (H :: Γ) A := by
  intro Δ σ hΔ hσ
  have hTail : ValidSubst eqrel Δ (tailSubst σ) Γ := hσ.tail
  have hHeadH : RedTerm (hH hΔ hTail).red (headSubst σ) := hσ.head hH hΔ
  have hHeadF : RedTerm (hF hΔ hTail).red (headSubst σ) :=
    convTerm₂ (hF hΔ hTail).red (hH hΔ hTail).red (hFH hΔ hTail) hHeadH
  have hσF : ValidSubst eqrel Δ σ (F :: Γ) :=
    ValidSubst.cons hTail (hF hΔ hTail).red hHeadF
  refine ⟨(hA hΔ hσF).red, fun {σ'} hσ' hσσ' ↦ ?_⟩
  have hTail' : ValidSubst eqrel Δ (tailSubst σ') Γ := hσ'.tail
  have hHeadH' : RedTerm (hH hΔ hTail').red (headSubst σ') := hσ'.head hH hΔ
  have hHeadF' : RedTerm (hF hΔ hTail').red (headSubst σ') :=
    convTerm₂ (hF hΔ hTail').red (hH hΔ hTail').red (hFH hΔ hTail') hHeadH'
  have hσ'F : ValidSubst eqrel Δ σ' (F :: Γ) :=
    ValidSubst.cons hTail' (hF hΔ hTail').red hHeadF'
  have hHeadEqH : RedTermEq (hH hΔ hTail).red (headSubst σ) (headSubst σ') :=
    hσσ'.head hH hΔ hσ
  have hHeadEqF : RedTermEq (hF hΔ hTail).red (headSubst σ) (headSubst σ') :=
    convEqTerm₂ (hF hΔ hTail).red (hH hΔ hTail).red (hFH hΔ hTail) hHeadEqH
  have hσσ'F : ValidSubstEq eqrel Δ σ σ' (F :: Γ) :=
    ValidSubstEq.cons hσσ'.tail (hF hΔ hTail).red hHeadEqF
  exact (hA hΔ hσF).eq hσ'F hσσ'F

/-- Irrelevance of valid type equality (`irrelevanceEq`). -/
theorem irrelevanceValidEq {eqrel : EqRelSet} {l l' : TypeLevel} {A B : Term} {Γ : Context}
    (hA : ValidType eqrel l Γ A)
    (hA' : ValidType eqrel l' Γ A)
    (hAB : ValidTypeEq hA B) :
    ValidTypeEq hA' B := by
  intro Δ σ hΔ hσ
  exact irrelevanceEq (hA hΔ hσ).red (hA' hΔ hσ).red (hAB hΔ hσ)

/-- Irrelevance of valid terms (`irrelevanceTerm`). -/
theorem irrelevanceValidTerm {eqrel : EqRelSet} {l l' : TypeLevel} {A t : Term} {Γ : Context}
    (hA : ValidType eqrel l Γ A)
    (hA' : ValidType eqrel l' Γ A)
    (ht : ValidTerm hA t) :
    ValidTerm hA' t := by
  intro Δ σ hΔ hσ
  refine ⟨irrelevanceTerm (hA hΔ hσ).red (hA' hΔ hσ).red (ht hΔ hσ).term,
    fun hσ' hσσ' ↦ irrelevanceEqTerm (hA hΔ hσ).red (hA' hΔ hσ).red ((ht hΔ hσ).eq hσ' hσσ')⟩

/-- Irrelevance of valid terms with propositionally equal types (`irrelevanceTerm′`). -/
theorem irrelevanceValidTerm' {eqrel : EqRelSet} {l l' : TypeLevel} {A A' t : Term} {Γ : Context}
    (heq : A = A')
    (hA : ValidType eqrel l Γ A)
    (hA' : ValidType eqrel l' Γ A')
    (ht : ValidTerm hA t) :
    ValidTerm hA' t := by
  subst heq
  exact irrelevanceValidTerm hA hA' ht

/-- Irrelevance of valid terms under lifting of equal context types (`irrelevanceTermLift`). -/
theorem irrelevanceTermLift {eqrel : EqRelSet} {l : TypeLevel} {A F H t : Term} {Γ : Context}
    (hF : ValidType eqrel l Γ F)
    (hH : ValidType eqrel l Γ H)
    (hFH : ValidTypeEq hF H)
    (hA : ValidType eqrel l (F :: Γ) A)
    (ht : ValidTerm hA t) :
    ValidTerm (irrelevanceLift hF hH hFH hA) t := by
  intro Δ σ hΔ hσ
  have hTail : ValidSubst eqrel Δ (tailSubst σ) Γ := hσ.tail
  have hHeadH : RedTerm (hH hΔ hTail).red (headSubst σ) := hσ.head hH hΔ
  have hHeadF : RedTerm (hF hΔ hTail).red (headSubst σ) :=
    convTerm₂ (hF hΔ hTail).red (hH hΔ hTail).red (hFH hΔ hTail) hHeadH
  have hσF : ValidSubst eqrel Δ σ (F :: Γ) :=
    ValidSubst.cons hTail (hF hΔ hTail).red hHeadF
  refine ⟨(ht hΔ hσF).term, fun {σ'} hσ' hσσ' ↦ ?_⟩
  have hTail' : ValidSubst eqrel Δ (tailSubst σ') Γ := hσ'.tail
  have hHeadH' : RedTerm (hH hΔ hTail').red (headSubst σ') := hσ'.head hH hΔ
  have hHeadF' : RedTerm (hF hΔ hTail').red (headSubst σ') :=
    convTerm₂ (hF hΔ hTail').red (hH hΔ hTail').red (hFH hΔ hTail') hHeadH'
  have hσ'F : ValidSubst eqrel Δ σ' (F :: Γ) :=
    ValidSubst.cons hTail' (hF hΔ hTail').red hHeadF'
  have hHeadEqH : RedTermEq (hH hΔ hTail).red (headSubst σ) (headSubst σ') :=
    hσσ'.head hH hΔ hσ
  have hHeadEqF : RedTermEq (hF hΔ hTail).red (headSubst σ) (headSubst σ') :=
    convEqTerm₂ (hF hΔ hTail).red (hH hΔ hTail).red (hFH hΔ hTail) hHeadEqH
  have hσσ'F : ValidSubstEq eqrel Δ σ σ' (F :: Γ) :=
    ValidSubstEq.cons hσσ'.tail (hF hΔ hTail).red hHeadEqF
  exact (ht hΔ hσF).eq hσ'F hσσ'F

/-- Irrelevance of valid term equality (`irrelevanceEqTerm`). -/
theorem irrelevanceValidEqTerm {eqrel : EqRelSet} {l l' : TypeLevel} {A t u : Term} {Γ : Context}
    (hA : ValidType eqrel l Γ A)
    (hA' : ValidType eqrel l' Γ A)
    (htu : ValidTermEq hA t u) :
    ValidTermEq hA' t u := by
  intro Δ σ hΔ hσ
  exact irrelevanceEqTerm (hA hΔ hσ).red (hA' hΔ hσ).red (htu hΔ hσ)

/-!
## Reflexivity (`Definition/LogicalRelation/Substitution/Reflexivity.agda`)
-/

/-- Reflexivity of valid types (`reflᵛ`). -/
theorem reflValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hA : ValidType eqrel l Γ A) : ValidTypeEq hA A :=
  fun hΔ hσ ↦ reflEq (hA hΔ hσ).red

/-- Reflexivity of valid terms (`reflᵗᵛ`). -/
theorem reflValidTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t : Term}
    (hA : ValidType eqrel l Γ A) (ht : ValidTerm hA t) :
    ValidTermEq hA t t :=
  fun hΔ hσ ↦ reflEqTerm (hA hΔ hσ).red (ht hΔ hσ).term

/-!
## Weakening (`Definition/LogicalRelation/Substitution/Weakening.agda`)
-/

/-- Weakening of valid types by one (`wk1ᵛ`). -/
theorem wk1Valid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A F : Term}
    (hA : ValidType eqrel l Γ A) :
    ValidType eqrel l (F :: Γ) (wk1 A) := by
  intro Δ σ hΔ hσ
  have pA : RedType eqrel l Δ (subst (tailSubst σ) A) := (hA hΔ hσ.tail).red
  have pA' : RedType eqrel l Δ (subst σ (wk1 A)) :=
    irrelevance' (subst_wk A).symm pA
  refine ⟨pA', fun {σ'} hσ' hσσ' ↦ ?_⟩
  exact irrelevanceEq'' (subst_wk A).symm (subst_wk A).symm pA pA'
    ((hA hΔ hσ.tail).eq hσ'.tail hσσ'.tail)

/-- Weakening of valid type equality by one (`wk1Eqᵛ`). -/
theorem wk1ValidEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B F : Term}
    (hA : ValidType eqrel l Γ A) (hAB : ValidTypeEq hA B) :
    ValidTypeEq (wk1Valid (F := F) hA) (wk1 B) := by
  intro Δ σ hΔ hσ
  have pA : RedType eqrel l Δ (subst (tailSubst σ) A) := (hA hΔ hσ.tail).red
  have pA' : RedType eqrel l Δ (subst σ (wk1 A)) :=
    irrelevance' (subst_wk A).symm pA
  exact irrelevanceEq'' (subst_wk A).symm (subst_wk B).symm pA pA' (hAB hΔ hσ.tail)

/-!
## Conversion (`Definition/LogicalRelation/Substitution/Conversion.agda`)
-/

/-- Conversion from left to right of valid terms (`convᵛ`). -/
theorem convValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {t A B : Term}
    (hA : ValidType eqrel l Γ A)
    (hB : ValidType eqrel l Γ B)
    (hAB : ValidTypeEq hA B)
    (ht : ValidTerm hA t) :
    ValidTerm hB t := by
  intro Δ σ hΔ hσ
  have pA := (hA hΔ hσ).red
  have pB := (hB hΔ hσ).red
  have pAB := hAB hΔ hσ
  refine ⟨convTerm₁ pA pB pAB (ht hΔ hσ).term,
    fun hσ' hσσ' ↦ convEqTerm₁ pA pB pAB ((ht hΔ hσ).eq hσ' hσσ')⟩

/-- Conversion from right to left of valid terms (`conv₂ᵛ`). -/
theorem conv2Valid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {t A B : Term}
    (hA : ValidType eqrel l Γ A)
    (hB : ValidType eqrel l Γ B)
    (hAB : ValidTypeEq hA B)
    (ht : ValidTerm hB t) :
    ValidTerm hA t := by
  intro Δ σ hΔ hσ
  have pA := (hA hΔ hσ).red
  have pB := (hB hΔ hσ).red
  have pAB := hAB hΔ hσ
  refine ⟨convTerm₂ pA pB pAB (ht hΔ hσ).term,
    fun hσ' hσσ' ↦ convEqTerm₂ pA pB pAB ((ht hΔ hσ).eq hσ' hσσ')⟩

/-- Conversion from left to right of valid term equality (`convEqᵛ`). -/
theorem convValidEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {t u A B : Term}
    (hA : ValidType eqrel l Γ A)
    (hB : ValidType eqrel l Γ B)
    (hAB : ValidTypeEq hA B)
    (htu : ValidTermEq hA t u) :
    ValidTermEq hB t u := by
  intro Δ σ hΔ hσ
  exact convEqTerm₁ (hA hΔ hσ).red (hB hΔ hσ).red (hAB hΔ hσ) (htu hΔ hσ)

/-!
## Level Embedding (`Definition/LogicalRelation/Substitution/MaybeEmbed.agda`)
-/

/-- Embedding of any validity level into `¹` (`maybeEmbᵛ`). -/
theorem maybeEmbValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hA : ValidType eqrel l Γ A) : ValidType eqrel .one Γ A := by
  intro Δ σ hΔ hσ
  have pA := (hA hΔ hσ).red
  have pA' := maybeEmb pA
  exact ⟨pA', fun hσ' hσσ' ↦ irrelevanceEq pA pA' ((hA hΔ hσ).eq hσ' hσσ')⟩

/-- Embedding of validity level `⁰` into any level `l` (`maybeEmbₛ′`). -/
theorem maybeEmbValid' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hA : ValidType eqrel .zero Γ A) : ValidType eqrel l Γ A := by
  intro Δ σ hΔ hσ
  have pA := (hA hΔ hσ).red
  have pA' := maybeEmb' (l := l) pA
  exact ⟨pA', fun hσ' hσσ' ↦ irrelevanceEq pA pA' ((hA hΔ hσ).eq hσ' hσσ')⟩

/-!
## Substitution Properties (`Definition/LogicalRelation/Substitution/Properties.agda`)
-/

/-- Valid substitutions are syntactically well-formed (`wellformedSubst`). -/
theorem wellformedSubst {eqrel : EqRelSet} {Γ Δ : Context} {σ : Subst}
    (hΓ : ValidCtx eqrel Γ) (hΔ : CtxWf Δ) (hσ : ValidSubst eqrel Δ σ Γ) :
    SubstWf Δ σ Γ := by
  induction hΓ generalizing σ with
  | nil => exact .nil
  | cons _ hA ih =>
      exact .cons (ih hσ.tail) (escapeTerm (hA hΔ hσ.tail).red (hσ.head hA hΔ))

/-- Valid substitution equality is syntactically well-formed (`wellformedSubstEq`). -/
theorem wellformedSubstEq {eqrel : EqRelSet} {Γ Δ : Context} {σ σ' : Subst}
    (hΓ : ValidCtx eqrel Γ) (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ) (hσσ' : ValidSubstEq eqrel Δ σ σ' Γ) :
    SubstEq Δ σ σ' Γ := by
  induction hΓ generalizing σ σ' with
  | nil => exact .nil
  | cons _ hA ih =>
      exact .cons (ih hσ.tail hσσ'.tail)
        (eqrel.termToEq (escapeTermEq (hA hΔ hσ.tail).red (hσσ'.head hA hΔ hσ)))

/-- Extend a valid substitution with a term (`consSubstS`). -/
theorem consSubstS {eqrel : EqRelSet} {l : TypeLevel} {σ : Subst} {t A : Term} {Γ Δ : Context}
    (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ)
    (hA : ValidType eqrel l Γ A)
    (ht : RedTerm (hA hΔ hσ).red t) :
    ValidSubst eqrel Δ (consSubst σ t) (A :: Γ) :=
  ValidSubst.cons hσ (hA hΔ hσ).red ht

/-- Extend a valid substitution equality with a term (`consSubstSEq`). -/
theorem consSubstSEq {eqrel : EqRelSet} {l : TypeLevel} {σ σ' : Subst} {t A : Term}
    {Γ Δ : Context}
    (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ)
    (hσσ' : ValidSubstEq eqrel Δ σ σ' Γ)
    (hA : ValidType eqrel l Γ A)
    (ht : RedTerm (hA hΔ hσ).red t) :
    ValidSubstEq eqrel Δ (consSubst σ t) (consSubst σ' t) (A :: Γ) :=
  ValidSubstEq.cons hσσ' (hA hΔ hσ).red (reflEqTerm (hA hΔ hσ).red ht)

/-- Weakening of valid substitutions (`wkSubstS`). -/
theorem wkSubstS {eqrel : EqRelSet} {ρ : Wk} {σ : Subst} {Γ Δ Δ' : Context}
    (hρ : WkCtx ρ Δ' Δ) (hΔ' : CtxWf Δ')
    (hσ : ValidSubst eqrel Δ σ Γ) :
    ValidSubst eqrel Δ' (wkSubst ρ σ) Γ := by
  induction Γ generalizing σ with
  | nil => trivial
  | cons A Γ ih =>
      rcases hσ with ⟨hTail, l, pA, hHead⟩
      have pA_wk : RedType eqrel l Δ' (wk ρ (subst (tailSubst σ) A)) :=
        wkRed hρ hΔ' pA
      have pA' : RedType eqrel l Δ' (subst (tailSubst (wkSubst ρ σ)) A) :=
        irrelevance' (wk_subst A) pA_wk
      have hHead_wk : RedTerm pA_wk (wk ρ (headSubst σ)) :=
        wkRedTerm hρ hΔ' pA hHead
      have hHead' : RedTerm pA' (headSubst (wkSubst ρ σ)) :=
        irrelevanceTerm' (wk_subst A) pA_wk pA' hHead_wk
      exact ⟨ih hTail, l, pA', hHead'⟩

/-- Weakening of valid substitution equality (`wkSubstSEq`). -/
theorem wkSubstSEq {eqrel : EqRelSet} {ρ : Wk} {σ σ' : Subst} {Γ Δ Δ' : Context}
    (hρ : WkCtx ρ Δ' Δ) (hΔ' : CtxWf Δ')
    (hσσ' : ValidSubstEq eqrel Δ σ σ' Γ) :
    ValidSubstEq eqrel Δ' (wkSubst ρ σ) (wkSubst ρ σ') Γ := by
  induction Γ generalizing σ σ' with
  | nil => trivial
  | cons A Γ ih =>
      rcases hσσ' with ⟨hTailEq, l, pA, hHeadEq⟩
      have pA_wk : RedType eqrel l Δ' (wk ρ (subst (tailSubst σ) A)) :=
        wkRed hρ hΔ' pA
      have pA' : RedType eqrel l Δ' (subst (tailSubst (wkSubst ρ σ)) A) :=
        irrelevance' (wk_subst A) pA_wk
      have hHeadEq_wk : RedTermEq pA_wk (wk ρ (headSubst σ)) (wk ρ (headSubst σ')) :=
        wkRedTermEq hρ hΔ' pA hHeadEq
      have hHeadEq' : RedTermEq pA' (headSubst (wkSubst ρ σ)) (headSubst (wkSubst ρ σ')) :=
        irrelevanceEqTerm' (wk_subst A) pA_wk pA' hHeadEq_wk
      exact ⟨ih hTailEq, l, pA', hHeadEq'⟩

/-- Weaken a valid substitution by one type (`wk1SubstS`). -/
theorem wk1SubstS {eqrel : EqRelSet} {F : Term} {σ : Subst} {Γ Δ : Context}
    (hΔ : CtxWf Δ) (hF : TypeWf Δ F)
    (hσ : ValidSubst eqrel Δ σ Γ) :
    ValidSubst eqrel (F :: Δ) (wk1Subst σ) Γ :=
  wkSubstS (.step .id) (.cons hΔ hF) hσ

/-- Weaken a valid substitution equality by one type (`wk1SubstSEq`). -/
theorem wk1SubstSEq {eqrel : EqRelSet} {F : Term} {σ σ' : Subst} {Γ Δ : Context}
    (hΔ : CtxWf Δ) (hF : TypeWf Δ F)
    (hσσ' : ValidSubstEq eqrel Δ σ σ' Γ) :
    ValidSubstEq eqrel (F :: Δ) (wk1Subst σ) (wk1Subst σ') Γ :=
  wkSubstSEq (.step .id) (.cons hΔ hF) hσσ'

/-- Lift a valid substitution (`liftSubstS`). -/
theorem member_here_wk1Subst (σ : Subst) (F : Term) (Δ : Context) :
    Member 0 (subst (wk1Subst σ) F) (subst σ F :: Δ) := by
  change Member 0 (subst (wkSubst (.step .id) σ) F) (subst σ F :: Δ)
  rw [← wk_subst (ρ := .step .id) (σ := σ) F]
  exact .here

theorem liftSubstS {eqrel : EqRelSet} {l : TypeLevel} {F : Term} {σ : Subst} {Γ Δ : Context}
    (hΔ : CtxWf Δ)
    (hF : ValidType eqrel l Γ F)
    (hσ : ValidSubst eqrel Δ σ Γ) :
    ValidSubst eqrel (subst σ F :: Δ) (liftSubst σ) (F :: Γ) := by
  have hσF : TypeWf Δ (subst σ F) := escape (hF hΔ hσ).red
  have hΔF : CtxWf (subst σ F :: Δ) := .cons hΔ hσF
  have hTail : ValidSubst eqrel (subst σ F :: Δ) (wk1Subst σ) Γ :=
    wk1SubstS hΔ hσF hσ
  have pF : RedType eqrel l (subst σ F :: Δ) (subst (wk1Subst σ) F) :=
    (hF hΔF hTail).red
  have hLookup : Member 0 (subst (wk1Subst σ) F) (subst σ F :: Δ) :=
    member_here_wk1Subst σ F Δ
  have hVar0 : HasType (subst σ F :: Δ) (.var 0) (subst (wk1Subst σ) F) :=
    .var hΔF hLookup
  have hHead : RedTerm pF (.var 0) :=
    neuTerm pF (.var 0) hVar0 (eqrel.varRefl hVar0)
  exact ⟨hTail, l, pF, hHead⟩

/-- Lift a valid substitution equality (`liftSubstSEq`). -/
theorem liftSubstSEq {eqrel : EqRelSet} {l : TypeLevel} {F : Term} {σ σ' : Subst} {Γ Δ : Context}
    (hΔ : CtxWf Δ)
    (hF : ValidType eqrel l Γ F)
    (hσ : ValidSubst eqrel Δ σ Γ)
    (hσσ' : ValidSubstEq eqrel Δ σ σ' Γ) :
    ValidSubstEq eqrel (subst σ F :: Δ) (liftSubst σ) (liftSubst σ') (F :: Γ) := by
  have hσF : TypeWf Δ (subst σ F) := escape (hF hΔ hσ).red
  have hΔF : CtxWf (subst σ F :: Δ) := .cons hΔ hσF
  have hTail : ValidSubst eqrel (subst σ F :: Δ) (wk1Subst σ) Γ :=
    wk1SubstS hΔ hσF hσ
  have hTailEq : ValidSubstEq eqrel (subst σ F :: Δ) (wk1Subst σ) (wk1Subst σ') Γ :=
    wk1SubstSEq hΔ hσF hσσ'
  have pF : RedType eqrel l (subst σ F :: Δ) (subst (wk1Subst σ) F) :=
    (hF hΔF hTail).red
  have hLookup : Member 0 (subst (wk1Subst σ) F) (subst σ F :: Δ) :=
    member_here_wk1Subst σ F Δ
  have hVar0 : HasType (subst σ F :: Δ) (.var 0) (subst (wk1Subst σ) F) :=
    .var hΔF hLookup
  have hHeadEq : RedTermEq pF (.var 0) (.var 0) :=
    neuEqTerm pF (.var 0) (.var 0) hVar0 hVar0 (eqrel.varRefl hVar0)
  exact ⟨hTailEq, l, pF, hHeadEq⟩

/-- Valid contexts are well-formed and admit a valid identity substitution
(`soundContext` and `idSubstS`). -/
theorem soundContext_and_idSubstS {eqrel : EqRelSet} {Γ : Context}
    (hΓ : ValidCtx eqrel Γ) :
    CtxWf Γ ∧ ValidSubst eqrel Γ idSubst Γ := by
  induction hΓ with
  | nil => exact ⟨.nil, trivial⟩
  | @cons Γ A l _ hA ih =>
      rcases ih with ⟨wfΓ, idΓ⟩
      have pA_id : RedType eqrel l Γ (subst idSubst A) := (hA wfΓ idΓ).red
      have wfA : TypeWf Γ A := escape (irrelevance' (subst_id A) pA_id)
      have wfΓA : CtxWf (A :: Γ) := .cons wfΓ wfA
      have hTail : ValidSubst eqrel (A :: Γ) (wk1Subst idSubst) Γ :=
        wk1SubstS wfΓ wfA idΓ
      have pA_tail : RedType eqrel l (A :: Γ) (subst (wk1Subst idSubst) A) :=
        (hA wfΓA hTail).red
      have hLookup : Member 0 (subst (wk1Subst idSubst) A) (A :: Γ) := by
        have h0 := member_here_wk1Subst idSubst A Γ
        rwa [subst_id A] at h0
      have hVar0 : HasType (A :: Γ) (.var 0) (subst (wk1Subst idSubst) A) :=
        .var wfΓA hLookup
      have hHead : RedTerm pA_tail (.var 0) :=
        neuTerm pA_tail (.var 0) hVar0 (eqrel.varRefl hVar0)
      exact ⟨wfΓA, hTail, l, pA_tail, hHead⟩

/-- Valid contexts are syntactically well-formed (`soundContext`). -/
theorem soundContext {eqrel : EqRelSet} {Γ : Context} (hΓ : ValidCtx eqrel Γ) : CtxWf Γ :=
  (soundContext_and_idSubstS hΓ).1

/-- Identity substitution is valid on a valid context (`idSubstS`). -/
theorem idSubstS {eqrel : EqRelSet} {Γ : Context} (hΓ : ValidCtx eqrel Γ) :
    ValidSubst eqrel Γ idSubst Γ :=
  (soundContext_and_idSubstS hΓ).2

/-- Reflexivity of valid substitutions (`reflSubst`). -/
theorem reflSubst {eqrel : EqRelSet} {σ : Subst} {Γ Δ : Context}
    (hσ : ValidSubst eqrel Δ σ Γ) :
    ValidSubstEq eqrel Δ σ σ Γ := by
  induction Γ generalizing σ with
  | nil => trivial
  | cons A Γ ih =>
      rcases hσ with ⟨hTail, l, pA, hHead⟩
      exact ⟨ih hTail, l, pA, reflEqTerm pA hHead⟩

/-- Reflexivity of the valid identity substitution (`reflIdSubst`). -/
theorem reflIdSubst {eqrel : EqRelSet} {Γ : Context} (hΓ : ValidCtx eqrel Γ) :
    ValidSubstEq eqrel Γ idSubst idSubst Γ :=
  reflSubst (idSubstS hΓ)

/-- Symmetry of valid substitution equality (`symS`). -/
theorem symS {eqrel : EqRelSet} {σ σ' : Subst} {Γ Δ : Context}
    (hΓ : ValidCtx eqrel Γ) (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ)
    (hσ' : ValidSubst eqrel Δ σ' Γ)
    (hσσ' : ValidSubstEq eqrel Δ σ σ' Γ) :
    ValidSubstEq eqrel Δ σ' σ Γ := by
  induction hΓ generalizing σ σ' with
  | nil => trivial
  | @cons Γ A l _ hA ih =>
      have pA := (hA hΔ hσ.tail).red
      have pA' := (hA hΔ hσ'.tail).red
      have pAA' := (hA hΔ hσ.tail).eq hσ'.tail hσσ'.tail
      have hSym : RedTermEq pA (headSubst σ') (headSubst σ) :=
        symEqTerm pA (hσσ'.head hA hΔ hσ)
      exact ⟨ih hσ.tail hσ'.tail hσσ'.tail,
        l, pA', convEqTerm₁ pA pA' pAA' hSym⟩

/-- Transitivity of valid substitution equality (`transS`). -/
theorem transS {eqrel : EqRelSet} {σ σ' σ'' : Subst} {Γ Δ : Context}
    (hΓ : ValidCtx eqrel Γ) (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ)
    (hσ' : ValidSubst eqrel Δ σ' Γ)
    (_hσ'' : ValidSubst eqrel Δ σ'' Γ)
    (hσσ' : ValidSubstEq eqrel Δ σ σ' Γ)
    (hσ'σ'' : ValidSubstEq eqrel Δ σ' σ'' Γ) :
    ValidSubstEq eqrel Δ σ σ'' Γ := by
  induction hΓ generalizing σ σ' σ'' with
  | nil => trivial
  | @cons Γ A l _ hA ih =>
      have pA := (hA hΔ hσ.tail).red
      have pA' := (hA hΔ hσ'.tail).red
      have pAA' := (hA hΔ hσ.tail).eq hσ'.tail hσσ'.tail
      have h1 : RedTermEq pA (headSubst σ) (headSubst σ') :=
        hσσ'.head hA hΔ hσ
      have h2' : RedTermEq pA' (headSubst σ') (headSubst σ'') :=
        hσ'σ''.head hA hΔ hσ'
      have h2 : RedTermEq pA (headSubst σ') (headSubst σ'') :=
        convEqTerm₂ pA pA' pAA' h2'
      exact ⟨ih hσ.tail hσ'.tail _hσ''.tail hσσ'.tail hσ'σ''.tail,
        l, pA, transEqTerm pA h1 h2⟩

/-!
## Escape and Reducibility of Valid Judgments
(`Definition/LogicalRelation/Substitution/Escape.agda` and `Reducibility.agda`)
-/

/-- Valid types are reducible (`reducibleᵛ`). -/
theorem reducibleValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hΓ : ValidCtx eqrel Γ) (hA : ValidType eqrel l Γ A) :
    RedType eqrel l Γ A :=
  irrelevance' (subst_id A) (hA (soundContext hΓ) (idSubstS hΓ)).red

/-- Valid type equality is reducible (`reducibleEqᵛ`). -/
theorem reducibleValidEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B : Term}
    (hΓ : ValidCtx eqrel Γ) (hA : ValidType eqrel l Γ A)
    (hAB : ValidTypeEq hA B) :
    RedEq (reducibleValid hΓ hA) B := by
  have wfΓ := soundContext hΓ
  have idΓ := idSubstS hΓ
  exact irrelevanceEq'' (subst_id A) (subst_id B)
    (hA wfΓ idΓ).red (reducibleValid hΓ hA) (hAB wfΓ idΓ)

/-- Valid terms are reducible (`reducibleTermᵛ`). -/
theorem reducibleValidTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {t A : Term}
    (hΓ : ValidCtx eqrel Γ) (hA : ValidType eqrel l Γ A)
    (ht : ValidTerm hA t) :
    RedTerm (reducibleValid hΓ hA) t := by
  have wfΓ := soundContext hΓ
  have idΓ := idSubstS hΓ
  exact irrelevanceTerm'' (subst_id A) (subst_id t)
    (hA wfΓ idΓ).red (reducibleValid hΓ hA) (ht wfΓ idΓ).term

/-- Valid term equality is reducible (`reducibleEqTermᵛ`). -/
theorem reducibleValidEqTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {t u A : Term}
    (hΓ : ValidCtx eqrel Γ) (hA : ValidType eqrel l Γ A)
    (htu : ValidTermEq hA t u) :
    RedTermEq (reducibleValid hΓ hA) t u := by
  have wfΓ := soundContext hΓ
  have idΓ := idSubstS hΓ
  exact irrelevanceEqTerm'' (subst_id t) (subst_id u) (subst_id A)
    (hA wfΓ idΓ).red (reducibleValid hΓ hA) (htu wfΓ idΓ)

/-- Valid types are syntactically well-formed (`escapeᵛ`). -/
theorem escapeValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hΓ : ValidCtx eqrel Γ) (hA : ValidType eqrel l Γ A) :
    TypeWf Γ A :=
  escape (reducibleValid hΓ hA)

/-- Valid type equality respects `eqrel.TypeEqRel` (`escapeEqᵛ`). -/
theorem escapeValidEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B : Term}
    (hΓ : ValidCtx eqrel Γ) (hA : ValidType eqrel l Γ A)
    (hAB : ValidTypeEq hA B) :
    eqrel.TypeEqRel Γ A B :=
  escapeEq (reducibleValid hΓ hA) (reducibleValidEq hΓ hA hAB)

/-- Valid terms are syntactically well-typed (`escapeTermᵛ`). -/
theorem escapeValidTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {t A : Term}
    (hΓ : ValidCtx eqrel Γ) (hA : ValidType eqrel l Γ A)
    (ht : ValidTerm hA t) :
    HasType Γ t A :=
  escapeTerm (reducibleValid hΓ hA) (reducibleValidTerm hΓ hA ht)

/-- Valid term equality respects `eqrel.TermEqRel` (`escapeEqTermᵛ`). -/
theorem escapeValidEqTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {t u A : Term}
    (hΓ : ValidCtx eqrel Γ) (hA : ValidType eqrel l Γ A)
    (htu : ValidTermEq hA t u) :
    eqrel.TermEqRel Γ t u A :=
  escapeTermEq (reducibleValid hΓ hA) (reducibleValidEqTerm hΓ hA htu)

/-!
## Weak-Head Expansion of Valid Terms (`Definition/LogicalRelation/Substitution/Reduction.agda`)
-/

/-- Weak-head expansion of valid terms (`redSubstTermᵛ`). -/
theorem redSubstTermValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t u : Term}
    (htu : ValidRedTerm eqrel Γ t u A)
    (hA : ValidType eqrel l Γ A)
    (hu : ValidTerm hA u) :
    ValidTerm hA t ∧ ValidTermEq hA t u := by
  refine ⟨fun hΔ hσ ↦ ?_, fun hΔ hσ ↦ ?_⟩
  · have pA := (hA hΔ hσ).red
    rcases redSubstTerm (htu hΔ hσ) pA (hu hΔ hσ).term with ⟨ht, htu_eq⟩
    refine ⟨ht, fun {σ'} hσ' hσσ' ↦ ?_⟩
    have pA' := (hA hΔ hσ').red
    have pAA' := (hA hΔ hσ).eq hσ' hσσ'
    rcases redSubstTerm (htu hΔ hσ') pA' (hu hΔ hσ').term with ⟨_, ht'u'_eq⟩
    exact transEqTerm pA htu_eq
      (transEqTerm pA ((hu hΔ hσ).eq hσ' hσσ')
        (convEqTerm₂ pA pA' pAA' (symEqTerm pA' ht'u'_eq)))
  · exact (redSubstTerm (htu hΔ hσ) (hA hΔ hσ).red (hu hΔ hσ).term).2

/-!
## Universe Introductions (`Definition/LogicalRelation/Substitution/Introductions/Universe.agda`)
-/

/-- Helper constructing `RedType eqrel .one Δ .univ`. -/
theorem redUOne {eqrel : EqRelSet} {Δ : Context} (hΔ : CtxWf Δ) :
    RedType eqrel .one Δ .univ :=
  ⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) Δ, .U ⟨.zeroLT, hΔ⟩⟩

/-- Validity of the universe type `U` (`Uᵛ`). -/
theorem UValid {eqrel : EqRelSet} {Γ : Context} :
    ValidType eqrel .one Γ .univ :=
  fun hΔ _ ↦
    ⟨redUOne hΔ,
      fun _ _ ↦ ⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) _,
        .U ⟨.zeroLT, hΔ⟩, rfl⟩⟩

/-- Valid terms of type `U` are valid types (`univᵛ`). -/
theorem univValid {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A : Term}
    (hU : ValidType eqrel l Γ .univ)
    (hA : ValidTerm hU A) :
    ValidType eqrel l' Γ A := by
  intro Δ σ hΔ hσ
  have pU := (hU hΔ hσ).red
  have pA₀ : RedType eqrel .zero Δ (subst σ A) := univEq pU (hA hΔ hσ).term
  have pA : RedType eqrel l' Δ (subst σ A) := maybeEmb' pA₀
  exact ⟨pA, fun hσ' hσσ' ↦ univEqEq pU pA ((hA hΔ hσ).eq hσ' hσσ')⟩

/-- Valid term equality of type `U` is valid type equality (`univEqᵛ`). -/
theorem univEqValid {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A B : Term}
    (hU : ValidType eqrel l' Γ .univ)
    (hA : ValidType eqrel l Γ A)
    (hAB : ValidTermEq hU A B) :
    ValidTypeEq hA B :=
  fun hΔ hσ ↦ univEqEq (hU hΔ hσ).red (hA hΔ hσ).red (hAB hΔ hσ)

/-!
## Natural Number Introductions (`Definition/LogicalRelation/Substitution/Introductions/Nat.agda`)
-/

/-- Helper constructing `RedType eqrel l Δ .nat`. -/
theorem redNat {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} (hΔ : CtxWf Δ) :
    RedType eqrel l Δ .nat :=
  ⟨RedNatRel eqrel Δ, .nat (idRedWf (.nat hΔ))⟩

/-- Validity of `ℕ` (`ℕᵛ`). -/
theorem natValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} :
    ValidType eqrel l Γ .nat :=
  fun hΔ _ ↦
    ⟨redNat hΔ,
      fun _ _ ↦ ⟨RedNatRel eqrel _, .nat (idRedWf (.nat hΔ)), .refl (.nat hΔ)⟩⟩

/-- Validity of `ℕ` as a term of `U` (`ℕᵗᵛ`). -/
theorem natTermValid {eqrel : EqRelSet} {Γ : Context} :
    ValidTerm (UValid (eqrel := eqrel) (Γ := Γ)) .nat := by
  intro Δ σ hΔ _
  have hNatU : HasType Δ .nat .univ := .nat hΔ
  have hNatWf : TypeWf Δ .nat := .nat hΔ
  refine ⟨⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) Δ, .U ⟨.zeroLT, hΔ⟩,
      ⟨.nat, idRedTermWf hNatU, .nat, eqrel.natTermRefl hΔ,
        RedNatRel eqrel Δ, .nat (idRedWf hNatWf)⟩⟩,
    fun _ _ ↦ ⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) Δ, .U ⟨.zeroLT, hΔ⟩,
      ⟨.nat, .nat, idRedTermWf hNatU, idRedTermWf hNatU, .nat, .nat,
        eqrel.natTermRefl hΔ, RedNatRel eqrel Δ, .nat (idRedWf hNatWf),
        ⟨RedNatRel eqrel Δ, .nat (idRedWf hNatWf)⟩, .refl hNatWf⟩⟩⟩

/-- Validity of `zero` (`zeroᵛ`). -/
theorem zeroValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} :
    ValidTerm (natValid (eqrel := eqrel) (l := l) (Γ := Γ)) .zero := by
  intro Δ σ hΔ _
  have hZero : HasType Δ .zero .nat := .zero hΔ
  have hNatWf : TypeWf Δ .nat := .nat hΔ
  refine ⟨⟨RedNatRel eqrel Δ, .nat (idRedWf hNatWf),
      .mk .zero .zero (idRedTermWf hZero) (eqrel.zeroRefl hΔ) .zero⟩,
    fun _ _ ↦ ⟨RedNatRel eqrel Δ, .nat (idRedWf hNatWf),
      .mk .zero .zero .zero .zero (idRedTermWf hZero) (idRedTermWf hZero)
        (eqrel.zeroRefl hΔ) .zero⟩⟩

/-- Validity of `suc` (`sucᵛ`). -/
theorem sucValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {n : Term}
    (hNat : ValidType eqrel l Γ .nat)
    (hn : ValidTerm hNat n) :
    ValidTerm hNat (.succ n) := by
  intro Δ σ hΔ hσ
  have pNat := (hNat hΔ hσ).red
  refine ⟨sucTerm pNat (hn hΔ hσ).term,
    fun hσ' hσσ' ↦ sucEqTerm pNat ((hn hΔ hσ).eq hσ' hσσ')⟩

/-!
## Single Variable Substitution (`Definition/LogicalRelation/Substitution/Introductions/SingleSubst.agda`)
-/

/-- Validity of substituting a single variable in a type (`substS`). -/
theorem substS {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (ht : ValidTerm hF t) :
    ValidType eqrel l Γ (subst0 G t) := by
  intro Δ σ hΔ hσ
  have hσt : ValidSubst eqrel Δ (consSubst σ (subst σ t)) (F :: Γ) :=
    consSubstS hΔ hσ hF (ht hΔ hσ).term
  have pGt := (hG hΔ hσt).red
  have pGt' : RedType eqrel l Δ (subst σ (subst0 G t)) :=
    irrelevance' (substConsId G) pGt
  refine ⟨pGt', fun {σ'} hσ' hσσ' ↦ ?_⟩
  have hσ't : ValidSubst eqrel Δ (consSubst σ' (subst σ' t)) (F :: Γ) :=
    consSubstS hΔ hσ' hF (ht hΔ hσ').term
  have hσσ't : ValidSubstEq eqrel Δ (consSubst σ (subst σ t)) (consSubst σ' (subst σ' t)) (F :: Γ) :=
    ValidSubstEq.cons hσσ' (hF hΔ hσ).red ((ht hΔ hσ).eq hσ' hσσ')
  exact irrelevanceEq'' (substConsId G) (substConsId G) pGt pGt'
    ((hG hΔ hσt).eq hσ't hσσ't)

/-- Validity of substituting a single variable in type equality (`substSEq`). -/
theorem substSEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F F' G G' t t' : Term}
    (hF : ValidType eqrel l Γ F)
    (hF' : ValidType eqrel l Γ F')
    (hFF' : ValidTypeEq hF F')
    (hG : ValidType eqrel l (F :: Γ) G)
    (hG' : ValidType eqrel l (F' :: Γ) G')
    (hGG' : ValidTypeEq hG G')
    (ht : ValidTerm hF t)
    (ht' : ValidTerm hF' t')
    (htt' : ValidTermEq hF t t') :
    ValidTypeEq (substS hF hG ht) (subst0 G' t') := by
  intro Δ σ hΔ hσ
  have hσt : ValidSubst eqrel Δ (consSubst σ (subst σ t)) (F :: Γ) :=
    consSubstS hΔ hσ hF (ht hΔ hσ).term
  have pGt := (hG hΔ hσt).red
  have pGt' : RedType eqrel l Δ (subst σ (subst0 G t)) :=
    irrelevance' (substConsId G) pGt
  have ht_conv : ValidTerm hF' t := convValid hF hF' hFF' ht
  have hσt_F' : ValidSubst eqrel Δ (consSubst σ (subst σ t)) (F' :: Γ) :=
    consSubstS hΔ hσ hF' (ht_conv hΔ hσ).term
  have pG't := (hG' hΔ hσt_F').red
  have hGt_G't : RedEq pGt' (subst (consSubst σ (subst σ t)) G') :=
    irrelevanceEq' (substConsId G) pGt pGt' (hGG' hΔ hσt)
  have hσt'_F' : ValidSubst eqrel Δ (consSubst σ (subst σ t')) (F' :: Γ) :=
    consSubstS hΔ hσ hF' (ht' hΔ hσ).term
  have htt'_F' : ValidTermEq hF' t t' := convValidEq hF hF' hFF' htt'
  have hσσ_t_t' : ValidSubstEq eqrel Δ (consSubst σ (subst σ t)) (consSubst σ (subst σ t')) (F' :: Γ) :=
    ValidSubstEq.cons (reflSubst hσ) (hF' hΔ hσ).red (htt'_F' hΔ hσ)
  have hG't_G't' : RedEq pG't (subst σ (subst0 G' t')) :=
    irrelevanceEq'' rfl (substConsId G') pG't pG't ((hG' hΔ hσt_F').eq hσt'_F' hσσ_t_t')
  have pG't'_raw := (hG' hΔ hσt'_F').red
  have pG't' : RedType eqrel l Δ (subst σ (subst0 G' t')) :=
    irrelevance' (substConsId G') pG't'_raw
  exact transEq pGt' pG't pG't' hGt_G't hG't_G't'

/-- Validity of substituting a single variable in a term (`substSTerm`). -/
theorem substSTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t f : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (hf : ValidTerm hG f)
    (ht : ValidTerm hF t) :
    ValidTerm (substS hF hG ht) (subst0 f t) := by
  intro Δ σ hΔ hσ
  have hσt : ValidSubst eqrel Δ (consSubst σ (subst σ t)) (F :: Γ) :=
    consSubstS hΔ hσ hF (ht hΔ hσ).term
  have pGt := (hG hΔ hσt).red
  have pGt' : RedType eqrel l Δ (subst σ (subst0 G t)) :=
    irrelevance' (substConsId G) pGt
  have pft : RedTerm pGt' (subst σ (subst0 f t)) :=
    irrelevanceTerm'' (substConsId G) (substConsId f) pGt pGt' (hf hΔ hσt).term
  refine ⟨pft, fun {σ'} hσ' hσσ' ↦ ?_⟩
  have hσ't : ValidSubst eqrel Δ (consSubst σ' (subst σ' t)) (F :: Γ) :=
    consSubstS hΔ hσ' hF (ht hΔ hσ').term
  have hσσ't : ValidSubstEq eqrel Δ (consSubst σ (subst σ t)) (consSubst σ' (subst σ' t)) (F :: Γ) :=
    ValidSubstEq.cons hσσ' (hF hΔ hσ).red ((ht hΔ hσ).eq hσ' hσσ')
  exact irrelevanceEqTerm'' (substConsId f) (substConsId f) (substConsId G)
    pGt pGt' ((hf hΔ hσt).eq hσ't hσσ't)

/-- Validity of single lifted substitution in types (`subst↑S`). -/
theorem substUpS {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (ht : ValidTerm (wk1Valid (F := F) hF) t) :
    ValidType eqrel l (F :: Γ) (substKeep G t) := by
  intro Δ σ hΔ hσ
  have hwk1F : ValidType eqrel l (F :: Γ) (wk1 F) := wk1Valid (F := F) hF
  have pwk1F := (hwk1F hΔ hσ).red
  have pTailF := (hF hΔ hσ.tail).red
  have ht' : RedTerm pTailF (subst σ t) :=
    irrelevanceTerm' (subst_wk F) pwk1F pTailF (ht hΔ hσ).term
  have hσ_t : ValidSubst eqrel Δ (consSubst (tailSubst σ) (subst σ t)) (F :: Γ) :=
    ValidSubst.cons hσ.tail pTailF ht'
  have pGt := (hG hΔ hσ_t).red
  have pGt' : RedType eqrel l Δ (subst σ (substKeep G t)) :=
    irrelevance' (substConsTailId (G := G) (t := t) (σ := σ)) pGt
  refine ⟨pGt', fun {σ'} hσ' hσσ' ↦ ?_⟩
  have pwk1F' := (hwk1F hΔ hσ').red
  have pTailF' := (hF hΔ hσ'.tail).red
  have ht'_σ' : RedTerm pTailF' (subst σ' t) :=
    irrelevanceTerm' (subst_wk F) pwk1F' pTailF' (ht hΔ hσ').term
  have hσ'_t : ValidSubst eqrel Δ (consSubst (tailSubst σ') (subst σ' t)) (F :: Γ) :=
    ValidSubst.cons hσ'.tail pTailF' ht'_σ'
  have hteq : RedTermEq pTailF (subst σ t) (subst σ' t) :=
    irrelevanceEqTerm' (subst_wk F) pwk1F pTailF ((ht hΔ hσ).eq hσ' hσσ')
  have hσσ'_t : ValidSubstEq eqrel Δ
      (consSubst (tailSubst σ) (subst σ t))
      (consSubst (tailSubst σ') (subst σ' t)) (F :: Γ) :=
    ValidSubstEq.cons hσσ'.tail pTailF hteq
  exact irrelevanceEq''
    (substConsTailId (G := G) (t := t) (σ := σ))
    (substConsTailId (G := G) (t := t) (σ := σ'))
    pGt pGt' ((hG hΔ hσ_t).eq hσ'_t hσσ'_t)

/-- Validity of single lifted substitution in type equality (`subst↑SEq`). -/
theorem substUpSEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G G' t t' : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (hG' : ValidType eqrel l (F :: Γ) G')
    (hGG' : ValidTypeEq hG G')
    (ht : ValidTerm (wk1Valid (F := F) hF) t)
    (ht' : ValidTerm (wk1Valid (F := F) hF) t')
    (htt' : ValidTermEq (wk1Valid (F := F) hF) t t') :
    ValidTypeEq (substUpS hF hG ht) (substKeep G' t') := by
  intro Δ σ hΔ hσ
  have hwk1F : ValidType eqrel l (F :: Γ) (wk1 F) := wk1Valid (F := F) hF
  have pwk1F := (hwk1F hΔ hσ).red
  have pTailF := (hF hΔ hσ.tail).red
  have ht₁ : RedTerm pTailF (subst σ t) :=
    irrelevanceTerm' (subst_wk F) pwk1F pTailF (ht hΔ hσ).term
  have ht₂ : RedTerm pTailF (subst σ t') :=
    irrelevanceTerm' (subst_wk F) pwk1F pTailF (ht' hΔ hσ).term
  have htt'₁ : RedTermEq pTailF (subst σ t) (subst σ t') :=
    irrelevanceEqTerm' (subst_wk F) pwk1F pTailF (htt' hΔ hσ)
  have hσ_t : ValidSubst eqrel Δ (consSubst (tailSubst σ) (subst σ t)) (F :: Γ) :=
    ValidSubst.cons hσ.tail pTailF ht₁
  have hσ_t' : ValidSubst eqrel Δ (consSubst (tailSubst σ) (subst σ t')) (F :: Γ) :=
    ValidSubst.cons hσ.tail pTailF ht₂
  have pGt := (hG hΔ hσ_t).red
  have pGt' := irrelevance' (substConsTailId (G := G) (t := t) (σ := σ)) pGt
  have pG't := (hG' hΔ hσ_t).red
  have pG't' := irrelevance' (substConsTailId (G := G') (t := t) (σ := σ)) pG't
  have pG't₂ := (hG' hΔ hσ_t').red
  have pG't₂' := irrelevance' (substConsTailId (G := G') (t := t') (σ := σ)) pG't₂
  have h1 : RedEq pGt' (subst σ (substKeep G' t)) :=
    irrelevanceEq''
      (substConsTailId (G := G) (t := t) (σ := σ))
      (substConsTailId (G := G') (t := t) (σ := σ))
      pGt pGt' (hGG' hΔ hσ_t)
  have hσσ_t_t' : ValidSubstEq eqrel Δ
      (consSubst (tailSubst σ) (subst σ t))
      (consSubst (tailSubst σ) (subst σ t')) (F :: Γ) :=
    ValidSubstEq.cons (reflSubst hσ.tail) pTailF htt'₁
  have h2 : RedEq pG't' (subst σ (substKeep G' t')) :=
    irrelevanceEq''
      (substConsTailId (G := G') (t := t) (σ := σ))
      (substConsTailId (G := G') (t := t') (σ := σ))
      pG't pG't' ((hG' hΔ hσ_t).eq hσ_t' hσσ_t_t')
  exact transEq pGt' pG't' pG't₂' h1 h2

theorem elimPiAt_zero {eqrel : EqRelSet} {Γ : Context} {A F G : Term}
    (D : TypeStar Γ A (.pi F G)) (p : RedType eqrel .zero Γ A) :
    RedPiAt eqrel .zero Γ A F G := by
  rcases p with ⟨rel, h⟩
  cases h with
  | U _ => cases whnfRedStar D .univ
  | nat D' => cases whrDetStar ⟨D'.reduction, .nat⟩ ⟨D, .pi⟩
  | ne neA =>
      have h := whrDetStar ⟨D, .pi⟩ ⟨neA.D.reduction, .neutral neA.neK⟩
      subst h
      cases neA.neK
  | pi D' hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext =>
      have hPi : Term.pi _ _ = Term.pi F G :=
        whrDetStar ⟨D'.reduction, .pi⟩ ⟨D, .pi⟩
      injection hPi with hF₀ hG₀
      subst hF₀ hG₀
      refine ⟨D', hF, hG, AeqA, ?_, ?_, ?_⟩
      · intro ρ Δ hρ hΔ
        rcases hF_ex hρ hΔ with ⟨r, hr⟩
        exact ⟨r, derivF hρ hΔ r hr⟩
      · intro ρ Δ a hρ hΔ ha
        have ha' : RelFHasTerm relF ρ Δ a := by
          rcases hF_ex hρ hΔ with ⟨r, hr⟩
          have hrAt := derivF hρ hΔ r hr
          exact ⟨r, hr, (RedTerm_of_LogRelAt hrAt _).mp ha⟩
        rcases hG_ex hρ hΔ ha' with ⟨s, hs⟩
        exact ⟨s, derivG hρ hΔ ha' s hs⟩
      · intro ρ Δ a b hρ hΔ ha hb hab
        have ha' : RelFHasTerm relF ρ Δ a := by
          rcases hF_ex hρ hΔ with ⟨r, hr⟩
          exact ⟨r, hr, (RedTerm_of_LogRelAt (derivF hρ hΔ r hr) _).mp ha⟩
        have hb' : RelFHasTerm relF ρ Δ b := by
          rcases hF_ex hρ hΔ with ⟨r, hr⟩
          exact ⟨r, hr, (RedTerm_of_LogRelAt (derivF hρ hΔ r hr) _).mp hb⟩
        have hab' : RelFEqTerm relF ρ Δ a b := by
          rcases hF_ex hρ hΔ with ⟨r, hr⟩
          exact ⟨r, hr, (RedTermEq_of_LogRelAt (derivF hρ hΔ r hr) _).mp hab⟩
        rcases Gext hρ hΔ ha' hb' hab' with ⟨s, hs, hB⟩
        exact ⟨s, derivG hρ hΔ ha' s hs, hB⟩
  | emb hlt _ => cases hlt

/-- Reducible substitution of `Π`-types (`substSΠ₁`). -/
theorem substSPi₁ {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {F G t : Term}
    (pPi : RedType eqrel l Γ (.pi F G))
    (pF : RedType eqrel l' Γ F)
    (ht : RedTerm pF t) :
    RedType eqrel l Γ (subst0 G t) := by
  have hGeq : subst0 (wk (.lift .id) G) t = subst0 G t := by
    rw [wk_lift_id]
  cases l with
  | zero =>
      have piA := elimPiAt_zero (.refl (escape pPi)) pPi
      have wfΓ : CtxWf Γ := wfType piA.hF
      have ht_id : RedTerm (piA.redF .id wfΓ) t :=
        irrelevanceTerm' (wk_id F).symm pF (piA.redF .id wfΓ) ht
      exact irrelevance' hGeq (piA.redG .id wfΓ ht_id)
  | one =>
      rcases elimPiAt' (.refl (escape pPi)) pPi with ⟨l₀, piA⟩
      have wfΓ : CtxWf Γ := wfType piA.hF
      have ht_id : RedTerm (piA.redF .id wfΓ) t :=
        irrelevanceTerm' (wk_id F).symm pF (piA.redF .id wfΓ) ht
      exact maybeEmb (irrelevance' hGeq (piA.redG .id wfΓ ht_id))

/-- Reducible substitution of `Π`-type congruence (`substSΠ₂`). -/
theorem substSPi₂ {eqrel : EqRelSet} {l l' l'' l''' : TypeLevel} {Γ : Context}
    {F F' G G' t t' : Term}
    (pPi : RedType eqrel l Γ (.pi F G))
    (pPiEq : RedEq pPi (.pi F' G'))
    (pF : RedType eqrel l' Γ F)
    (pF' : RedType eqrel l' Γ F')
    (ht : RedTerm pF t)
    (ht' : RedTerm pF' t')
    (htt' : RedTermEq pF t t')
    (pGt : RedType eqrel l'' Γ (subst0 G t))
    (pG't' : RedType eqrel l''' Γ (subst0 G' t')) :
    RedEq pGt (subst0 G' t') := by
  rcases elimPiAt' (.refl (escape pPi)) pPi with ⟨l₀, piA⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ rel ↦ LogRelAt eqrel l₀ Δ (wk ρ F) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ a rel ↦ LogRelAt eqrel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel
  have hAt : LogRelAt eqrel l₀ Γ (.pi F G) (RedPiRel eqrel Γ F G relF₀ relG₀) :=
    .pi piA.D piA.hF piA.hG piA.AeqA relF₀ relG₀
      piA.redF (fun _ _ _ h ↦ h) piA.redG (fun _ _ _ _ h ↦ h) piA.Gext
  have pPi₀ : RedType eqrel l₀ Γ (.pi F G) := ⟨_, hAt⟩
  have hPiEq_rel : RedPiEq eqrel Γ F G relF₀ relG₀ (.pi F' G') :=
    (RedEq_of_LogRelAt hAt pPi₀).mp (irrelevanceEq pPi pPi₀ pPiEq)
  rcases hPiEq_rel with ⟨F₂, G₂, D', _, FeqF', GeqG'⟩
  have hPi₂ : Term.pi F' G' = Term.pi F₂ G₂ := whnfRedStar D' .pi
  injection hPi₂ with hF'F₂ hG'G₂
  subst hF'F₂ hG'G₂
  have wfΓ : CtxWf Γ := wfType piA.hF
  have pF_id : RedType eqrel l₀ Γ (wk .id F) := piA.redF .id wfΓ
  have ht_id : RedTerm pF_id t := irrelevanceTerm' (wk_id F).symm pF pF_id ht
  have pFF'_id : RedEq pF_id (wk .id F') := FeqF' .id wfΓ
  have ht'_id : RedTerm pF_id t' :=
    convTerm₂' (wk_id F').symm pF_id pF' pFF'_id ht'
  have htt'_id : RedTermEq pF_id t t' :=
    irrelevanceEqTerm' (wk_id F).symm pF pF_id htt'
  have pGt_id : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) t) :=
    piA.redG .id wfΓ ht_id
  have pGt'_id : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) t') :=
    piA.redG .id wfΓ ht'_id
  have hGt_Gt' : RedEq pGt_id (subst0 (wk (.lift .id) G) t') :=
    piA.Gext .id wfΓ ht_id ht'_id htt'_id
  have hGt'_G't' : RedEq pGt'_id (subst0 (wk (.lift .id) G') t') :=
    GeqG' .id wfΓ ht'_id
  have hGeq : subst0 (wk (.lift .id) G) t = subst0 G t := by
    rw [wk_lift_id]
  have hG'eq : subst0 (wk (.lift .id) G') t' = subst0 G' t' := by
    rw [wk_lift_id]
  exact irrelevanceEq' hGeq pGt_id pGt
    (transEq pGt_id pGt'_id pG't' hGt_Gt' (irrelevanceEqR' hG'eq pGt'_id hGt'_G't'))

/-- Valid substitution of `Π`-types (`substSΠ`). -/
theorem substSPi {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t : Term}
    (hF : ValidType eqrel l Γ F)
    (hPi : ValidType eqrel l Γ (.pi F G))
    (ht : ValidTerm hF t) :
    ValidType eqrel l Γ (subst0 G t) := by
  intro Δ σ hΔ hσ
  have pGt := substSPi₁ (hPi hΔ hσ).red (hF hΔ hσ).red (ht hΔ hσ).term
  have pGt' : RedType eqrel l Δ (subst σ (subst0 G t)) :=
    irrelevance' (singleSubstLift G t).symm pGt
  refine ⟨pGt', fun {σ'} hσ' hσσ' ↦ ?_⟩
  have pGt_σ' := substSPi₁ (hPi hΔ hσ').red (hF hΔ hσ').red (ht hΔ hσ').term
  exact irrelevanceEq'' (singleSubstLift G t).symm (singleSubstLift G t).symm pGt pGt'
    (substSPi₂ (hPi hΔ hσ).red ((hPi hΔ hσ).eq hσ' hσσ')
      (hF hΔ hσ).red (hF hΔ hσ').red
      (ht hΔ hσ).term (ht hΔ hσ').term ((ht hΔ hσ).eq hσ' hσσ')
      pGt pGt_σ')

/-- Valid substitution of `Π`-congruence (`substSΠEq`). -/
theorem substSPiEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G F' G' t u : Term}
    (hF : ValidType eqrel l Γ F)
    (hF' : ValidType eqrel l Γ F')
    (hPi : ValidType eqrel l Γ (.pi F G))
    (hPi' : ValidType eqrel l Γ (.pi F' G'))
    (hPiEq : ValidTypeEq hPi (.pi F' G'))
    (ht : ValidTerm hF t)
    (hu : ValidTerm hF' u)
    (htu : ValidTermEq hF t u) :
    ValidTypeEq (substSPi hF hPi ht) (subst0 G' u) := by
  intro Δ σ hΔ hσ
  have hGt : ValidType eqrel l Γ (subst0 G t) := substSPi hF hPi ht
  have pGt := substSPi₁ (hPi hΔ hσ).red (hF hΔ hσ).red (ht hΔ hσ).term
  have pG'u := substSPi₁ (hPi' hΔ hσ).red (hF' hΔ hσ).red (hu hΔ hσ).term
  exact irrelevanceEq'' (singleSubstLift G t).symm (singleSubstLift G' u).symm
    pGt (hGt hΔ hσ).red
    (substSPi₂ (hPi hΔ hσ).red (hPiEq hΔ hσ)
      (hF hΔ hσ).red (hF' hΔ hσ).red
      (ht hΔ hσ).term (hu hΔ hσ).term (htu hΔ hσ)
      pGt pG'u)

/-!
## `Π`-Type Introductions (`Definition/LogicalRelation/Substitution/Introductions/Pi.agda`)
-/

/-- Validity of `Π F ▹ G` (`Πᵛ`). -/
theorem piValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G) :
    ValidType eqrel l Γ (.pi F G) := by
  intro Δ σ hΔ hσ
  have pσF := (hF hΔ hσ).red
  have wfF : TypeWf Δ (subst σ F) := escape pσF
  have pσG := (hG (.cons hΔ wfF) (liftSubstS hΔ hF hσ)).red
  have wfG : TypeWf (subst σ F :: Δ) (subst (liftSubst σ) G) := escape pσG
  have wfPi : TypeWf Δ (.pi (subst σ F) (subst (liftSubst σ) G)) := .pi wfF wfG
  have hPiEq : eqrel.TypeEqRel Δ (.pi (subst σ F) (subst (liftSubst σ) G))
      (.pi (subst σ F) (subst (liftSubst σ) G)) :=
    eqrel.piCong wfF (escapeEq pσF (reflEq pσF)) (escapeEq pσG (reflEq pσG))
  let relF : Wk → Context → RedRel → Prop :=
    fun ρ Δ₁ rel ↦ LogRelAt eqrel l Δ₁ (wk ρ (subst σ F)) rel
  let relG : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ₁ a rel ↦ LogRelAt eqrel l Δ₁ (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) a) rel
  have pF_wk : ∀ {ρ Δ₁}, WkCtx ρ Δ₁ Δ → CtxWf Δ₁ → RedType eqrel l Δ₁ (wk ρ (subst σ F)) :=
    fun hρ hΔ₁ ↦ wkRed hρ hΔ₁ pσF
  have pG_wk : ∀ {ρ Δ₁ a} (hρ : WkCtx ρ Δ₁ Δ) (hΔ₁ : CtxWf Δ₁),
      RedTerm (pF_wk hρ hΔ₁) a →
      RedType eqrel l Δ₁ (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) a) := by
    intro ρ Δ₁ a hρ hΔ₁ ha
    have hρσ : ValidSubst eqrel Δ₁ (wkSubst ρ σ) Γ := wkSubstS hρ hΔ₁ hσ
    have ha' : RedTerm (hF hΔ₁ hρσ).red a :=
      irrelevanceTerm' (wk_subst F) (pF_wk hρ hΔ₁) (hF hΔ₁ hρσ).red ha
    have hρσa : ValidSubst eqrel Δ₁ (consSubst (wkSubst ρ σ) a) (F :: Γ) :=
      consSubstS hΔ₁ hρσ hF ha'
    exact irrelevance' (singleSubstWkComp a σ G).symm (hG hΔ₁ hρσa).red
  have hGext : ∀ {ρ Δ₁ a b} (hρ : WkCtx ρ Δ₁ Δ) (hΔ₁ : CtxWf Δ₁)
      (ha : RedTerm (pF_wk hρ hΔ₁) a) (hb : RedTerm (pF_wk hρ hΔ₁) b),
      RedTermEq (pF_wk hρ hΔ₁) a b →
      RedEq (pG_wk hρ hΔ₁ ha) (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) b) := by
    intro ρ Δ₁ a b hρ hΔ₁ ha hb hab
    have hρσ : ValidSubst eqrel Δ₁ (wkSubst ρ σ) Γ := wkSubstS hρ hΔ₁ hσ
    have ha' : RedTerm (hF hΔ₁ hρσ).red a :=
      irrelevanceTerm' (wk_subst F) (pF_wk hρ hΔ₁) (hF hΔ₁ hρσ).red ha
    have hb' : RedTerm (hF hΔ₁ hρσ).red b :=
      irrelevanceTerm' (wk_subst F) (pF_wk hρ hΔ₁) (hF hΔ₁ hρσ).red hb
    have hab' : RedTermEq (hF hΔ₁ hρσ).red a b :=
      irrelevanceEqTerm' (wk_subst F) (pF_wk hρ hΔ₁) (hF hΔ₁ hρσ).red hab
    have hρσa : ValidSubst eqrel Δ₁ (consSubst (wkSubst ρ σ) a) (F :: Γ) :=
      consSubstS hΔ₁ hρσ hF ha'
    have hρσb : ValidSubst eqrel Δ₁ (consSubst (wkSubst ρ σ) b) (F :: Γ) :=
      consSubstS hΔ₁ hρσ hF hb'
    have hρσab : ValidSubstEq eqrel Δ₁ (consSubst (wkSubst ρ σ) a) (consSubst (wkSubst ρ σ) b) (F :: Γ) :=
      ValidSubstEq.cons (reflSubst hρσ) (hF hΔ₁ hρσ).red hab'
    exact irrelevanceEq'' (singleSubstWkComp a σ G).symm (singleSubstWkComp b σ G).symm
      (hG hΔ₁ hρσa).red (pG_wk hρ hΔ₁ ha)
      ((hG hΔ₁ hρσa).eq hρσb hρσab)
  have hLogPi : LogRelAt eqrel l Δ (.pi (subst σ F) (subst (liftSubst σ) G))
      (RedPiRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF relG) :=
    .pi (idRedWf wfPi) wfF wfG hPiEq relF relG
      (fun hρ hΔ₁ ↦ pF_wk hρ hΔ₁)
      (fun _ _ _ hr ↦ hr)
      (fun hρ hΔ₁ ha ↦ pG_wk hρ hΔ₁ ha)
      (fun _ _ _ _ hs ↦ hs)
      (fun hρ hΔ₁ ha hb hab ↦ hGext hρ hΔ₁ ha hb hab)
  refine ⟨⟨RedPiRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF relG, hLogPi⟩,
    fun {σ'} hσ' hσσ' ↦ ?_⟩
  have pσ'F := (hF hΔ hσ').red
  have wfF' : TypeWf Δ (subst σ' F) := escape pσ'F
  have pσ'G := (hG (.cons hΔ wfF') (liftSubstS hΔ hF hσ')).red
  have wfG' : TypeWf (subst σ' F :: Δ) (subst (liftSubst σ') G) := escape pσ'G
  have wfPi' : TypeWf Δ (.pi (subst σ' F) (subst (liftSubst σ') G)) := .pi wfF' wfG'
  have wfΔF : CtxWf (subst σ F :: Δ) := .cons hΔ wfF
  have hwk1σ := wk1SubstS hΔ wfF hσ
  have hwk1σ' := wk1SubstS hΔ wfF hσ'
  have hwk1σσ' := wk1SubstSEq hΔ wfF hσσ'
  have pF_wk1σ := (hF wfΔF hwk1σ).red
  have pF_wk1σ' := (hF wfΔF hwk1σ').red
  have hLookup0 : Member 0 (subst (wk1Subst σ) F) (subst σ F :: Δ) :=
    member_here_wk1Subst σ F Δ
  have var0 : HasType (subst σ F :: Δ) (.var 0) (subst (wk1Subst σ) F) :=
    .var wfΔF hLookup0
  have var0' : HasType (subst σ F :: Δ) (.var 0) (subst (wk1Subst σ') F) :=
    .conv var0 (eqrel.typeToEq (escapeEq pF_wk1σ ((hF wfΔF hwk1σ).eq hwk1σ' hwk1σσ')))
  have hLiftσ'_in_ΔF : ValidSubst eqrel (subst σ F :: Δ) (liftSubst σ') (F :: Γ) :=
    ValidSubst.cons hwk1σ' pF_wk1σ'
      (neuTerm pF_wk1σ' (.var 0) var0' (eqrel.varRefl var0'))
  have hLiftσσ'_in_ΔF : ValidSubstEq eqrel (subst σ F :: Δ) (liftSubst σ) (liftSubst σ') (F :: Γ) :=
    ValidSubstEq.cons hwk1σσ' pF_wk1σ
      (neuEqTerm pF_wk1σ (.var 0) (.var 0) var0 var0 (eqrel.varRefl var0))
  have hPiEq_σσ' : eqrel.TypeEqRel Δ (.pi (subst σ F) (subst (liftSubst σ) G))
      (.pi (subst σ' F) (subst (liftSubst σ') G)) :=
    eqrel.piCong wfF
      (escapeEq pσF ((hF hΔ hσ).eq hσ' hσσ'))
      (escapeEq pσG ((hG wfΔF (liftSubstS hΔ hF hσ)).eq hLiftσ'_in_ΔF hLiftσσ'_in_ΔF))
  refine ⟨RedPiRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF relG, hLogPi,
    .mk (subst σ' F) (subst (liftSubst σ') G) (.refl wfPi') hPiEq_σσ'
      (fun hρ hΔ₁ ↦ wkRedEq hρ hΔ₁ pσF ((hF hΔ hσ).eq hσ' hσσ'))
      (fun {ρ Δ₁ a} hρ hΔ₁ ha ↦ ?_)⟩
  have hρσ : ValidSubst eqrel Δ₁ (wkSubst ρ σ) Γ := wkSubstS hρ hΔ₁ hσ
  have hρσ' : ValidSubst eqrel Δ₁ (wkSubst ρ σ') Γ := wkSubstS hρ hΔ₁ hσ'
  have hρσσ' : ValidSubstEq eqrel Δ₁ (wkSubst ρ σ) (wkSubst ρ σ') Γ :=
    wkSubstSEq hρ hΔ₁ hσσ'
  have ha' : RedTerm (hF hΔ₁ hρσ).red a :=
    irrelevanceTerm' (wk_subst F) (pF_wk hρ hΔ₁) (hF hΔ₁ hρσ).red ha
  have ha'' : RedTerm (hF hΔ₁ hρσ').red a :=
    convTerm₁ (hF hΔ₁ hρσ).red (hF hΔ₁ hρσ').red ((hF hΔ₁ hρσ).eq hρσ' hρσσ') ha'
  have hρσa : ValidSubst eqrel Δ₁ (consSubst (wkSubst ρ σ) a) (F :: Γ) :=
    consSubstS hΔ₁ hρσ hF ha'
  have hρσ'a : ValidSubst eqrel Δ₁ (consSubst (wkSubst ρ σ') a) (F :: Γ) :=
    consSubstS hΔ₁ hρσ' hF ha''
  have hρσa_eq : ValidSubstEq eqrel Δ₁ (consSubst (wkSubst ρ σ) a) (consSubst (wkSubst ρ σ') a) (F :: Γ) :=
    consSubstSEq hΔ₁ hρσ hρσσ' hF ha'
  exact irrelevanceEq'' (singleSubstWkComp a σ G).symm (singleSubstWkComp a σ' G).symm
    (hG hΔ₁ hρσa).red (pG_wk hρ hΔ₁ ha)
    ((hG hΔ₁ hρσa).eq hρσ'a hρσa_eq)

/-- Validity of `Π`-congruence (`Π-congᵛ`). -/
theorem piCongValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G H E : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (hH : ValidType eqrel l Γ H)
    (hE : ValidType eqrel l (H :: Γ) E)
    (hFH : ValidTypeEq hF H)
    (hGE : ValidTypeEq hG E) :
    ValidTypeEq (piValid hF hG) (.pi H E) := by
  intro Δ σ hΔ hσ
  have hPiValid : ValidType eqrel l Γ (.pi F G) := piValid hF hG
  have pPiFG := (hPiValid hΔ hσ).red
  rcases elimPiAt' (.refl (escape pPiFG)) pPiFG with ⟨l₀, piA⟩
  have pσF := (hF hΔ hσ).red
  have wfσF : TypeWf Δ (subst σ F) := escape pσF
  have pσG := (hG (.cons hΔ wfσF) (liftSubstS hΔ hF hσ)).red
  have wfσH : TypeWf Δ (subst σ H) := escape (hH hΔ hσ).red
  have wfσE : TypeWf (subst σ H :: Δ) (subst (liftSubst σ) E) :=
    escape (hE (.cons hΔ wfσH) (liftSubstS hΔ hH hσ)).red
  have hσFH : eqrel.TypeEqRel Δ (subst σ F) (subst σ H) :=
    escapeEq pσF (hFH hΔ hσ)
  have hσGE : eqrel.TypeEqRel (subst σ F :: Δ) (subst (liftSubst σ) G) (subst (liftSubst σ) E) :=
    escapeEq pσG (hGE (.cons hΔ wfσF) (liftSubstS hΔ hF hσ))
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ₁ rel ↦ LogRelAt eqrel l₀ Δ₁ (wk ρ (subst σ F)) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ₁ a rel ↦ LogRelAt eqrel l₀ Δ₁ (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) a) rel
  have hLogPi₀ : LogRelAt eqrel l₀ Δ (.pi (subst σ F) (subst (liftSubst σ) G))
      (RedPiRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀) :=
    .pi piA.D piA.hF piA.hG piA.AeqA relF₀ relG₀
      piA.redF (fun _ _ _ h ↦ h) piA.redG (fun _ _ _ _ h ↦ h) piA.Gext
  have pPiFG₀ : RedType eqrel l₀ Δ (.pi (subst σ F) (subst (liftSubst σ) G)) :=
    ⟨RedPiRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀, hLogPi₀⟩
  have hRes₀ : RedEq pPiFG₀ (.pi (subst σ H) (subst (liftSubst σ) E)) := by
    refine ⟨RedPiRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀, hLogPi₀,
      .mk (subst σ H) (subst (liftSubst σ) E) (.refl (.pi wfσH wfσE))
        (eqrel.piCong wfσF hσFH hσGE)
        (fun {ρ Δ₁} hρ hΔ₁ ↦ ?_)
        (fun {ρ Δ₁ a} hρ hΔ₁ ha ↦ ?_)⟩
    · have hρσ := wkSubstS hρ hΔ₁ hσ
      exact irrelevanceEq'' (wk_subst F).symm (wk_subst H).symm
        (hF hΔ₁ hρσ).red (piA.redF hρ hΔ₁) (hFH hΔ₁ hρσ)
    · have hρσ := wkSubstS hρ hΔ₁ hσ
      have ha' : RedTerm (hF hΔ₁ hρσ).red a :=
        irrelevanceTerm' (wk_subst F) (piA.redF hρ hΔ₁) (hF hΔ₁ hρσ).red ha
      have hρσa := consSubstS hΔ₁ hρσ hF ha'
      exact irrelevanceEq'' (singleSubstWkComp a σ G).symm (singleSubstWkComp a σ E).symm
        (hG hΔ₁ hρσa).red (piA.redG hρ hΔ₁ ha) (hGE hΔ₁ hρσa)
  exact irrelevanceEq pPiFG₀ pPiFG hRes₀

/-- Validity of `Π F ▹ G` as a term of `U` (`Πᵗᵛ`). -/
theorem piTermValid {eqrel : EqRelSet} {Γ : Context} {F G : Term}
    (hF : ValidType eqrel .one Γ F)
    (hU : ValidType eqrel .one (F :: Γ) .univ)
    (hFt : ValidTerm (UValid (eqrel := eqrel) (Γ := Γ)) F)
    (hGt : ValidTerm hU G) :
    ValidTerm (UValid (eqrel := eqrel) (Γ := Γ)) (.pi F G) := by
  intro Δ σ hΔ hσ
  have hLiftσ := liftSubstS hΔ hF hσ
  have wfF : TypeWf Δ (subst σ F) := escape (hF hΔ hσ).red
  have pUΔ : RedType eqrel .one Δ .univ := redUOne hΔ
  have wfFt : HasType Δ (subst σ F) .univ := escapeTerm pUΔ (hFt hΔ hσ).term
  have hFFt : eqrel.TermEqRel Δ (subst σ F) (subst σ F) .univ :=
    escapeTermEq pUΔ (reflEqTerm pUΔ (hFt hΔ hσ).term)
  have pU_ΔF := (hU (.cons hΔ wfF) hLiftσ).red
  have wfGt : HasType (subst σ F :: Δ) (subst (liftSubst σ) G) .univ :=
    escapeTerm pU_ΔF (hGt (.cons hΔ wfF) hLiftσ).term
  have hGGt : eqrel.TermEqRel (subst σ F :: Δ) (subst (liftSubst σ) G) (subst (liftSubst σ) G) .univ :=
    escapeTermEq pU_ΔF (reflEqTerm pU_ΔF (hGt (.cons hΔ wfF) hLiftσ).term)
  have hF₀ : ValidType eqrel .zero Γ F := univValid UValid hFt
  have hG₀ : ValidType eqrel .zero (F :: Γ) G := univValid hU hGt
  have hPi₀Valid : ValidType eqrel .zero Γ (.pi F G) := piValid hF₀ hG₀
  have hPiFG₀ := hPi₀Valid hΔ hσ
  have wfPit : HasType Δ (.pi (subst σ F) (subst (liftSubst σ) G)) .univ :=
    .pi wfFt wfGt
  rcases hPiFG₀.red with ⟨relPi₀, hLogPi₀⟩
  refine ⟨⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) Δ, .U ⟨.zeroLT, hΔ⟩,
      .mk (.pi (subst σ F) (subst (liftSubst σ) G)) (idRedTermWf wfPit)
        .pi (eqrel.piTermCong wfF hFFt hGGt) ⟨relPi₀, hLogPi₀⟩⟩,
    fun {σ'} hσ' hσσ' ↦ ?_⟩
  have hLiftσ' := liftSubstS hΔ hF hσ'
  have hwk1σ := wk1SubstS hΔ wfF hσ
  have hwk1σ' := wk1SubstS hΔ wfF hσ'
  have wfΔF : CtxWf (subst σ F :: Δ) := .cons hΔ wfF
  have hLookup0 : Member 0 (subst (wk1Subst σ) F) (subst σ F :: Δ) :=
    member_here_wk1Subst σ F Δ
  have var0 : HasType (subst σ F :: Δ) (.var 0) (subst (wk1Subst σ) F) :=
    .var wfΔF hLookup0
  have var0' : HasType (subst σ F :: Δ) (.var 0) (subst (wk1Subst σ') F) :=
    .conv var0 (eqrel.typeToEq (escapeEq (hF wfΔF hwk1σ).red
      ((hF wfΔF hwk1σ).eq hwk1σ' (wk1SubstSEq hΔ wfF hσσ'))))
  have hLiftσ'_in_ΔF : ValidSubst eqrel (subst σ F :: Δ) (liftSubst σ') (F :: Γ) :=
    ValidSubst.cons hwk1σ' (hF wfΔF hwk1σ').red
      (neuTerm (hF wfΔF hwk1σ').red (.var 0) var0' (eqrel.varRefl var0'))
  have wfF' : TypeWf Δ (subst σ' F) := escape (hF hΔ hσ').red
  have wfFt' : HasType Δ (subst σ' F) .univ := escapeTerm pUΔ (hFt hΔ hσ').term
  have wfGt' : HasType (subst σ' F :: Δ) (subst (liftSubst σ') G) .univ :=
    escapeTerm (hU (.cons hΔ wfF') hLiftσ').red (hGt (.cons hΔ wfF') hLiftσ').term
  have hFF't : eqrel.TermEqRel Δ (subst σ F) (subst σ' F) .univ :=
    escapeTermEq pUΔ ((hFt hΔ hσ).eq hσ' hσσ')
  have hGG't : eqrel.TermEqRel (subst σ F :: Δ) (subst (liftSubst σ) G) (subst (liftSubst σ') G) .univ :=
    escapeTermEq pU_ΔF ((hGt wfΔF hLiftσ).eq hLiftσ'_in_ΔF (liftSubstSEq hΔ hF hσ hσσ'))
  have hPiFG₀' := hPi₀Valid hΔ hσ'
  have hPiEq₀ := hPiFG₀.eq hσ' hσσ'
  rcases hPiEq₀ with ⟨rel₀, hLog₀, hEq₀⟩
  exact ⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) Δ, .U ⟨.zeroLT, hΔ⟩,
    .mk (.pi (subst σ F) (subst (liftSubst σ) G))
      (.pi (subst σ' F) (subst (liftSubst σ') G))
      (idRedTermWf wfPit) (idRedTermWf (.pi wfFt' wfGt'))
      .pi .pi (eqrel.piTermCong wfF hFF't hGG't)
      rel₀ hLog₀ hPiFG₀'.red hEq₀⟩

/-- Validity of `Π`-congruence as a term equality in `U` (`Π-congᵗᵛ`). -/
theorem piCongTermValid {eqrel : EqRelSet} {Γ : Context} {F G H E : Term}
    (hF : ValidType eqrel .one Γ F)
    (hH : ValidType eqrel .one Γ H)
    (hUF : ValidType eqrel .one (F :: Γ) .univ)
    (hUH : ValidType eqrel .one (H :: Γ) .univ)
    (hFt : ValidTerm (UValid (eqrel := eqrel) (Γ := Γ)) F)
    (hGt : ValidTerm hUF G)
    (hHt : ValidTerm (UValid (eqrel := eqrel) (Γ := Γ)) H)
    (hEt : ValidTerm hUH E)
    (hFHt : ValidTermEq (UValid (eqrel := eqrel) (Γ := Γ)) F H)
    (hGEt : ValidTermEq hUF G E) :
    ValidTermEq (UValid (eqrel := eqrel) (Γ := Γ)) (.pi F G) (.pi H E) := by
  intro Δ σ hΔ hσ
  have wfF : TypeWf Δ (subst σ F) := escape (hF hΔ hσ).red
  have wfH : TypeWf Δ (subst σ H) := escape (hH hΔ hσ).red
  have hLiftFσ := liftSubstS hΔ hF hσ
  have hLiftHσ := liftSubstS hΔ hH hσ
  have hF_u : ValidType eqrel .zero Γ F := univValid UValid hFt
  have hG_u : ValidType eqrel .zero (F :: Γ) G := univValid hUF hGt
  have hH_u : ValidType eqrel .zero Γ H := univValid UValid hHt
  have hE_u : ValidType eqrel .zero (H :: Γ) E := univValid hUH hEt
  have hFH_u : ValidTypeEq hF_u H := univEqValid UValid hF_u hFHt
  have hGE_u : ValidTypeEq hG_u E := univEqValid hUF hG_u hGEt
  have pUΔ : RedType eqrel .one Δ .univ := redUOne hΔ
  have wfPiFG : HasType Δ (.pi (subst σ F) (subst (liftSubst σ) G)) .univ :=
    .pi (escapeTerm pUΔ (hFt hΔ hσ).term)
      (escapeTerm (hUF (.cons hΔ wfF) hLiftFσ).red (hGt (.cons hΔ wfF) hLiftFσ).term)
  have wfPiHE : HasType Δ (.pi (subst σ H) (subst (liftSubst σ) E)) .univ :=
    .pi (escapeTerm pUΔ (hHt hΔ hσ).term)
      (escapeTerm (hUH (.cons hΔ wfH) hLiftHσ).red (hEt (.cons hΔ wfH) hLiftHσ).term)
  have hPiEq₀ := piCongValid hF_u hG_u hH_u hE_u hFH_u hGE_u hΔ hσ
  rcases hPiEq₀ with ⟨rel₀, hLog₀, hEq₀⟩
  have hPiH_u : ValidType eqrel .zero Γ (.pi H E) := piValid hH_u hE_u
  exact ⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) Δ, .U ⟨.zeroLT, hΔ⟩,
    .mk (.pi (subst σ F) (subst (liftSubst σ) G))
      (.pi (subst σ H) (subst (liftSubst σ) E))
      (idRedTermWf wfPiFG) (idRedTermWf wfPiHE)
      .pi .pi
      (eqrel.piTermCong wfF
        (escapeTermEq pUΔ (hFHt hΔ hσ))
        (escapeTermEq (hUF (.cons hΔ wfF) hLiftFσ).red (hGEt (.cons hΔ wfF) hLiftFσ)))
      rel₀ hLog₀ (hPiH_u hΔ hσ).red hEq₀⟩

/-- Validity of non-dependent function types `F ▹▹ G` (`▹▹ᵛ`). -/
theorem arrValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l Γ G) :
    ValidType eqrel l Γ (arr F G) :=
  piValid hF (wk1Valid hG)

/-- Validity of non-dependent function type congruence (`▹▹-congᵛ`). -/
theorem arrCongValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F F' G G' : Term}
    (hF : ValidType eqrel l Γ F)
    (hF' : ValidType eqrel l Γ F')
    (hFF' : ValidTypeEq hF F')
    (hG : ValidType eqrel l Γ G)
    (hG' : ValidType eqrel l Γ G')
    (hGG' : ValidTypeEq hG G') :
    ValidTypeEq (arrValid hF hG) (arr F' G') :=
  piCongValid hF (wk1Valid hG) hF' (wk1Valid hG') hFF' (wk1ValidEq hG hGG')

/-!
## Application Introductions (`Definition/LogicalRelation/Substitution/Introductions/Application.agda`)
-/

/-- Application of valid terms (`appᵛ`). -/
theorem appValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t u : Term}
    (hF : ValidType eqrel l Γ F)
    (hPi : ValidType eqrel l Γ (.pi F G))
    (ht : ValidTerm hPi t)
    (hu : ValidTerm hF u) :
    ValidTerm (substSPi hF hPi hu) (.app t u) := by
  intro Δ σ hΔ hσ
  have hGu : ValidType eqrel l Γ (subst0 G u) := substSPi hF hPi hu
  have pF := (hF hΔ hσ).red
  have pPi := (hPi hΔ hσ).red
  have pt := (ht hΔ hσ).term
  have pu := (hu hΔ hσ).term
  have pGu := (hGu hΔ hσ).red
  have pGu' : RedType eqrel l Δ (subst0 (subst (liftSubst σ) G) (subst σ u)) :=
    irrelevance' (singleSubstLift G u) pGu
  refine ⟨irrelevanceTerm' (singleSubstLift G u).symm pGu' pGu (appTerm pF pGu' pPi pt pu),
    fun {σ'} hσ' hσσ' ↦ ?_⟩
  have pu' : RedTerm pF (subst σ' u) :=
    convTerm₂ pF (hF hΔ hσ').red ((hF hΔ hσ).eq hσ' hσσ') (hu hΔ hσ').term
  exact irrelevanceEqTerm' (singleSubstLift G u).symm pGu' pGu
    (appCongTerm pF pGu' pPi ((ht hΔ hσ).eq hσ' hσσ') pu pu' ((hu hΔ hσ).eq hσ' hσσ'))

/-- Application congruence of valid terms (`app-congᵛ`). -/
theorem appCongValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t u a b : Term}
    (hF : ValidType eqrel l Γ F)
    (hPi : ValidType eqrel l Γ (.pi F G))
    (htu : ValidTermEq hPi t u)
    (ha : ValidTerm hF a)
    (hb : ValidTerm hF b)
    (hab : ValidTermEq hF a b) :
    ValidTermEq (substSPi hF hPi ha) (.app t a) (.app u b) := by
  intro Δ σ hΔ hσ
  have hGa : ValidType eqrel l Γ (subst0 G a) := substSPi hF hPi ha
  have pF := (hF hΔ hσ).red
  have pGa := (hGa hΔ hσ).red
  have pGa' : RedType eqrel l Δ (subst0 (subst (liftSubst σ) G) (subst σ a)) :=
    irrelevance' (singleSubstLift G a) pGa
  have pPi := (hPi hΔ hσ).red
  have pa := (ha hΔ hσ).term
  exact irrelevanceEqTerm' (singleSubstLift G a).symm pGa' pGa
    (appCongTerm pF pGa' pPi (htu hΔ hσ) pa (hb hΔ hσ).term (hab hΔ hσ))

end Abel2018


namespace Abel2018

/-!
# Lambda and Natrec Introductions, and the Fundamental Theorem

This module translates:
- `Definition/LogicalRelation/Substitution/Introductions/Lambda.agda`
- `Definition/LogicalRelation/Substitution/Introductions/Natrec.agda`
- `Definition/LogicalRelation/Fundamental.agda`
- `Definition/LogicalRelation/Fundamental/Reducibility.agda`
-/

/-!
## Lambda Introductions (`Definition/LogicalRelation/Substitution/Introductions/Lambda.agda`)
-/

theorem lamRedTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ Δ : Context} {F G t : Term} {σ : Subst}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (ht : ValidTerm hG t)
    (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ) :
    RedTerm ((piValid hF hG) hΔ hσ).red (subst σ (.lam t)) := by
  have hPiFG : ValidType eqrel l Γ (.pi F G) := piValid hF hG
  have pPi := (hPiFG hΔ hσ).red
  have hLiftσ := liftSubstS hΔ hF hσ
  have pσF := (hF hΔ hσ).red
  have wfF : TypeWf Δ (subst σ F) := escape pσF
  have wfΔF : CtxWf (subst σ F :: Δ) := .cons hΔ wfF
  have wfwk1F : TypeWf (subst σ F :: Δ) (wk (.step .id) (subst σ F)) :=
    wkTypeWf (.step .id) wfΔF wfF
  have pσG := (hG wfΔF hLiftσ).red
  have wfG : TypeWf (subst σ F :: Δ) (subst (liftSubst σ) G) := escape pσG
  have pσt := (ht wfΔF hLiftσ).term
  have wft : HasType (subst σ F :: Δ) (subst (liftSubst σ) t) (subst (liftSubst σ) G) :=
    escapeTerm pσG pσt
  have wk1t0 : RedTerm pσG (subst0 (wk (.lift (.step .id)) (subst (liftSubst σ) t)) (.var 0)) :=
    irrelevanceTerm'' rfl (wkSingleSubstId (subst (liftSubst σ) t)).symm pσG pσG pσt
  have hBetaRaw : Step (subst σ F :: Δ)
      (.app (.lam (wk (.lift (.step .id)) (subst (liftSubst σ) t))) (.var 0))
      (subst0 (wk (.lift (.step .id)) (subst (liftSubst σ) t)) (.var 0))
      (subst0 (wk (.lift (.step .id)) (subst (liftSubst σ) G)) (.var 0)) :=
    .beta wfwk1F
      (wkHasType (.lift (.step .id)) (.cons wfΔF wfwk1F) wft)
      (.var wfΔF .here)
  have hBeta : Step (subst σ F :: Δ)
      (.app (wk1 (.lam (subst (liftSubst σ) t))) (.var 0))
      (subst0 (wk (.lift (.step .id)) (subst (liftSubst σ) t)) (.var 0))
      (subst (liftSubst σ) G) := by
    have h := hBetaRaw
    rw [wkSingleSubstId (subst (liftSubst σ) G)] at h
    exact h
  have hEta : eqrel.TermEqRel Δ (.lam (subst (liftSubst σ) t)) (.lam (subst (liftSubst σ) t))
      (.pi (subst σ F) (subst (liftSubst σ) G)) :=
    eqrel.etaEq wfF (.lam wfF wft) (.lam wfF wft) .lam .lam
      (escapeTermEq pσG (reflEqTerm pσG (redSubstTerm hBeta pσG wk1t0).1))
  rcases elimPiAt' (.refl (escape pPi)) pPi with ⟨l₀, piA⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ₁ rel ↦ LogRelAt eqrel l₀ Δ₁ (wk ρ (subst σ F)) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ₁ a rel ↦ LogRelAt eqrel l₀ Δ₁ (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) a) rel
  have hAt : LogRelAt eqrel l₀ Δ (.pi (subst σ F) (subst (liftSubst σ) G))
      (RedPiRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀) :=
    .pi piA.D piA.hF piA.hG piA.AeqA relF₀ relG₀
      piA.redF (fun _ _ _ h ↦ h) piA.redG (fun _ _ _ _ h ↦ h) piA.Gext
  have pPi₀ : RedType eqrel l₀ Δ (.pi (subst σ F) (subst (liftSubst σ) G)) := ⟨_, hAt⟩
  have hPiTerm : RedPiTerm eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀
      (subst σ (.lam t)) := by
    refine .mk (.lam (subst (liftSubst σ) t)) (idRedTermWf (.lam wfF wft)) .lam hEta
      (fun {ρ Δ₁ a b} hρ hΔ₁ ha hb hab ↦ ?_)
      (fun {ρ Δ₁ a} hρ hΔ₁ ha ↦ ?_)
    · have hρσ := wkSubstS hρ hΔ₁ hσ
      have pF_ρ := piA.redF hρ hΔ₁
      have pF_ρσ := (hF hΔ₁ hρσ).red
      have ha' : RedTerm pF_ρσ a := irrelevanceTerm' (wk_subst F) pF_ρ pF_ρσ ha
      have hb' : RedTerm pF_ρσ b := irrelevanceTerm' (wk_subst F) pF_ρ pF_ρσ hb
      have hab' : RedTermEq pF_ρσ a b := irrelevanceEqTerm' (wk_subst F) pF_ρ pF_ρσ hab
      have wfF₁' : TypeWf Δ₁ (subst (wkSubst ρ σ) F) := escape pF_ρσ
      have wfF₁ : TypeWf Δ₁ (wk ρ (subst σ F)) := escape pF_ρ
      have hLiftρσ := liftSubstS hΔ₁ hF hρσ
      have pG₁ := (hG (.cons hΔ₁ wfF₁') hLiftρσ).red
      have hCtxEq : (subst (wkSubst ρ σ) F :: Δ₁) = (wk ρ (subst σ F) :: Δ₁) :=
        congrArg (fun x ↦ x :: Δ₁) (wk_subst F).symm
      have pG₁' : RedType eqrel l (wk ρ (subst σ F) :: Δ₁) (wk (.lift ρ) (subst (liftSubst σ) G)) :=
        irrelevanceΓ' hCtxEq (wk_subst_lift G).symm pG₁
      have pt₁' : RedTerm pG₁' (wk (.lift ρ) (subst (liftSubst σ) t)) :=
        irrelevanceTermΓ'' hCtxEq (wk_subst_lift G).symm (wk_subst_lift t).symm
          pG₁ pG₁' (ht (.cons hΔ₁ wfF₁') hLiftρσ).term
      have wfa : HasType Δ₁ a (wk ρ (subst σ F)) := escapeTerm pF_ρ ha
      have wfb : HasType Δ₁ b (wk ρ (subst σ F)) := escapeTerm pF_ρ hb
      have wft₁ : HasType (wk ρ (subst σ F) :: Δ₁)
          (wk (.lift ρ) (subst (liftSubst σ) t))
          (wk (.lift ρ) (subst (liftSubst σ) G)) :=
        escapeTerm pG₁' pt₁'
      have hρσa := consSubstS hΔ₁ hρσ hF ha'
      have hρσb := consSubstS hΔ₁ hρσ hF hb'
      have pGa' := (hG hΔ₁ hρσa).red
      have pGa := piA.redG hρ hΔ₁ ha
      have pta : RedTerm pGa (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) a) :=
        irrelevanceTerm'' (singleSubstWkComp a σ G).symm (singleSubstWkComp a σ t).symm
          pGa' pGa (ht hΔ₁ hρσa).term
      have pGb' := (hG hΔ₁ hρσb).red
      have pGb := piA.redG hρ hΔ₁ hb
      have ptb : RedTerm pGb (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) b) :=
        irrelevanceTerm'' (singleSubstWkComp b σ G).symm (singleSubstWkComp b σ t).symm
          pGb' pGb (ht hΔ₁ hρσb).term
      have hlam_a : RedTermEq pGa (.app (wk ρ (.lam (subst (liftSubst σ) t))) a)
          (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) a) :=
        (redSubstTerm (.beta wfF₁ wft₁ wfa) pGa pta).2
      have hGa_Gb : RedEq pGa (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) b) :=
        piA.Gext hρ hΔ₁ ha hb hab
      have hρσab : ValidSubstEq eqrel Δ₁ (consSubst (wkSubst ρ σ) a) (consSubst (wkSubst ρ σ) b) (F :: Γ) :=
        ValidSubstEq.cons (reflSubst hρσ) pF_ρσ hab'
      have hta_tb : RedTermEq pGa
          (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) a)
          (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) b) :=
        irrelevanceEqTerm'' (singleSubstWkComp a σ t).symm (singleSubstWkComp b σ t).symm
          (singleSubstWkComp a σ G).symm pGa' pGa ((ht hΔ₁ hρσa).eq hρσb hρσab)
      have htb_lam_b : RedTermEq pGa
          (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) b)
          (.app (wk ρ (.lam (subst (liftSubst σ) t))) b) :=
        convEqTerm₂ pGa pGb hGa_Gb
          (symEqTerm pGb (redSubstTerm (.beta wfF₁ wft₁ wfb) pGb ptb).2)
      exact transEqTerm pGa hlam_a (transEqTerm pGa hta_tb htb_lam_b)
    · have hρσ := wkSubstS hρ hΔ₁ hσ
      have pF_ρ := piA.redF hρ hΔ₁
      have pF_ρσ := (hF hΔ₁ hρσ).red
      have ha' : RedTerm pF_ρσ a := irrelevanceTerm' (wk_subst F) pF_ρ pF_ρσ ha
      have wfF₁' : TypeWf Δ₁ (subst (wkSubst ρ σ) F) := escape pF_ρσ
      have wfF₁ : TypeWf Δ₁ (wk ρ (subst σ F)) := escape pF_ρ
      have hLiftρσ := liftSubstS hΔ₁ hF hρσ
      have pG₁ := (hG (.cons hΔ₁ wfF₁') hLiftρσ).red
      have hCtxEq : (subst (wkSubst ρ σ) F :: Δ₁) = (wk ρ (subst σ F) :: Δ₁) :=
        congrArg (fun x ↦ x :: Δ₁) (wk_subst F).symm
      have pG₁' : RedType eqrel l (wk ρ (subst σ F) :: Δ₁) (wk (.lift ρ) (subst (liftSubst σ) G)) :=
        irrelevanceΓ' hCtxEq (wk_subst_lift G).symm pG₁
      have pt₁' : RedTerm pG₁' (wk (.lift ρ) (subst (liftSubst σ) t)) :=
        irrelevanceTermΓ'' hCtxEq (wk_subst_lift G).symm (wk_subst_lift t).symm
          pG₁ pG₁' (ht (.cons hΔ₁ wfF₁') hLiftρσ).term
      have wfa : HasType Δ₁ a (wk ρ (subst σ F)) := escapeTerm pF_ρ ha
      have wft₁ : HasType (wk ρ (subst σ F) :: Δ₁)
          (wk (.lift ρ) (subst (liftSubst σ) t))
          (wk (.lift ρ) (subst (liftSubst σ) G)) :=
        escapeTerm pG₁' pt₁'
      have hρσa := consSubstS hΔ₁ hρσ hF ha'
      have pGa' := (hG hΔ₁ hρσa).red
      have pGa := piA.redG hρ hΔ₁ ha
      have pta : RedTerm pGa (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) a) :=
        irrelevanceTerm'' (singleSubstWkComp a σ G).symm (singleSubstWkComp a σ t).symm
          pGa' pGa (ht hΔ₁ hρσa).term
      exact (redSubstTerm (.beta wfF₁ wft₁ wfa) pGa pta).1
  exact irrelevanceTerm pPi₀ pPi ⟨_, hAt, hPiTerm⟩

/-- Valid lambda term construction (`lamᵛ`). -/
theorem lamValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (ht : ValidTerm hG t) :
    ValidTerm (piValid hF hG) (.lam t) := by
  intro Δ σ hΔ hσ
  have hPiFG : ValidType eqrel l Γ (.pi F G) := piValid hF hG
  have pPi := (hPiFG hΔ hσ).red
  refine ⟨lamRedTerm hF hG ht hΔ hσ, fun {σ'} hσ' hσσ' ↦ ?_⟩
  have pPi' := (hPiFG hΔ hσ').red
  have pPiEq := (hPiFG hΔ hσ).eq hσ' hσσ'
  have wfF : TypeWf Δ (subst σ F) := escape (hF hΔ hσ).red
  have wfF' : TypeWf Δ (subst σ' F) := escape (hF hΔ hσ').red
  have wfΔF : CtxWf (subst σ F :: Δ) := .cons hΔ wfF
  have wfΔF' : CtxWf (subst σ' F :: Δ) := .cons hΔ wfF'
  have hLiftσ := liftSubstS hΔ hF hσ
  have hLiftσ' := liftSubstS hΔ hF hσ'
  have pG₁ := (hG wfΔF hLiftσ).red
  have pG₁' := (hG wfΔF' hLiftσ').red
  have wft : HasType (subst σ F :: Δ) (subst (liftSubst σ) t) (subst (liftSubst σ) G) :=
    escapeTerm pG₁ (ht wfΔF hLiftσ).term
  have wft' : HasType (subst σ' F :: Δ) (subst (liftSubst σ') t) (subst (liftSubst σ') G) :=
    escapeTerm pG₁' (ht wfΔF' hLiftσ').term
  rcases elimPiAt' (.refl (escape pPi)) pPi with ⟨l₀, piA⟩
  rcases elimPiAt' (.refl (escape pPi')) pPi' with ⟨l₀', piA'⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ₁ rel ↦ LogRelAt eqrel l₀ Δ₁ (wk ρ (subst σ F)) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ₁ a rel ↦ LogRelAt eqrel l₀ Δ₁ (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) a) rel
  have hAt : LogRelAt eqrel l₀ Δ (.pi (subst σ F) (subst (liftSubst σ) G))
      (RedPiRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀) :=
    .pi piA.D piA.hF piA.hG piA.AeqA relF₀ relG₀
      piA.redF (fun _ _ _ h ↦ h) piA.redG (fun _ _ _ _ h ↦ h) piA.Gext
  have pPi₀ : RedType eqrel l₀ Δ (.pi (subst σ F) (subst (liftSubst σ) G)) := ⟨_, hAt⟩
  have hAppEq : ∀ {ρ Δ₁ a} (hρ : WkCtx ρ Δ₁ Δ) (hΔ₁ : CtxWf Δ₁)
      (ha : RedTerm (piA.redF hρ hΔ₁) a),
      RedTermEq (piA.redG hρ hΔ₁ ha)
        (.app (wk ρ (subst σ (.lam t))) a)
        (.app (wk ρ (subst σ' (.lam t))) a) := by
    intro ρ Δ₁ a hρ hΔ₁ ha
    have hρσ := wkSubstS hρ hΔ₁ hσ
    have hρσ' := wkSubstS hρ hΔ₁ hσ'
    have hρσσ' := wkSubstSEq hρ hΔ₁ hσσ'
    have pF_ρ := piA.redF hρ hΔ₁
    have pF'_ρ := piA'.redF hρ hΔ₁
    have pF_ρσ := (hF hΔ₁ hρσ).red
    have pF_ρσ' := (hF hΔ₁ hρσ').red
    have wfF₁' : TypeWf Δ₁ (subst (wkSubst ρ σ) F) := escape pF_ρσ
    have wfF₁ : TypeWf Δ₁ (wk ρ (subst σ F)) := escape pF_ρ
    have wfF₂' : TypeWf Δ₁ (subst (wkSubst ρ σ') F) := escape pF_ρσ'
    have wfF₂ : TypeWf Δ₁ (wk ρ (subst σ' F)) := escape pF'_ρ
    have hFF'_ρσ := (hF hΔ₁ hρσ).eq hρσ' hρσσ'
    have ha' : RedTerm pF_ρσ a := irrelevanceTerm' (wk_subst F) pF_ρ pF_ρσ ha
    have ha'' : RedTerm pF_ρσ' a := convTerm₁ pF_ρσ pF_ρσ' hFF'_ρσ ha'
    have ha''' : RedTerm pF'_ρ a := irrelevanceTerm' (wk_subst F).symm pF_ρσ' pF'_ρ ha''
    have wfa : HasType Δ₁ a (wk ρ (subst σ F)) := escapeTerm pF_ρ ha
    have wfa' : HasType Δ₁ a (wk ρ (subst σ' F)) := escapeTerm pF'_ρ ha'''
    have hρσa := consSubstS hΔ₁ hρσ hF ha'
    have hρσ'a := consSubstS hΔ₁ hρσ' hF ha''
    have hρσa_eq := consSubstSEq hΔ₁ hρσ hρσσ' hF ha'
    have pGa' := (hG hΔ₁ hρσa).red
    have pGa₁' := (hG hΔ₁ hρσ'a).red
    have pGa := piA.redG hρ hΔ₁ ha
    have pGa'' := piA'.redG hρ hΔ₁ ha'''
    have hGa_eq : RedEq pGa (subst0 (wk (.lift ρ) (subst (liftSubst σ') G)) a) :=
      irrelevanceEq'' (singleSubstWkComp a σ G).symm (singleSubstWkComp a σ' G).symm
        pGa' pGa ((hG hΔ₁ hρσa).eq hρσ'a hρσa_eq)
    have hLiftρσ := liftSubstS hΔ₁ hF hρσ
    have hLiftρσ' := liftSubstS hΔ₁ hF hρσ'
    have pG₁_ρ := (hG (.cons hΔ₁ wfF₁') hLiftρσ).red
    have hCtxEq₁ : (subst (wkSubst ρ σ) F :: Δ₁) = (wk ρ (subst σ F) :: Δ₁) :=
      congrArg (fun x ↦ x :: Δ₁) (wk_subst F).symm
    have pG₁'_ρ : RedType eqrel l (wk ρ (subst σ F) :: Δ₁) (wk (.lift ρ) (subst (liftSubst σ) G)) :=
      irrelevanceΓ' hCtxEq₁ (wk_subst_lift G).symm pG₁_ρ
    have pG₂_ρ := (hG (.cons hΔ₁ wfF₂') hLiftρσ').red
    have hCtxEq₂ : (subst (wkSubst ρ σ') F :: Δ₁) = (wk ρ (subst σ' F) :: Δ₁) :=
      congrArg (fun x ↦ x :: Δ₁) (wk_subst F).symm
    have pG₂'_ρ : RedType eqrel l (wk ρ (subst σ' F) :: Δ₁) (wk (.lift ρ) (subst (liftSubst σ') G)) :=
      irrelevanceΓ' hCtxEq₂ (wk_subst_lift G).symm pG₂_ρ
    have pt₁' : RedTerm pG₁'_ρ (wk (.lift ρ) (subst (liftSubst σ) t)) :=
      irrelevanceTermΓ'' hCtxEq₁ (wk_subst_lift G).symm (wk_subst_lift t).symm
        pG₁_ρ pG₁'_ρ (ht (.cons hΔ₁ wfF₁') hLiftρσ).term
    have pt₂' : RedTerm pG₂'_ρ (wk (.lift ρ) (subst (liftSubst σ') t)) :=
      irrelevanceTermΓ'' hCtxEq₂ (wk_subst_lift G).symm (wk_subst_lift t).symm
        pG₂_ρ pG₂'_ρ (ht (.cons hΔ₁ wfF₂') hLiftρσ').term
    have wft₁ : HasType (wk ρ (subst σ F) :: Δ₁)
        (wk (.lift ρ) (subst (liftSubst σ) t))
        (wk (.lift ρ) (subst (liftSubst σ) G)) :=
      escapeTerm pG₁'_ρ pt₁'
    have wft₂ : HasType (wk ρ (subst σ' F) :: Δ₁)
        (wk (.lift ρ) (subst (liftSubst σ') t))
        (wk (.lift ρ) (subst (liftSubst σ') G)) :=
      escapeTerm pG₂'_ρ pt₂'
    have pta : RedTerm pGa (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) a) :=
      irrelevanceTerm'' (singleSubstWkComp a σ G).symm (singleSubstWkComp a σ t).symm
        pGa' pGa (ht hΔ₁ hρσa).term
    have pta' : RedTerm pGa'' (subst0 (wk (.lift ρ) (subst (liftSubst σ') t)) a) :=
      irrelevanceTerm'' (singleSubstWkComp a σ' G).symm (singleSubstWkComp a σ' t).symm
        pGa₁' pGa'' (ht hΔ₁ hρσ'a).term
    have hlam_ta : RedTermEq pGa (.app (wk ρ (subst σ (.lam t))) a)
        (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) a) :=
      (redSubstTerm (.beta wfF₁ wft₁ wfa) pGa pta).2
    have hta'_lam' : RedTermEq pGa
        (subst0 (wk (.lift ρ) (subst (liftSubst σ') t)) a)
        (.app (wk ρ (subst σ' (.lam t))) a) :=
      convEqTerm₂ pGa pGa'' hGa_eq
        (symEqTerm pGa'' (redSubstTerm (.beta wfF₂ wft₂ wfa') pGa'' pta').2)
    have hta_ta' : RedTermEq pGa
        (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) a)
        (subst0 (wk (.lift ρ) (subst (liftSubst σ') t)) a) :=
      irrelevanceEqTerm'' (singleSubstWkComp a σ t).symm (singleSubstWkComp a σ' t).symm
        (singleSubstWkComp a σ G).symm pGa' pGa ((ht hΔ₁ hρσa).eq hρσ'a hρσa_eq)
    exact transEqTerm pGa hlam_ta (transEqTerm pGa hta_ta' hta'_lam')
  have var0_wf : HasType (subst σ F :: Δ) (.var 0) (wk (.step .id) (subst σ F)) :=
    .var wfΔF .here
  have neuVar0 : RedTerm (piA.redF (.step .id) wfΔF) (.var 0) :=
    neuTerm (piA.redF (.step .id) wfΔF) (.var 0) var0_wf (eqrel.varRefl var0_wf)
  have hEtaEq_σ_σ' : eqrel.TermEqRel Δ (.lam (subst (liftSubst σ) t)) (.lam (subst (liftSubst σ') t))
      (.pi (subst σ F) (subst (liftSubst σ) G)) :=
    eqrel.etaEq wfF (.lam wfF wft)
      (.conv (.lam wfF' wft') (.symm (eqrel.typeToEq (escapeEq pPi pPiEq))))
      .lam .lam
      (escapeTermEq pG₁
        (irrelevanceEqTerm' (idWkLiftSubstLemma σ G)
          (piA.redG (.step .id) wfΔF neuVar0) pG₁
          (hAppEq (.step .id) wfΔF neuVar0)))
  have ht_σ_0 : RedPiTerm eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀
      (subst σ (.lam t)) :=
    (RedTerm_of_LogRelAt hAt pPi₀).mp
      (irrelevanceTerm pPi pPi₀ (lamRedTerm hF hG ht hΔ hσ))
  have ht_σ'_0 : RedPiTerm eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀
      (subst σ' (.lam t)) :=
    (RedTerm_of_LogRelAt hAt pPi₀).mp
      (irrelevanceTerm pPi pPi₀
        (convTerm₂ pPi pPi' pPiEq (lamRedTerm hF hG ht hΔ hσ')))
  have hPiEqTerm : RedPiTermEq eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀
      (subst σ (.lam t)) (subst σ' (.lam t)) :=
    .mk (.lam (subst (liftSubst σ) t)) (.lam (subst (liftSubst σ') t))
      (idRedTermWf (.lam wfF wft))
      (idRedTermWf (.conv (.lam wfF' wft') (.symm (eqrel.typeToEq (escapeEq pPi pPiEq)))))
      .lam .lam hEtaEq_σ_σ' ht_σ_0 ht_σ'_0 hAppEq
  exact irrelevanceEqTerm pPi₀ pPi ⟨_, hAt, hPiEqTerm⟩

/-- Reducibility of η-equality under a valid substitution (`η-eqEqTerm`). -/
theorem etaEqTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ Δ : Context} {f g F G : Term} {σ : Subst}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (hf0g0 : ValidTermEq hG (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)))
    (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ)
    (hf : RedTerm ((piValid hF hG) hΔ hσ).red (subst σ f))
    (hg : RedTerm ((piValid hF hG) hΔ hσ).red (subst σ g)) :
    RedTermEq ((piValid hF hG) hΔ hσ).red (subst σ f) (subst σ g) := by
  have hPiFG : ValidType eqrel l Γ (.pi F G) := piValid hF hG
  have pPi := (hPiFG hΔ hσ).red
  rcases elimPiAt' (.refl (escape pPi)) pPi with ⟨l₀, piA⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ₁ rel ↦ LogRelAt eqrel l₀ Δ₁ (wk ρ (subst σ F)) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ₁ a rel ↦ LogRelAt eqrel l₀ Δ₁ (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) a) rel
  have hAt : LogRelAt eqrel l₀ Δ (.pi (subst σ F) (subst (liftSubst σ) G))
      (RedPiRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀) :=
    .pi piA.D piA.hF piA.hG piA.AeqA relF₀ relG₀
      piA.redF (fun _ _ _ h ↦ h) piA.redG (fun _ _ _ _ h ↦ h) piA.Gext
  have pPi₀ : RedType eqrel l₀ Δ (.pi (subst σ F) (subst (liftSubst σ) G)) := ⟨_, hAt⟩
  have hfPi : RedPiTerm eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀ (subst σ f) :=
    (RedTerm_of_LogRelAt hAt pPi₀).mp (irrelevanceTerm pPi pPi₀ hf)
  have hgPi : RedPiTerm eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀ (subst σ g) :=
    (RedTerm_of_LogRelAt hAt pPi₀).mp (irrelevanceTerm pPi pPi₀ hg)
  rcases hfPi with ⟨f₁, df, funcF, feqf, appEq_f, appTerm_f⟩
  rcases hgPi with ⟨g₁, dg, funcG, geqg, appEq_g, appTerm_g⟩
  have wfF : TypeWf Δ (subst σ F) := piA.hF
  have wfΔF : CtxWf (subst σ F :: Δ) := .cons hΔ wfF
  have pσF := (hF hΔ hσ).red
  have pwk1F : RedType eqrel l (subst σ F :: Δ) (wk (.step .id) (subst σ F)) :=
    wkRed (.step .id) wfΔF pσF
  have var0' : HasType (subst σ F :: Δ) (.var 0) (wk (.step .id) (subst σ F)) :=
    .var wfΔF .here
  have var0 : RedTerm pwk1F (.var 0) :=
    neuTerm pwk1F (.var 0) var0' (eqrel.varRefl var0')
  have var0_eq : RedTermEq pwk1F (.var 0) (.var 0) :=
    neuEqTerm pwk1F (.var 0) (.var 0) var0' var0' (eqrel.varRefl var0')
  have var0_0 : RedTerm (piA.redF (.step .id) wfΔF) (.var 0) :=
    irrelevanceTerm pwk1F (piA.redF (.step .id) wfΔF) var0
  have pσG' := piA.redG (.step .id) wfΔF var0_0
  have hLiftσ := liftSubstS hΔ hF hσ
  have pσG := (hG wfΔF hLiftσ).red
  have σf0_eq_σg0_raw : eqrel.TermEqRel (subst σ F :: Δ)
      (subst (liftSubst σ) (.app (wk1 f) (.var 0)))
      (subst (liftSubst σ) (.app (wk1 g) (.var 0)))
      (subst (liftSubst σ) G) :=
    escapeTermEq pσG (hf0g0 wfΔF hLiftσ)
  have hf_wk_eq : subst (liftSubst σ) (.app (wk1 f) (.var 0)) =
      .app (wk1 (subst σ f)) (.var 0) := by
    change Term.app (subst (liftSubst σ) (wk (.step .id) f)) (.var 0) =
      Term.app (wk (.step .id) (subst σ f)) (.var 0)
    exact congrArg (fun x ↦ Term.app x (.var 0))
      ((subst_wk (ρ := .step .id) f).trans (wk_subst (ρ := .step .id) f).symm)
  have hg_wk_eq : subst (liftSubst σ) (.app (wk1 g) (.var 0)) =
      .app (wk1 (subst σ g)) (.var 0) := by
    change Term.app (subst (liftSubst σ) (wk (.step .id) g)) (.var 0) =
      Term.app (wk (.step .id) (subst σ g)) (.var 0)
    exact congrArg (fun x ↦ Term.app x (.var 0))
      ((subst_wk (ρ := .step .id) g).trans (wk_subst (ρ := .step .id) g).symm)
  have σf0_eq_σg0' : eqrel.TermEqRel (subst σ F :: Δ)
      (.app (wk1 (subst σ f)) (.var 0))
      (.app (wk1 (subst σ g)) (.var 0))
      (subst (liftSubst σ) G) := by
    rwa [hf_wk_eq, hg_wk_eq] at σf0_eq_σg0_raw
  have hf₁_term : RedTerm pPi f₁ :=
    irrelevanceTerm pPi₀ pPi ⟨_, hAt, .mk f₁ (idRedTermWf df.target) funcF feqf appEq_f appTerm_f⟩
  have hg₁_term : RedTerm pPi g₁ :=
    irrelevanceTerm pPi₀ pPi ⟨_, hAt, .mk g₁ (idRedTermWf dg.target) funcG geqg appEq_g appTerm_g⟩
  have f_eq_f₁ : RedTermEq pPi (subst σ f) f₁ :=
    (redSubstStarTerm df.reduction pPi hf₁_term).2
  have g_eq_g₁ : RedTermEq pPi (subst σ g) g₁ :=
    (redSubstStarTerm dg.reduction pPi hg₁_term).2
  have pwk1Pi : RedType eqrel l (subst σ F :: Δ) (wk (.step .id) (.pi (subst σ F) (subst (liftSubst σ) G))) :=
    wkRed (.step .id) wfΔF pPi
  have pσG'_l : RedType eqrel l (subst σ F :: Δ)
      (subst0 (wk (.lift (.step .id)) (subst (liftSubst σ) G)) (.var 0)) :=
    irrelevance' (cons0wkLift1_id σ G).symm pσG
  have eq'_red : RedTermEq pσG
      (.app (wk (.step .id) (subst σ f)) (.var 0))
      (.app (wk (.step .id) f₁) (.var 0)) :=
    irrelevanceEqTerm' (cons0wkLift1_id σ G) pσG'_l pσG
      (appCongTerm pwk1F pσG'_l pwk1Pi
        (wkRedTermEq (.step .id) wfΔF pPi f_eq_f₁) var0 var0 var0_eq)
  have eq₁'_red : RedTermEq pσG
      (.app (wk (.step .id) (subst σ g)) (.var 0))
      (.app (wk (.step .id) g₁) (.var 0)) :=
    irrelevanceEqTerm' (cons0wkLift1_id σ G) pσG'_l pσG
      (appCongTerm pwk1F pσG'_l pwk1Pi
        (wkRedTermEq (.step .id) wfΔF pPi g_eq_g₁) var0 var0 var0_eq)
  have eq_syn := escapeTermEq pσG eq'_red
  have eq₁_syn := escapeTermEq pσG eq₁'_red
  have hEta_f₁_g₁ : eqrel.TermEqRel Δ f₁ g₁ (.pi (subst σ F) (subst (liftSubst σ) G)) :=
    eqrel.etaEq wfF df.target dg.target funcF.toWhnf funcG.toWhnf
      (eqrel.transTerm (eqrel.symmTerm eq_syn) (eqrel.transTerm σf0_eq_σg0' eq₁_syn))
  have hPiEqTerm : RedPiTermEq eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀
      (subst σ f) (subst σ g) := by
    refine .mk f₁ g₁ df dg funcF funcG hEta_f₁_g₁
      (.mk f₁ df funcF feqf appEq_f appTerm_f)
      (.mk g₁ dg funcG geqg appEq_g appTerm_g)
      (fun {ρ Δ₁ a} hρ hΔ₁ ha ↦ ?_)
    have hρσ := wkSubstS hρ hΔ₁ hσ
    have pF'' := (hF hΔ₁ hρσ).red
    have ha' : RedTerm pF'' a :=
      irrelevanceTerm' (wk_subst F) (piA.redF hρ hΔ₁) pF'' ha
    have hρσa := consSubstS hΔ₁ hρσ hF ha'
    have fEq : subst (consSubst (wkSubst ρ σ) a) (.app (wk1 f) (.var 0)) =
        .app (wk ρ (subst σ f)) a := by
      change Term.app (subst (consSubst (wkSubst ρ σ) a) (wk (.step .id) f)) a =
        Term.app (wk ρ (subst σ f)) a
      exact congrArg (fun x ↦ Term.app x a)
        ((subst_wk (ρ := .step .id) f).trans (wk_subst (ρ := ρ) f).symm)
    have gEq : subst (consSubst (wkSubst ρ σ) a) (.app (wk1 g) (.var 0)) =
        .app (wk ρ (subst σ g)) a := by
      change Term.app (subst (consSubst (wkSubst ρ σ) a) (wk (.step .id) g)) a =
        Term.app (wk ρ (subst σ g)) a
      exact congrArg (fun x ↦ Term.app x a)
        ((subst_wk (ρ := .step .id) g).trans (wk_subst (ρ := ρ) g).symm)
    have GEq : subst (consSubst (wkSubst ρ σ) a) G =
        subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) a :=
      (singleSubstWkComp a σ G).symm
    have pGa := piA.redG hρ hΔ₁ ha
    have hf_eq_g : RedTermEq pGa (.app (wk ρ (subst σ f)) a) (.app (wk ρ (subst σ g)) a) :=
      irrelevanceEqTerm'' fEq gEq GEq (hG hΔ₁ hρσa).red pGa (hf0g0 hΔ₁ hρσa)
    have pρPi := wkRed hρ hΔ₁ pPi
    have hf₁_ρ : RedTerm pρPi (wk ρ f₁) := wkRedTerm hρ hΔ₁ pPi hf₁_term
    have hg₁_ρ : RedTerm pρPi (wk ρ g₁) := wkRedTerm hρ hΔ₁ pPi hg₁_term
    have hf₁a : RedTerm pGa (.app (wk ρ f₁) a) :=
      appTerm (piA.redF hρ hΔ₁) pGa pρPi hf₁_ρ ha
    have hg₁a : RedTerm pGa (.app (wk ρ g₁) a) :=
      appTerm (piA.redF hρ hΔ₁) pGa pρPi hg₁_ρ ha
    have wfa : HasType Δ₁ a (wk ρ (subst σ F)) := escapeTerm (piA.redF hρ hΔ₁) ha
    have hfa_f₁a : RedTermEq pGa (.app (wk ρ (subst σ f)) a) (.app (wk ρ f₁) a) :=
      (redSubstStarTerm ((wkStar hρ hΔ₁ df.reduction).app wfa) pGa hf₁a).2
    have hga_g₁a : RedTermEq pGa (.app (wk ρ (subst σ g)) a) (.app (wk ρ g₁) a) :=
      (redSubstStarTerm ((wkStar hρ hΔ₁ dg.reduction).app wfa) pGa hg₁a).2
    exact transEqTerm pGa (symEqTerm pGa hfa_f₁a)
      (transEqTerm pGa hf_eq_g hga_g₁a)
  exact irrelevanceEqTerm pPi₀ pPi ⟨_, hAt, hPiEqTerm⟩

/-- Validity of η-equality (`η-eqᵛ`). -/
theorem etaEqValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {f g F G : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (hf : ValidTerm (piValid hF hG) f)
    (hg : ValidTerm (piValid hF hG) g)
    (hf0g0 : ValidTermEq hG (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0))) :
    ValidTermEq (piValid hF hG) f g :=
  fun hΔ hσ ↦ etaEqTerm hF hG hf0g0 hΔ hσ (hf hΔ hσ).term (hg hΔ hσ).term

/-!
## Natural Recursion Introductions (`Definition/LogicalRelation/Substitution/Introductions/Natrec.agda`)
-/

/-- Natural recursion closure reduction (`natrec-subst*`). -/
theorem natrecSubstStar {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context}
    {C c g n n' : Term}
    (hC : TypeWf (.nat :: Γ) C)
    (hc : HasType Γ c (subst0 C .zero))
    (hg : HasType Γ g (recStepType C))
    (dnn' : Star Γ n n' .nat)
    (pNat : RedType eqrel l Γ .nat)
    (hn' : RedTerm pNat n')
    (prop : ∀ {t t'}, RedTerm pNat t → RedTerm pNat t' → RedTermEq pNat t t' →
      TypeEq Γ (subst0 C t) (subst0 C t')) :
    Star Γ (.natrec C c g n) (.natrec C c g n') (subst0 C n) := by
  generalize hNatEq : Term.nat = N₀ at dnn'
  induction dnn' with
  | refl hn =>
      subst hNatEq
      exact .refl (.natrec hC hc hg hn)
  | @step _ n n₁ n' hStep hRest ih =>
      subst hNatEq
      rcases redSubstStarTerm hRest pNat hn' with ⟨hn₁, _⟩
      rcases redSubstTerm hStep pNat hn₁ with ⟨hn, hnn₁⟩
      have hRestNatrec : Star Γ (.natrec C c g n₁) (.natrec C c g n') (subst0 C n₁) :=
        ih hn' rfl
      exact .step (.natrec hC hc hg hStep)
        (hRestNatrec.conv (prop hn₁ hn (symEqTerm pNat hnn₁)))

theorem consSubstSEqNat {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context}
    {σ σ' : Subst} {t t' : Term} {Γ : Context}
    (hTailEq : ValidSubstEq eqrel Δ σ σ' Γ)
    (pNat : RedType eqrel l Δ .nat)
    (hHeadEq : RedTermEq pNat t t') :
    ValidSubstEq eqrel Δ (consSubst σ t) (consSubst σ' t') (.nat :: Γ) :=
  ⟨hTailEq, l, pNat, hHeadEq⟩

theorem sucCase₃ {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context}
    (hNat : ValidType eqrel l Γ .nat) :
    ValidTerm (wk1Valid (F := .nat) hNat) (.succ (.var 0)) := by
  have hVar0 : ValidTerm (wk1Valid (F := .nat) hNat) (.var 0) := by
    intro Δ σ hΔ hσ
    have pwk1Nat := ((wk1Valid (F := .nat) hNat) hΔ hσ).red
    have pTailNat := (hNat hΔ hσ.tail).red
    refine ⟨irrelevanceTerm pTailNat pwk1Nat (hσ.head hNat hΔ),
      fun {σ'} hσ' hσσ' ↦ irrelevanceEqTerm pTailNat pwk1Nat (hσσ'.head hNat hΔ hσ)⟩
  intro Δ σ hΔ hσ
  exact sucValid (wk1Valid (F := .nat) hNat) hVar0 hΔ hσ

theorem sucCase₂ {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F : Term}
    (hNat : ValidType eqrel l Γ .nat)
    (hF : ValidType eqrel l (.nat :: Γ) F) :
    ValidType eqrel l (.nat :: Γ) (substKeep F (.succ (.var 0))) :=
  substUpS hNat hF (sucCase₃ hNat)

theorem sucCase₁ {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F : Term}
    (hNat : ValidType eqrel l Γ .nat)
    (hF : ValidType eqrel l (.nat :: Γ) F) :
    ValidType eqrel l (.nat :: Γ) (arr F (substKeep F (.succ (.var 0)))) :=
  arrValid hF (sucCase₂ hNat hF)

/-- Construct a valid type for the successor case of `natrec` (`sucCase`). -/
theorem sucCase {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F : Term}
    (hNat : ValidType eqrel l Γ .nat)
    (hF : ValidType eqrel l (.nat :: Γ) F) :
    ValidType eqrel l Γ (recStepType F) :=
  piValid hNat (sucCase₁ hNat hF)

/-- Construct a valid type equality for the successor case of `natrec` (`sucCaseCong`). -/
theorem sucCaseCong {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F F' : Term}
    (hNat : ValidType eqrel l Γ .nat)
    (hF : ValidType eqrel l (.nat :: Γ) F)
    (hF' : ValidType eqrel l (.nat :: Γ) F')
    (hFF' : ValidTypeEq hF F') :
    ValidTypeEq (sucCase hNat hF) (recStepType F') :=
  piCongValid hNat (sucCase₁ hNat hF) hNat (sucCase₁ hNat hF')
    (reflValid hNat)
    (arrCongValid hF hF' hFF' (sucCase₂ hNat hF) (sucCase₂ hNat hF')
      (substUpSEq hNat hF hF' hFF' (sucCase₃ hNat) (sucCase₃ hNat)
        (reflValidTerm (wk1Valid (F := .nat) hNat) (sucCase₃ hNat))))

theorem redTerm_of_RedNatTerm {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} {n : Term}
    (hΔ : CtxWf Δ) (hn : RedNatTerm eqrel Δ n) :
    RedTerm (redNat (eqrel := eqrel) (l := l) hΔ) n :=
  ⟨RedNatRel eqrel Δ, .nat (idRedWf (.nat hΔ)), hn⟩

theorem redNatTerm_of_RedTerm {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} {n : Term}
    (hΔ : CtxWf Δ) (hn : RedTerm (redNat (eqrel := eqrel) (l := l) hΔ) n) :
    RedNatTerm eqrel Δ n :=
  (RedTerm_of_LogRelAt (.nat (idRedWf (.nat hΔ))) (redNat hΔ)).mp hn

theorem redNatTermEq_of_RedTermEq {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} {n m : Term}
    (hΔ : CtxWf Δ) (hnm : RedTermEq (redNat (eqrel := eqrel) (l := l) hΔ) n m) :
    RedNatTermEq eqrel Δ n m :=
  (RedTermEq_of_LogRelAt (.nat (idRedWf (.nat hΔ))) (redNat hΔ)).mp hnm

theorem invRedNatTerm_suc {eqrel : EqRelSet} {Δ : Context} {n n' : Term}
    (hn : RedNatTerm eqrel Δ n) (d : Star Δ n (.succ n') .nat) :
    eqrel.TermEqRel Δ (.succ n') (.succ n') .nat ∧ RedNatTerm eqrel Δ n' := by
  cases hn with
  | mk _ k d₀ keqk prop₀ =>
      have hk : k = .succ n' :=
        whrDetStarTerm ⟨d₀.reduction, (natural_of_NaturalProp prop₀).toWhnf⟩ ⟨d, .succ⟩
      subst hk
      cases prop₀ with
      | suc hn' => exact ⟨keqk, hn'⟩
      | ne nf => cases nf.neK

theorem invRedNatTerm_zero {eqrel : EqRelSet} {Δ : Context} {n : Term}
    (hn : RedNatTerm eqrel Δ n) (d : Star Δ n .zero .nat) :
    eqrel.TermEqRel Δ .zero .zero .nat := by
  cases hn with
  | mk _ k d₀ keqk prop₀ =>
      have hk : k = .zero :=
        whrDetStarTerm ⟨d₀.reduction, (natural_of_NaturalProp prop₀).toWhnf⟩ ⟨d, .zero⟩
      subst hk
      exact keqk

theorem invRedNatTerm_ne {eqrel : EqRelSet} {Δ : Context} {n n' : Term}
    (hn : RedNatTerm eqrel Δ n) (d : Star Δ n n' .nat) (neN' : Neutral n') :
    eqrel.TermEqRel Δ n' n' .nat ∧ RedNeNf eqrel Δ n' .nat := by
  cases hn with
  | mk _ k d₀ keqk prop₀ =>
      have hk : k = n' :=
        whrDetStarTerm ⟨d₀.reduction, (natural_of_NaturalProp prop₀).toWhnf⟩
          ⟨d, .neutral neN'⟩
      subst hk
      cases prop₀ with
      | suc _ => cases neN'
      | zero => cases neN'
      | ne nf => exact ⟨keqk, nf⟩

/-- Reducibility of natural recursion under a valid substitution (`natrecTerm`). -/
theorem natrecTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ Δ : Context}
    {F z s n : Term} {σ : Subst}
    (hF : ValidType eqrel l (.nat :: Γ) F)
    (hF0 : ValidType eqrel l Γ (subst0 F .zero))
    (hFStep : ValidType eqrel l Γ (recStepType F))
    (hz : ValidTerm hF0 z)
    (hs : ValidTerm hFStep s)
    (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ)
    (hn : RedTerm (redNat (eqrel := eqrel) (l := l) hΔ) n) :
    RedTerm (irrelevance' (singleSubstComp n σ F).symm
      (hF hΔ (consSubstS hΔ hσ (natValid (l := l)) hn)).red)
      (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) n) := by
  have hNat : ValidType eqrel l Γ .nat := natValid (l := l)
  have pσNat : RedType eqrel l Δ .nat := (hNat hΔ hσ).red
  have wfNat : TypeWf Δ .nat := escape pσNat
  have hLiftσ := liftSubstS hΔ hNat hσ
  have pσF := (hF (.cons hΔ wfNat) hLiftσ).red
  have wfF : TypeWf (.nat :: Δ) (subst (liftSubst σ) F) := escape pσF
  have wfz : HasType Δ (subst σ z) (subst0 (subst (liftSubst σ) F) .zero) := by
    have h := escapeTerm (hF0 hΔ hσ).red (hz hΔ hσ).term
    rwa [singleSubstLift F .zero] at h
  have wfs : HasType Δ (subst σ s) (recStepType (subst (liftSubst σ) F)) := by
    have h := escapeTerm (hFStep hΔ hσ).red (hs hΔ hσ).term
    rwa [natrecSucCase σ F] at h
  have hPropF : ∀ {t t'}, RedTerm pσNat t → RedTerm pσNat t' → RedTermEq pσNat t t' →
      TypeEq Δ (subst0 (subst (liftSubst σ) F) t) (subst0 (subst (liftSubst σ) F) t') := by
    intro t t' ht ht' htt'
    have hσt := consSubstS hΔ hσ hNat ht
    have hσt' := consSubstS hΔ hσ hNat ht'
    have hσσt := consSubstSEqNat (reflSubst hσ) pσNat htt'
    have hEq := eqrel.typeToEq (escapeEq (hF hΔ hσt).red ((hF hΔ hσt).eq hσt' hσσt))
    rwa [← singleSubstComp t σ F, ← singleSubstComp t' σ F] at hEq
  have hn_nat : RedNatTerm eqrel Δ n := redNatTerm_of_RedTerm hΔ hn
  exact @RedNatTerm.rec eqrel Δ
    (fun n hn_nat ↦
      RedTerm (irrelevance' (singleSubstComp n σ F).symm
        (hF hΔ (consSubstS hΔ hσ hNat (redTerm_of_RedNatTerm hΔ hn_nat))).red)
        (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) n))
    (fun k _ ↦
      ∀ {m}, k = .succ m → ∀ (hm : RedNatTerm eqrel Δ m),
        RedTerm (irrelevance' (singleSubstComp m σ F).symm
          (hF hΔ (consSubstS hΔ hσ hNat (redTerm_of_RedNatTerm hΔ hm))).red)
          (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m))
    (fun n k d n_eq_n prop ih_prop ↦ by
      have hn_red : RedTerm pσNat n :=
        redTerm_of_RedNatTerm hΔ (.mk n k d n_eq_n prop)
      have pσFn' := (hF hΔ (consSubstS hΔ hσ hNat hn_red)).red
      have pσFn := irrelevance' (singleSubstComp n σ F).symm pσFn'
      cases prop with
      | @suc m hm_nat =>
          have hm : RedTerm pσNat m := redTerm_of_RedNatTerm hΔ hm_nat
          have wfm : HasType Δ m .nat := escapeTerm pσNat hm
          have hσsm : RedTerm pσNat (.succ m) :=
            redTerm_of_RedNatTerm hΔ
              (.mk (.succ m) (.succ m) (idRedTermWf (.succ wfm)) n_eq_n (.suc hm_nat))
          rcases redSubstStarTerm d.reduction pσNat hσsm with ⟨_, hσn_eq_σsm⟩
          have pσFsm := irrelevance' (singleSubstComp (.succ m) σ F).symm
            (hF hΔ (consSubstS hΔ hσ hNat hσsm)).red
          have hFn_eq_Fsm : RedEq pσFn (subst0 (subst (liftSubst σ) F) (.succ m)) :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (singleSubstComp (.succ m) σ F).symm
              pσFn' pσFn
              ((hF hΔ (consSubstS hΔ hσ hNat hn_red)).eq
                (consSubstS hΔ hσ hNat hσsm)
                (consSubstSEqNat (reflSubst hσ) pσNat hσn_eq_σsm))
          have pσFm := irrelevance' (singleSubstComp m σ F).symm
            (hF hΔ (consSubstS hΔ hσ hNat hm)).red
          have pσFsm' := irrelevance' (natrecIrrelevantSubst F z s m σ)
            (hF hΔ (consSubstS hΔ hσ hNat hσsm)).red
          have pσFStep : RedType eqrel l Δ (subst σ (recStepType F)) :=
            (hFStep hΔ hσ).red
          have hs_term : RedTerm pσFStep (subst σ s) :=
            (hs hΔ hσ).term
          have pσFStep_m : RedType eqrel l Δ
              (.pi (subst0 (subst (liftSubst σ) F) m)
                (subst (liftSubst (sgSubst m))
                  (subst (liftSubst (liftSubst σ))
                    (wk1 (substKeep F (.succ (.var 0))))))) :=
            substSPi₁ pσFStep pσNat hm
          have ih_m := ih_prop rfl hm_nat
          have natrecM := appTerm pσFm pσFsm' pσFStep_m
            (appTerm pσNat pσFStep_m pσFStep hs_term hm) ih_m
          have natrecM' : RedTerm pσFsm
              (.app (.app (subst σ s) m) (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m)) :=
            irrelevanceTerm'
              ((natrecIrrelevantSubst F z s m σ).symm.trans (singleSubstComp (.succ m) σ F).symm)
              pσFsm' pσFsm natrecM
          have hRed1 := natrecSubstStar wfF wfz wfs d.reduction pσNat hσsm hPropF
          have hRed2 : Star Δ
              (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) (.succ m))
              (.app (.app (subst σ s) m) (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m))
              (subst0 (subst (liftSubst σ) F) n) :=
            (Star.step (.natrecSucc wfm wfF wfz wfs)
              (.refl (escapeTerm pσFsm natrecM'))).conv
              (.symm (eqrel.typeToEq (escapeEq pσFn hFn_eq_Fsm)))
          exact (redSubstStarTerm (hRed1.trans hRed2) pσFn
            (convTerm₂ pσFn pσFsm hFn_eq_Fsm natrecM')).1
      | zero =>
          have hσ0 : RedTerm pσNat .zero :=
            redTerm_of_RedNatTerm hΔ (.mk .zero .zero (idRedTermWf (.zero hΔ)) n_eq_n .zero)
          rcases redSubstStarTerm d.reduction pσNat hσ0 with ⟨_, hσn_eq_σ0⟩
          have hFn_eq_F0_raw :=
            (hF hΔ (consSubstS hΔ hσ hNat hn_red)).eq
              (consSubstS hΔ hσ hNat hσ0)
              (consSubstSEqNat (reflSubst hσ) pσNat hσn_eq_σ0)
          have hFn_eq_F0 : RedEq pσFn (subst σ (subst0 F .zero)) :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (substConsId F)
              pσFn' pσFn hFn_eq_F0_raw
          have hFn_eq_F0'' : RedEq pσFn (subst0 (subst (liftSubst σ) F) .zero) :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (singleSubstComp .zero σ F).symm
              pσFn' pσFn hFn_eq_F0_raw
          have hRed1 := natrecSubstStar wfF wfz wfs d.reduction pσNat hσ0 hPropF
          have hRed2 : Star Δ
              (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) .zero)
              (subst σ z)
              (subst0 (subst (liftSubst σ) F) n) :=
            (Star.step (.natrecZero wfF wfz wfs) (.refl wfz)).conv
              (.symm (eqrel.typeToEq (escapeEq pσFn hFn_eq_F0'')))
          exact (redSubstStarTerm (hRed1.trans hRed2) pσFn
            (convTerm₂ pσFn (hF0 hΔ hσ).red hFn_eq_F0 (hz hΔ hσ).term)).1
      | ne nf =>
          have hσm : RedTerm pσNat k :=
            neuTerm pσNat nf.neK nf.hk nf.keqk
          rcases redSubstStarTerm d.reduction pσNat hσm with ⟨_, hσn_eq_σm⟩
          have pσFm := irrelevance' (singleSubstComp k σ F).symm
            (hF hΔ (consSubstS hΔ hσ hNat hσm)).red
          have hFn_eq_Fm : RedEq pσFn (subst0 (subst (liftSubst σ) F) k) :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (singleSubstComp k σ F).symm
              pσFn' pσFn
              ((hF hΔ (consSubstS hΔ hσ hNat hn_red)).eq
                (consSubstS hΔ hσ hNat hσm)
                (consSubstSEqNat (reflSubst hσ) pσNat hσn_eq_σm))
          have wfFF : eqrel.TypeEqRel (.nat :: Δ) (subst (liftSubst σ) F) (subst (liftSubst σ) F) :=
            escapeEq pσF (reflEq pσF)
          have wfzz : eqrel.TermEqRel Δ (subst σ z) (subst σ z) (subst0 (subst (liftSubst σ) F) .zero) := by
            have h := escapeTermEq (hF0 hΔ hσ).red (reflEqTerm (hF0 hΔ hσ).red (hz hΔ hσ).term)
            rwa [singleSubstLift F .zero] at h
          have wfss : eqrel.TermEqRel Δ (subst σ s) (subst σ s) (recStepType (subst (liftSubst σ) F)) := by
            have h := escapeTermEq (hFStep hΔ hσ).red (reflEqTerm (hFStep hΔ hσ).red (hs hΔ hσ).term)
            rwa [natrecSucCase σ F] at h
          have natrecM : RedTerm pσFm (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) k) :=
            neuTerm pσFm (.natrec nf.neK) (.natrec wfF wfz wfs nf.hk)
              (eqrel.natrecCong wfFF wfzz wfss nf.keqk)
          have hRed := natrecSubstStar wfF wfz wfs d.reduction pσNat hσm hPropF
          exact (redSubstStarTerm hRed pσFn (convTerm₂ pσFn pσFm hFn_eq_Fm natrecM)).1)
    (fun {_} _ ih {m'} heq _ ↦ by injection heq with h; subst h; exact ih)
    (fun {m'} heq ↦ by cases heq)
    (fun {_} nf {m'} heq ↦ by subst heq; cases nf.neK)
    n hn_nat
/-- Reducibility of natural recursion congruence under a valid substitution equality
(`natrec-congTerm`). -/
theorem natrecCongTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ Δ : Context}
    {F F' z z' s s' n m : Term} {σ σ' : Subst}
    (hF : ValidType eqrel l (.nat :: Γ) F)
    (hF' : ValidType eqrel l (.nat :: Γ) F')
    (hFF' : ValidTypeEq hF F')
    (hF0 : ValidType eqrel l Γ (subst0 F .zero))
    (hF'0 : ValidType eqrel l Γ (subst0 F' .zero))
    (_hF0F'0 : ValidTypeEq hF0 (subst0 F' .zero))
    (hFStep : ValidType eqrel l Γ (recStepType F))
    (hF'Step : ValidType eqrel l Γ (recStepType F'))
    (_hFStepEq : ValidTypeEq hFStep (recStepType F'))
    (hz : ValidTerm hF0 z)
    (hz' : ValidTerm hF'0 z')
    (hzz' : ValidTermEq hF0 z z')
    (hs : ValidTerm hFStep s)
    (hs' : ValidTerm hF'Step s')
    (hss' : ValidTermEq hFStep s s')
    (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ)
    (hσ' : ValidSubst eqrel Δ σ' Γ)
    (hσσ' : ValidSubstEq eqrel Δ σ σ' Γ)
    (hn : RedTerm (redNat (eqrel := eqrel) (l := l) hΔ) n)
    (hm : RedTerm (redNat (eqrel := eqrel) (l := l) hΔ) m)
    (hnm : RedTermEq (redNat (eqrel := eqrel) (l := l) hΔ) n m) :
    RedTermEq (irrelevance' (singleSubstComp n σ F).symm
      (hF hΔ (consSubstS hΔ hσ (natValid (l := l)) hn)).red)
      (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) n)
      (.natrec (subst (liftSubst σ') F') (subst σ' z') (subst σ' s') m) := by
  have hNat : ValidType eqrel l Γ .nat := natValid (l := l)
  have pσNat : RedType eqrel l Δ .nat := (hNat hΔ hσ).red
  have pσ'Nat : RedType eqrel l Δ .nat := (hNat hΔ hσ').red
  have wfNat : TypeWf Δ .nat := escape pσNat
  have wfNat' : TypeWf Δ .nat := escape pσ'Nat
  have hLiftσ := liftSubstS hΔ hNat hσ
  have hLiftσ' := liftSubstS hΔ hNat hσ'
  have pσF := (hF (.cons hΔ wfNat) hLiftσ).red
  have pσ'F := (hF (.cons hΔ wfNat) hLiftσ').red
  have pσ'F' := (hF' (.cons hΔ wfNat') hLiftσ').red
  have wfF : TypeWf (.nat :: Δ) (subst (liftSubst σ) F) := escape pσF
  have wfF' : TypeWf (.nat :: Δ) (subst (liftSubst σ') F') := escape pσ'F'
  have wfz : HasType Δ (subst σ z) (subst0 (subst (liftSubst σ) F) .zero) := by
    have h := escapeTerm (hF0 hΔ hσ).red (hz hΔ hσ).term
    rwa [singleSubstLift F .zero] at h
  have wfs : HasType Δ (subst σ s) (recStepType (subst (liftSubst σ) F)) := by
    have h := escapeTerm (hFStep hΔ hσ).red (hs hΔ hσ).term
    rwa [natrecSucCase σ F] at h
  have wfz' : HasType Δ (subst σ' z') (subst0 (subst (liftSubst σ') F') .zero) := by
    have h := escapeTerm (hF'0 hΔ hσ').red (hz' hΔ hσ').term
    rwa [singleSubstLift F' .zero] at h
  have wfs' : HasType Δ (subst σ' s') (recStepType (subst (liftSubst σ') F')) := by
    have h := escapeTerm (hF'Step hΔ hσ').red (hs' hΔ hσ').term
    rwa [natrecSucCase σ' F'] at h
  have hPropF : ∀ {t t'}, RedTerm pσNat t → RedTerm pσNat t' → RedTermEq pσNat t t' →
      TypeEq Δ (subst0 (subst (liftSubst σ) F) t) (subst0 (subst (liftSubst σ) F) t') := by
    intro t t' ht ht' htt'
    have hEq := eqrel.typeToEq (escapeEq (hF hΔ (consSubstS hΔ hσ hNat ht)).red
      ((hF hΔ (consSubstS hΔ hσ hNat ht)).eq
        (consSubstS hΔ hσ hNat ht')
        (consSubstSEqNat (reflSubst hσ) pσNat htt')))
    rwa [← singleSubstComp t σ F, ← singleSubstComp t' σ F] at hEq
  have hPropF' : ∀ {t t'}, RedTerm pσ'Nat t → RedTerm pσ'Nat t' → RedTermEq pσ'Nat t t' →
      TypeEq Δ (subst0 (subst (liftSubst σ') F') t) (subst0 (subst (liftSubst σ') F') t') := by
    intro t t' ht ht' htt'
    have hEq := eqrel.typeToEq (escapeEq (hF' hΔ (consSubstS hΔ hσ' hNat ht)).red
      ((hF' hΔ (consSubstS hΔ hσ' hNat ht)).eq
        (consSubstS hΔ hσ' hNat ht')
        (consSubstSEqNat (reflSubst hσ') pσ'Nat htt')))
    rwa [← singleSubstComp t σ' F', ← singleSubstComp t' σ' F'] at hEq
  have hn_nat := redNatTerm_of_RedTerm hΔ hn
  have hm_nat := redNatTerm_of_RedTerm hΔ hm
  have hnm_nat := redNatTermEq_of_RedTermEq hΔ hnm
  exact @RedNatTermEq.rec eqrel Δ
    (fun n m _ ↦
      ∀ (hn_nat : RedNatTerm eqrel Δ n) (hm_nat : RedNatTerm eqrel Δ m),
        RedTermEq (irrelevance' (singleSubstComp n σ F).symm
          (hF hΔ (consSubstS hΔ hσ hNat (redTerm_of_RedNatTerm hΔ hn_nat))).red)
          (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) n)
          (.natrec (subst (liftSubst σ') F') (subst σ' z') (subst σ' s') m))
    (fun k k' _ ↦
      ∀ {n' m'}, k = .succ n' → k' = .succ m' →
        ∀ (hn'_nat : RedNatTerm eqrel Δ n') (hm'_nat : RedNatTerm eqrel Δ m'),
          RedTermEq (irrelevance' (singleSubstComp n' σ F).symm
            (hF hΔ (consSubstS hΔ hσ hNat (redTerm_of_RedNatTerm hΔ hn'_nat))).red)
            (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) n')
            (.natrec (subst (liftSubst σ') F') (subst σ' z') (subst σ' s') m'))
    (fun n m k k' d d' keqk' prop ih_prop hn_nat hm_nat ↦ by
      have hn_red : RedTerm pσNat n := redTerm_of_RedNatTerm hΔ hn_nat
      have hm_red : RedTerm pσ'Nat m := redTerm_of_RedNatTerm hΔ hm_nat
      have hnm_red : RedTermEq pσNat n m :=
        ⟨RedNatRel eqrel Δ, .nat (idRedWf (.nat hΔ)), .mk n m k k' d d' keqk' prop⟩
      have pσFn' := (hF hΔ (consSubstS hΔ hσ hNat hn_red)).red
      have pσFn := irrelevance' (singleSubstComp n σ F).symm pσFn'
      have pσ'F'm' := (hF' hΔ (consSubstS hΔ hσ' hNat hm_red)).red
      have pσ'F'm := irrelevance' (singleSubstComp m σ' F').symm pσ'F'm'
      have pσ'Fm' := (hF hΔ (consSubstS hΔ hσ' hNat hm_red)).red
      have pσ'Fm := irrelevance' (singleSubstComp m σ' F).symm pσ'Fm'
      have hσFn_eq_σ'Fm : RedEq pσFn (subst0 (subst (liftSubst σ') F) m) :=
        irrelevanceEq'' (singleSubstComp n σ F).symm (singleSubstComp m σ' F).symm
          pσFn' pσFn
          ((hF hΔ (consSubstS hΔ hσ hNat hn_red)).eq
            (consSubstS hΔ hσ' hNat hm_red)
            (consSubstSEqNat hσσ' pσNat hnm_red))
      have hσ'Fm_eq_σ'F'm : RedEq pσ'Fm (subst0 (subst (liftSubst σ') F') m) :=
        irrelevanceEq'' (singleSubstComp m σ' F).symm (singleSubstComp m σ' F').symm
          pσ'Fm' pσ'Fm (hFF' hΔ (consSubstS hΔ hσ' hNat hm_red))
      have hσFn_eq_σ'F'm : RedEq pσFn (subst0 (subst (liftSubst σ') F') m) :=
        transEq pσFn pσ'Fm pσ'F'm hσFn_eq_σ'Fm hσ'Fm_eq_σ'F'm
      cases prop with
      | @suc n' m' hnm'_nat =>
          rcases invRedNatTerm_suc hn_nat d.reduction with ⟨sn'_eq, hn'_nat⟩
          rcases invRedNatTerm_suc hm_nat d'.reduction with ⟨sm'_eq, hm'_nat⟩
          have hn'_red : RedTerm pσNat n' := redTerm_of_RedNatTerm hΔ hn'_nat
          have hm'_red : RedTerm pσ'Nat m' := redTerm_of_RedNatTerm hΔ hm'_nat
          have hn'm'_red : RedTermEq pσNat n' m' :=
            ⟨RedNatRel eqrel Δ, .nat (idRedWf (.nat hΔ)), hnm'_nat⟩
          have wfn' : HasType Δ n' .nat := escapeTerm pσNat hn'_red
          have wfm' : HasType Δ m' .nat := escapeTerm pσ'Nat hm'_red
          have hσsn' : RedTerm pσNat (.succ n') :=
            redTerm_of_RedNatTerm hΔ
              (.mk (.succ n') (.succ n') (idRedTermWf (.succ wfn')) sn'_eq (.suc hn'_nat))
          have hσ'sm' : RedTerm pσ'Nat (.succ m') :=
            redTerm_of_RedNatTerm hΔ
              (.mk (.succ m') (.succ m') (idRedTermWf (.succ wfm')) sm'_eq (.suc hm'_nat))
          rcases redSubstStarTerm d.reduction pσNat hσsn' with ⟨_, hσn_eq_σsn'⟩
          rcases redSubstStarTerm d'.reduction pσ'Nat hσ'sm' with ⟨_, hσ'm_eq_σ'sm'⟩
          have pσFsn' := irrelevance' (singleSubstComp (.succ n') σ F).symm
            (hF hΔ (consSubstS hΔ hσ hNat hσsn')).red
          have hFn_eq_Fsn' : RedEq pσFn (subst0 (subst (liftSubst σ) F) (.succ n')) :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (singleSubstComp (.succ n') σ F).symm
              pσFn' pσFn
              ((hF hΔ (consSubstS hΔ hσ hNat hn_red)).eq
                (consSubstS hΔ hσ hNat hσsn')
                (consSubstSEqNat (reflSubst hσ) pσNat hσn_eq_σsn'))
          have hFn_eq_Fsn'' :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (natrecIrrelevantSubst F z s n' σ)
              pσFn' pσFn
              ((hF hΔ (consSubstS hΔ hσ hNat hn_red)).eq
                (consSubstS hΔ hσ hNat hσsn')
                (consSubstSEqNat (reflSubst hσ) pσNat hσn_eq_σsn'))
          have pσFn'_step := irrelevance' (singleSubstComp n' σ F).symm
            (hF hΔ (consSubstS hΔ hσ hNat hn'_red)).red
          have pσFsn'' := irrelevance' (natrecIrrelevantSubst F z s n' σ)
            (hF hΔ (consSubstS hΔ hσ hNat hσsn')).red
          have pσFStep_red : RedType eqrel l Δ (subst σ (recStepType F)) := (hFStep hΔ hσ).red
          have pσFStep_n' : RedType eqrel l Δ
              (.pi (subst0 (subst (liftSubst σ) F) n')
                (subst (liftSubst (sgSubst n'))
                  (subst (liftSubst (liftSubst σ))
                    (wk1 (substKeep F (.succ (.var 0))))))) :=
            substSPi₁ pσFStep_red pσNat hn'_red
          have pσ'F'sm' := irrelevance' (singleSubstComp (.succ m') σ' F').symm
            (hF' hΔ (consSubstS hΔ hσ' hNat hσ'sm')).red
          have hF'm_eq_F'sm' : RedEq pσ'F'm (subst0 (subst (liftSubst σ') F') (.succ m')) :=
            irrelevanceEq'' (singleSubstComp m σ' F').symm (singleSubstComp (.succ m') σ' F').symm
              pσ'F'm' pσ'F'm
              ((hF' hΔ (consSubstS hΔ hσ' hNat hm_red)).eq
                (consSubstS hΔ hσ' hNat hσ'sm')
                (consSubstSEqNat (reflSubst hσ') pσ'Nat hσ'm_eq_σ'sm'))
          have pσ'Fm'_step := irrelevance' (singleSubstComp m' σ' F).symm
            (hF hΔ (consSubstS hΔ hσ' hNat hm'_red)).red
          have pσ'F'm'_step := irrelevance' (singleSubstComp m' σ' F').symm
            (hF' hΔ (consSubstS hΔ hσ' hNat hm'_red)).red
          have pσ'F'sm'' := irrelevance' (natrecIrrelevantSubst F' z' s' m' σ')
            (hF' hΔ (consSubstS hΔ hσ' hNat hσ'sm')).red
          have pσ'F'Step_red : RedType eqrel l Δ (subst σ' (recStepType F')) := (hF'Step hΔ hσ').red
          have pσ'F'Step_m' : RedType eqrel l Δ
              (.pi (subst0 (subst (liftSubst σ') F') m')
                (subst (liftSubst (sgSubst m'))
                  (subst (liftSubst (liftSubst σ'))
                    (wk1 (substKeep F' (.succ (.var 0))))))) :=
            substSPi₁ pσ'F'Step_red pσ'Nat hm'_red
          have hσFn'_eq_σ'Fm' : RedEq pσFn'_step (subst0 (subst (liftSubst σ') F) m') :=
            irrelevanceEq'' (singleSubstComp n' σ F).symm (singleSubstComp m' σ' F).symm
              (hF hΔ (consSubstS hΔ hσ hNat hn'_red)).red pσFn'_step
              ((hF hΔ (consSubstS hΔ hσ hNat hn'_red)).eq
                (consSubstS hΔ hσ' hNat hm'_red)
                (consSubstSEqNat hσσ' pσNat hn'm'_red))
          have hσ'Fm'_eq_σ'F'm' : RedEq pσ'Fm'_step (subst0 (subst (liftSubst σ') F') m') :=
            irrelevanceEq'' (singleSubstComp m' σ' F).symm (singleSubstComp m' σ' F').symm
              (hF hΔ (consSubstS hΔ hσ' hNat hm'_red)).red pσ'Fm'_step
              (hFF' hΔ (consSubstS hΔ hσ' hNat hm'_red))
          have hσFn'_eq_σ'F'm' : RedEq pσFn'_step (subst0 (subst (liftSubst σ') F') m') :=
            transEq pσFn'_step pσ'Fm'_step pσ'F'm'_step hσFn'_eq_σ'Fm' hσ'Fm'_eq_σ'F'm'
          have hs_term : RedTerm pσFStep_red (subst σ s) := (hs hΔ hσ).term
          have hs'_term : RedTerm pσ'F'Step_red (subst σ' s') := (hs' hΔ hσ').term
          have natrec_n' := natrecTerm hF hF0 hFStep hz hs hΔ hσ hn'_red
          have natrec_m' := natrecTerm hF' hF'0 hF'Step hz' hs' hΔ hσ' hm'_red
          have natrecN := appTerm pσFn'_step pσFsn'' pσFStep_n'
            (appTerm pσNat pσFStep_n' pσFStep_red hs_term hn'_red) natrec_n'
          have natrecN' : RedTerm pσFsn'
              (.app (.app (subst σ s) n') (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) n')) :=
            irrelevanceTerm'
              ((natrecIrrelevantSubst F z s n' σ).symm.trans (singleSubstComp (.succ n') σ F).symm)
              pσFsn'' pσFsn' natrecN
          have natrecM := appTerm pσ'F'm'_step pσ'F'sm'' pσ'F'Step_m'
            (appTerm pσ'Nat pσ'F'Step_m' pσ'F'Step_red hs'_term hm'_red) natrec_m'
          have natrecM' : RedTerm pσ'F'sm'
              (.app (.app (subst σ' s') m') (.natrec (subst (liftSubst σ') F') (subst σ' z') (subst σ' s') m')) :=
            irrelevanceTerm'
              ((natrecIrrelevantSubst F' z' s' m' σ').symm.trans (singleSubstComp (.succ m') σ' F').symm)
              pσ'F'sm'' pσ'F'sm' natrecM
          have hσs_eq_σ's := (hs hΔ hσ).eq hσ' hσσ'
          have hσ's_eq_σ's' := convEqTerm₂ (hFStep hΔ hσ).red (hFStep hΔ hσ').red
            ((hFStep hΔ hσ).eq hσ' hσσ') (hss' hΔ hσ')
          have hσs_eq_σ's' : RedTermEq pσFStep_red (subst σ s) (subst σ' s') :=
            transEqTerm pσFStep_red hσs_eq_σ's hσ's_eq_σ's'
          have ih_n'm' := ih_prop rfl rfl hn'_nat hm'_nat
          have appEq := convEqTerm₂ pσFn pσFsn'' hFn_eq_Fsn''
            (appCongTerm pσFn'_step pσFsn'' pσFStep_n'
              (appCongTerm (G := subst (liftSubst σ) (.pi F (wk1 (substKeep F (.succ (.var 0)))))) (u := n')
                pσNat pσFStep_n' pσFStep_red hσs_eq_σ's' hn'_red hm'_red hn'm'_red)
              natrec_n'
              (convTerm₂ pσFn'_step pσ'F'm'_step hσFn'_eq_σ'F'm' natrec_m')
              ih_n'm')
          have hRed1 := (natrecSubstStar wfF wfz wfs d.reduction pσNat hσsn' hPropF).trans
            ((Star.step (.natrecSucc wfn' wfF wfz wfs)
              (.refl (escapeTerm pσFsn' natrecN'))).conv
              (.symm (eqrel.typeToEq (escapeEq pσFn hFn_eq_Fsn'))))
          have hRed2 := (natrecSubstStar wfF' wfz' wfs' d'.reduction pσ'Nat hσ'sm' hPropF').trans
            ((Star.step (.natrecSucc wfm' wfF' wfz' wfs')
              (.refl (escapeTerm pσ'F'sm' natrecM'))).conv
              (.symm (eqrel.typeToEq (escapeEq pσ'F'm hF'm_eq_F'sm'))))
          have eq₁ := (redSubstStarTerm hRed1 pσFn (convTerm₂ pσFn pσFsn' hFn_eq_Fsn' natrecN')).2
          have eq₂ := (redSubstStarTerm hRed2 pσ'F'm (convTerm₂ pσ'F'm pσ'F'sm' hF'm_eq_F'sm' natrecM')).2
          exact transEqTerm pσFn eq₁
            (transEqTerm pσFn appEq
              (convEqTerm₂ pσFn pσ'F'm hσFn_eq_σ'F'm (symEqTerm pσ'F'm eq₂)))
      | zero =>
          have z_eq := invRedNatTerm_zero hn_nat d.reduction
          have z'_eq := invRedNatTerm_zero hm_nat d'.reduction
          have hσ0 : RedTerm pσNat .zero :=
            redTerm_of_RedNatTerm hΔ (.mk .zero .zero (idRedTermWf (.zero hΔ)) z_eq .zero)
          have hσ'0 : RedTerm pσ'Nat .zero :=
            redTerm_of_RedNatTerm hΔ (.mk .zero .zero (idRedTermWf (.zero hΔ)) z'_eq .zero)
          rcases redSubstStarTerm d.reduction pσNat hσ0 with ⟨_, hσn_eq_σ0⟩
          rcases redSubstStarTerm d'.reduction pσ'Nat hσ'0 with ⟨_, hσ'm_eq_σ'0⟩
          have hσn_eq_σ'0 : RedTermEq pσNat n .zero :=
            transEqTerm pσNat hnm_red hσ'm_eq_σ'0
          have hFn_eq_F0_raw :=
            (hF hΔ (consSubstS hΔ hσ hNat hn_red)).eq
              (consSubstS hΔ hσ hNat hσ0)
              (consSubstSEqNat (reflSubst hσ) pσNat hσn_eq_σ0)
          have hFn_eq_F0 : RedEq pσFn (subst σ (subst0 F .zero)) :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (substConsId F) pσFn' pσFn hFn_eq_F0_raw
          have hFn_eq_F0'' : RedEq pσFn (subst0 (subst (liftSubst σ) F) .zero) :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (singleSubstComp .zero σ F).symm
              pσFn' pσFn hFn_eq_F0_raw
          have hσFn_eq_σ'F0_raw :=
            (hF hΔ (consSubstS hΔ hσ hNat hn_red)).eq
              (consSubstS hΔ hσ' hNat hσ'0)
              (consSubstSEqNat hσσ' pσNat hσn_eq_σ'0)
          have hσFn_eq_σ'F0 : RedEq pσFn (subst σ' (subst0 F .zero)) :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (substConsId F) pσFn' pσFn hσFn_eq_σ'F0_raw
          have hF'm_eq_F'0_raw :=
            (hF' hΔ (consSubstS hΔ hσ' hNat hm_red)).eq
              (consSubstS hΔ hσ' hNat hσ'0)
              (consSubstSEqNat (reflSubst hσ') pσ'Nat hσ'm_eq_σ'0)
          have hF'm_eq_F'0 : RedEq pσ'F'm (subst σ' (subst0 F' .zero)) :=
            irrelevanceEq'' (singleSubstComp m σ' F').symm (substConsId F') pσ'F'm' pσ'F'm hF'm_eq_F'0_raw
          have hF'm_eq_F'0'' : RedEq pσ'F'm (subst0 (subst (liftSubst σ') F') .zero) :=
            irrelevanceEq'' (singleSubstComp m σ' F').symm (singleSubstComp .zero σ' F').symm
              pσ'F'm' pσ'F'm hF'm_eq_F'0_raw
          have hσz_eq_σ'z := convEqTerm₂ pσFn (hF0 hΔ hσ).red hFn_eq_F0 ((hz hΔ hσ).eq hσ' hσσ')
          have hσ'z_eq_σ'z' := convEqTerm₂ pσFn (hF0 hΔ hσ').red hσFn_eq_σ'F0 (hzz' hΔ hσ')
          have hσz_eq_σ'z' := transEqTerm pσFn hσz_eq_σ'z hσ'z_eq_σ'z'
          have hRed1 := (natrecSubstStar wfF wfz wfs d.reduction pσNat hσ0 hPropF).trans
            ((Star.step (.natrecZero wfF wfz wfs) (.refl wfz)).conv
              (.symm (eqrel.typeToEq (escapeEq pσFn hFn_eq_F0''))))
          have hRed2 := (natrecSubstStar wfF' wfz' wfs' d'.reduction pσ'Nat hσ'0 hPropF').trans
            ((Star.step (.natrecZero wfF' wfz' wfs') (.refl wfz')).conv
              (.symm (eqrel.typeToEq (escapeEq pσ'F'm hF'm_eq_F'0''))))
          have eq₁ := (redSubstStarTerm hRed1 pσFn (convTerm₂ pσFn (hF0 hΔ hσ).red hFn_eq_F0 (hz hΔ hσ).term)).2
          have eq₂ := (redSubstStarTerm hRed2 pσ'F'm (convTerm₂ pσ'F'm (hF'0 hΔ hσ').red hF'm_eq_F'0 (hz' hΔ hσ').term)).2
          exact transEqTerm pσFn eq₁
            (transEqTerm pσFn hσz_eq_σ'z'
              (convEqTerm₂ pσFn pσ'F'm hσFn_eq_σ'F'm (symEqTerm pσ'F'm eq₂)))
      | ne nf =>
          rcases invRedNatTerm_ne hn_nat d.reduction nf.neK with ⟨_, nfN⟩
          rcases invRedNatTerm_ne hm_nat d'.reduction nf.neM with ⟨_, nfM⟩
          have hσn' : RedTerm pσNat k := neuTerm pσNat nfN.neK nfN.hk nfN.keqk
          have hσ'm' : RedTerm pσ'Nat k' := neuTerm pσ'Nat nfM.neK nfM.hk nfM.keqk
          rcases redSubstStarTerm d.reduction pσNat hσn' with ⟨_, hσn_eq_σn'⟩
          rcases redSubstStarTerm d'.reduction pσ'Nat hσ'm' with ⟨_, hσ'm_eq_σ'm'⟩
          have pσFn'_ne := irrelevance' (singleSubstComp k σ F).symm
            (hF hΔ (consSubstS hΔ hσ hNat hσn')).red
          have hFn_eq_Fn' : RedEq pσFn (subst0 (subst (liftSubst σ) F) k) :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (singleSubstComp k σ F).symm
              pσFn' pσFn
              ((hF hΔ (consSubstS hΔ hσ hNat hn_red)).eq
                (consSubstS hΔ hσ hNat hσn')
                (consSubstSEqNat (reflSubst hσ) pσNat hσn_eq_σn'))
          have pσ'F'm'_ne := irrelevance' (singleSubstComp k' σ' F').symm
            (hF' hΔ (consSubstS hΔ hσ' hNat hσ'm')).red
          have hF'm_eq_F'm' : RedEq pσ'F'm (subst0 (subst (liftSubst σ') F') k') :=
            irrelevanceEq'' (singleSubstComp m σ' F').symm (singleSubstComp k' σ' F').symm
              pσ'F'm' pσ'F'm
              ((hF' hΔ (consSubstS hΔ hσ' hNat hm_red)).eq
                (consSubstS hΔ hσ' hNat hσ'm')
                (consSubstSEqNat (reflSubst hσ') pσ'Nat hσ'm_eq_σ'm'))
          have hσFn'_eq_σ'Fm'_ne : RedEq pσFn'_ne (subst0 (subst (liftSubst σ') F') k') :=
            transEq pσFn'_ne pσFn pσ'F'm'_ne (symEq pσFn pσFn'_ne hFn_eq_Fn')
              (transEq pσFn pσ'F'm pσ'F'm'_ne hσFn_eq_σ'F'm hF'm_eq_F'm')
          have wfFF := escapeEq pσF (reflEq pσF)
          have wfzz : eqrel.TermEqRel Δ (subst σ z) (subst σ z) (subst0 (subst (liftSubst σ) F) .zero) := by
            have h := escapeTermEq (hF0 hΔ hσ).red (reflEqTerm (hF0 hΔ hσ).red (hz hΔ hσ).term)
            rwa [singleSubstLift F .zero] at h
          have wfss : eqrel.TermEqRel Δ (subst σ s) (subst σ s) (recStepType (subst (liftSubst σ) F)) := by
            have h := escapeTermEq (hFStep hΔ hσ).red (reflEqTerm (hFStep hΔ hσ).red (hs hΔ hσ).term)
            rwa [natrecSucCase σ F] at h
          have wfF'F' := escapeEq pσ'F' (reflEq pσ'F')
          have wfz'z' : eqrel.TermEqRel Δ (subst σ' z') (subst σ' z') (subst0 (subst (liftSubst σ') F') .zero) := by
            have h := escapeTermEq (hF'0 hΔ hσ').red (reflEqTerm (hF'0 hΔ hσ').red (hz' hΔ hσ').term)
            rwa [singleSubstLift F' .zero] at h
          have wfs's' : eqrel.TermEqRel Δ (subst σ' s') (subst σ' s') (recStepType (subst (liftSubst σ') F')) := by
            have h := escapeTermEq (hF'Step hΔ hσ').red (reflEqTerm (hF'Step hΔ hσ').red (hs' hΔ hσ').term)
            rwa [natrecSucCase σ' F'] at h
          have hσF_eq_σ'F : eqrel.TypeEqRel (.nat :: Δ) (subst (liftSubst σ) F) (subst (liftSubst σ') F) :=
            escapeEq pσF ((hF (.cons hΔ wfNat) hLiftσ).eq hLiftσ' (liftSubstSEq hΔ hNat hσ hσσ'))
          have hσ'F_eq_σ'F' : eqrel.TypeEqRel (.nat :: Δ) (subst (liftSubst σ') F) (subst (liftSubst σ') F') :=
            escapeEq pσ'F (hFF' (.cons hΔ wfNat) hLiftσ')
          have hFF'_syn : eqrel.TypeEqRel (.nat :: Δ) (subst (liftSubst σ) F) (subst (liftSubst σ') F') :=
            eqrel.transType hσF_eq_σ'F hσ'F_eq_σ'F'
          have hσz_eq_σ'z : eqrel.TermEqRel Δ (subst σ z) (subst σ' z) (subst0 (subst (liftSubst σ) F) .zero) := by
            have h := escapeTermEq (hF0 hΔ hσ).red ((hz hΔ hσ).eq hσ' hσσ')
            rwa [singleSubstLift F .zero] at h
          have hσ'z_eq_σ'z' : eqrel.TermEqRel Δ (subst σ' z) (subst σ' z') (subst0 (subst (liftSubst σ) F) .zero) := by
            have h := eqrel.convTerm (escapeTermEq (hF0 hΔ hσ').red (hzz' hΔ hσ'))
              (.symm (eqrel.typeToEq (escapeEq (hF0 hΔ hσ).red ((hF0 hΔ hσ).eq hσ' hσσ'))))
            rwa [singleSubstLift F .zero] at h
          have hzz'_syn : eqrel.TermEqRel Δ (subst σ z) (subst σ' z') (subst0 (subst (liftSubst σ) F) .zero) :=
            eqrel.transTerm hσz_eq_σ'z hσ'z_eq_σ'z'
          have hσs_eq_σ's : eqrel.TermEqRel Δ (subst σ s) (subst σ' s) (recStepType (subst (liftSubst σ) F)) := by
            have h := escapeTermEq (hFStep hΔ hσ).red ((hs hΔ hσ).eq hσ' hσσ')
            rwa [natrecSucCase σ F] at h
          have hσ's_eq_σ's' : eqrel.TermEqRel Δ (subst σ' s) (subst σ' s') (recStepType (subst (liftSubst σ) F)) := by
            have h := eqrel.convTerm (escapeTermEq (hFStep hΔ hσ').red (hss' hΔ hσ'))
              (.symm (eqrel.typeToEq (escapeEq (hFStep hΔ hσ).red ((hFStep hΔ hσ).eq hσ' hσσ'))))
            rwa [natrecSucCase σ F] at h
          have hss'_syn : eqrel.TermEqRel Δ (subst σ s) (subst σ' s') (recStepType (subst (liftSubst σ) F)) :=
            eqrel.transTerm hσs_eq_σ's hσ's_eq_σ's'
          have natrecN := neuTerm pσFn'_ne (.natrec nfN.neK) (.natrec wfF wfz wfs nfN.hk)
            (eqrel.natrecCong wfFF wfzz wfss nfN.keqk)
          have natrecM := neuTerm pσ'F'm'_ne (.natrec nfM.neK) (.natrec wfF' wfz' wfs' nfM.hk)
            (eqrel.natrecCong wfF'F' wfz'z' wfs's' nfM.keqk)
          have natrecN_eq_M := convEqTerm₂ pσFn pσFn'_ne hFn_eq_Fn'
            (neuEqTerm pσFn'_ne (.natrec nfN.neK) (.natrec nfM.neK)
              (.natrec wfF wfz wfs nfN.hk)
              (.conv (.natrec wfF' wfz' wfs' nfM.hk)
                (.symm (eqrel.typeToEq (escapeEq pσFn'_ne hσFn'_eq_σ'Fm'_ne))))
              (eqrel.natrecCong hFF'_syn hzz'_syn hss'_syn nf.keqm))
          have hRed1 := natrecSubstStar wfF wfz wfs d.reduction pσNat hσn' hPropF
          have hRed2 := natrecSubstStar wfF' wfz' wfs' d'.reduction pσ'Nat hσ'm' hPropF'
          have eq₁ := (redSubstStarTerm hRed1 pσFn (convTerm₂ pσFn pσFn'_ne hFn_eq_Fn' natrecN)).2
          have eq₂ := (redSubstStarTerm hRed2 pσ'F'm (convTerm₂ pσ'F'm pσ'F'm'_ne hF'm_eq_F'm' natrecM)).2
          exact transEqTerm pσFn eq₁
            (transEqTerm pσFn natrecN_eq_M
              (convEqTerm₂ pσFn pσ'F'm hσFn_eq_σ'F'm (symEqTerm pσ'F'm eq₂))))
    (fun {_ _} _ ih {n' m'} hk hk' hn' hm' ↦ by
      injection hk with h₁
      injection hk' with h₂
      subst h₁ h₂
      exact ih hn' hm')
    (fun {n' m'} hk ↦ by cases hk)
    (fun {_ _} nf {n' m'} hk ↦ by subst hk; cases nf.neK)
    n m hnm_nat hn_nat hm_nat

/-- Validity of natural recursion (`natrecᵛ`). -/
theorem natrecValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context}
    {F z s n : Term}
    (hNat : ValidType eqrel l Γ .nat)
    (hF : ValidType eqrel l (.nat :: Γ) F)
    (hF0 : ValidType eqrel l Γ (subst0 F .zero))
    (hFStep : ValidType eqrel l Γ (recStepType F))
    (hFn : ValidType eqrel l Γ (subst0 F n))
    (hz : ValidTerm hF0 z)
    (hs : ValidTerm hFStep s)
    (hn : ValidTerm hNat n) :
    ValidTerm hFn (.natrec F z s n) := by
  intro Δ σ hΔ hσ
  have hσn' : RedTerm (redNat (eqrel := eqrel) (l := l) hΔ) (subst σ n) :=
    irrelevanceTerm (hNat hΔ hσ).red (redNat hΔ) (hn hΔ hσ).term
  have eqPrf : subst0 (subst (liftSubst σ) F) (subst σ n) = subst σ (subst0 F n) :=
    (singleSubstLift F n).symm
  have pFn_raw := irrelevance' (singleSubstComp (subst σ n) σ F).symm
    (hF hΔ (consSubstS hΔ hσ (natValid (l := l)) hσn')).red
  refine ⟨irrelevanceTerm' eqPrf pFn_raw (hFn hΔ hσ).red
      (natrecTerm hF hF0 hFStep hz hs hΔ hσ hσn'),
    fun {σ'} hσ' hσσ' ↦ ?_⟩
  have hσ'n' : RedTerm (redNat (eqrel := eqrel) (l := l) hΔ) (subst σ' n) :=
    irrelevanceTerm (hNat hΔ hσ').red (redNat hΔ) (hn hΔ hσ').term
  have hσn_eq_σ'n : RedTermEq (redNat (eqrel := eqrel) (l := l) hΔ) (subst σ n) (subst σ' n) :=
    irrelevanceEqTerm (hNat hΔ hσ).red (redNat hΔ) ((hn hΔ hσ).eq hσ' hσσ')
  exact irrelevanceEqTerm' eqPrf pFn_raw (hFn hΔ hσ).red
    (natrecCongTerm hF hF (reflValid hF)
      hF0 hF0 (reflValid hF0)
      hFStep hFStep (reflValid hFStep)
      hz hz (reflValidTerm hF0 hz)
      hs hs (reflValidTerm hFStep hs)
      hΔ hσ hσ' hσσ' hσn' hσ'n' hσn_eq_σ'n)

/-- Validity of natural recursion congruence (`natrec-congᵛ`). -/
theorem natrecCongValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context}
    {F F' z z' s s' n n' : Term}
    (hNat : ValidType eqrel l Γ .nat)
    (hF : ValidType eqrel l (.nat :: Γ) F)
    (hF' : ValidType eqrel l (.nat :: Γ) F')
    (hFF' : ValidTypeEq hF F')
    (hF0 : ValidType eqrel l Γ (subst0 F .zero))
    (hF'0 : ValidType eqrel l Γ (subst0 F' .zero))
    (hF0F'0 : ValidTypeEq hF0 (subst0 F' .zero))
    (hFStep : ValidType eqrel l Γ (recStepType F))
    (hF'Step : ValidType eqrel l Γ (recStepType F'))
    (hFStepEq : ValidTypeEq hFStep (recStepType F'))
    (hFn : ValidType eqrel l Γ (subst0 F n))
    (hz : ValidTerm hF0 z)
    (hz' : ValidTerm hF'0 z')
    (hzz' : ValidTermEq hF0 z z')
    (hs : ValidTerm hFStep s)
    (hs' : ValidTerm hF'Step s')
    (hss' : ValidTermEq hFStep s s')
    (hn : ValidTerm hNat n)
    (hn' : ValidTerm hNat n')
    (hnn' : ValidTermEq hNat n n') :
    ValidTermEq hFn (.natrec F z s n) (.natrec F' z' s' n') := by
  intro Δ σ hΔ hσ
  have hσn' : RedTerm (redNat (eqrel := eqrel) (l := l) hΔ) (subst σ n) :=
    irrelevanceTerm (hNat hΔ hσ).red (redNat hΔ) (hn hΔ hσ).term
  have hσn'' : RedTerm (redNat (eqrel := eqrel) (l := l) hΔ) (subst σ n') :=
    irrelevanceTerm (hNat hΔ hσ).red (redNat hΔ) (hn' hΔ hσ).term
  have hσn_eq_σn' : RedTermEq (redNat (eqrel := eqrel) (l := l) hΔ) (subst σ n) (subst σ n') :=
    irrelevanceEqTerm (hNat hΔ hσ).red (redNat hΔ) (hnn' hΔ hσ)
  have pFn_raw := irrelevance' (singleSubstComp (subst σ n) σ F).symm
    (hF hΔ (consSubstS hΔ hσ (natValid (l := l)) hσn')).red
  exact irrelevanceEqTerm' (singleSubstLift F n).symm pFn_raw (hFn hΔ hσ).red
    (natrecCongTerm hF hF' hFF'
      hF0 hF'0 hF0F'0
      hFStep hF'Step hFStepEq
      hz hz' hzz'
      hs hs' hss'
      hΔ hσ hσ (reflSubst hσ)
      hσn' hσn'' hσn_eq_σn')
/-!
## Fundamental Theorem (`Definition/LogicalRelation/Fundamental.agda`, Theorem 3.21 & Theorem 3.23)
-/

/-- Fundamental theorem for variables (`fundamentalVar`). -/
theorem fundamentalVar {eqrel : EqRelSet} {Γ : Context} {A : Term} {x : Nat}
    (hMem : Member x A Γ) (hΓ : ValidCtx eqrel Γ) :
    ∃ (hA : ValidType eqrel .one Γ A), ValidTerm hA (.var x) := by
  induction hMem with
  | @here Γ A₀ =>
      cases hΓ with
      | @cons _ _ l hΓ₀ hA₀ =>
          have hA : ValidType eqrel .one (A₀ :: Γ) (wk1 A₀) :=
            maybeEmbValid (wk1Valid (F := A₀) hA₀)
          refine ⟨hA, fun {Δ σ} hΔ hσ ↦ ?_⟩
          have pA₀ : RedType eqrel l Δ (subst (tailSubst σ) A₀) := (hA₀ hΔ hσ.tail).red
          have pA' : RedType eqrel .one Δ (subst σ (wk1 A₀)) := (hA hΔ hσ).red
          refine ⟨irrelevanceTerm' (subst_wk A₀).symm pA₀ pA' (hσ.head hA₀ hΔ),
            fun {σ'} hσ' hσσ' ↦
              irrelevanceEqTerm' (subst_wk A₀).symm pA₀ pA' (hσσ'.head hA₀ hΔ hσ)⟩
  | @there Γ A₀ B x hMem ih =>
      cases hΓ with
      | cons hΓ₀ _ =>
          rcases ih hΓ₀ with ⟨hA₀, hVar₀⟩
          have hA : ValidType eqrel .one (B :: Γ) (wk1 A₀) := wk1Valid (F := B) hA₀
          refine ⟨hA, fun {Δ σ} hΔ hσ ↦ ?_⟩
          have pA₀ : RedType eqrel .one Δ (subst (tailSubst σ) A₀) := (hA₀ hΔ hσ.tail).red
          have pA' : RedType eqrel .one Δ (subst σ (wk1 A₀)) := (hA hΔ hσ).red
          refine ⟨irrelevanceTerm' (subst_wk A₀).symm pA₀ pA' (hVar₀ hΔ hσ.tail).term,
            fun {σ'} hσ' hσσ' ↦
              irrelevanceEqTerm' (subst_wk A₀).symm pA₀ pA'
                ((hVar₀ hΔ hσ.tail).eq hσ'.tail hσσ'.tail)⟩











theorem fund_type_fromUniv {eqrel : EqRelSet} {Γ : Context} {A : Term}
    (ihA : FundTermMotive eqrel Γ A .univ) :
    FundTypeMotive eqrel Γ A := by
  rcases ihA with ⟨hΓ, hU, hAt⟩
  exact ⟨hΓ, univValid (l' := .one) hU hAt⟩

theorem fund_term_pi {eqrel : EqRelSet} {Γ : Context} {F G : Term}
    (ihF : FundTermMotive eqrel Γ F .univ)
    (ihG : FundTermMotive eqrel (F :: Γ) G .univ) :
    FundTermMotive eqrel Γ (.pi F G) .univ := by
  rcases ihF with ⟨hΓ, hU, hFt⟩
  rcases ihG with ⟨_, hU₁, hGt⟩
  have hF : ValidType eqrel .one Γ F := univValid (l' := .one) hU hFt
  have hU₀ : ValidType eqrel .one Γ .univ := UValid
  have hU' : ValidType eqrel .one (F :: Γ) .univ := UValid
  have hFt' : ValidTerm hU₀ F := irrelevanceValidTerm hU hU₀ hFt
  have hGt' : ValidTerm hU' G := irrelevanceValidTerm hU₁ hU' hGt
  exact ⟨hΓ, hU, irrelevanceValidTerm hU₀ hU (piTermValid hF hU' hFt' hGt')⟩

theorem fund_term_lam {eqrel : EqRelSet} {Γ : Context} {F G t : Term}
    (ihF : FundTypeMotive eqrel Γ F)
    (iht : FundTermMotive eqrel (F :: Γ) t G) :
    FundTermMotive eqrel Γ (.lam t) (.pi F G) := by
  rcases ihF with ⟨hΓ, hF⟩
  rcases iht with ⟨_, hG, ht⟩
  exact ⟨hΓ, piValid hF hG, lamValid hF hG ht⟩

theorem fund_term_app {eqrel : EqRelSet} {Γ : Context} {g a F G : Term}
    (ihg : FundTermMotive eqrel Γ g (.pi F G))
    (iha : FundTermMotive eqrel Γ a F) :
    FundTermMotive eqrel Γ (.app g a) (subst0 G a) := by
  rcases ihg with ⟨_, hPiFG, hg⟩
  rcases iha with ⟨hΓ₁, hF, ha⟩
  exact ⟨hΓ₁, substSPi hF hPiFG ha, appValid hF hPiFG hg ha⟩

theorem fund_term_suc {eqrel : EqRelSet} {Γ : Context} {n : Term}
    (ihn : FundTermMotive eqrel Γ n .nat) :
    FundTermMotive eqrel Γ (.succ n) .nat := by
  rcases ihn with ⟨hΓ, hNat, hn⟩
  exact ⟨hΓ, hNat, sucValid hNat hn⟩

theorem fund_term_natrec {eqrel : EqRelSet} {Γ : Context} {G z s n : Term}
    (ihG : FundTypeMotive eqrel (.nat :: Γ) G)
    (ihz : FundTermMotive eqrel Γ z (subst0 G .zero))
    (ihs : FundTermMotive eqrel Γ s (recStepType G))
    (ihn : FundTermMotive eqrel Γ n .nat) :
    FundTermMotive eqrel Γ (.natrec G z s n) (subst0 G n) := by
  rcases ihG with ⟨_, hG⟩
  rcases ihz with ⟨_, hG0, hz⟩
  rcases ihs with ⟨_, hGStep, hs⟩
  rcases ihn with ⟨hΓ₃, hNat, hn⟩
  have hGn : ValidType eqrel .one Γ (subst0 G n) := substS hNat hG hn
  exact ⟨hΓ₃, hGn, natrecValid hNat hG hG0 hGStep hGn hz hs hn⟩

theorem fund_term_conv {eqrel : EqRelSet} {Γ : Context} {t A A' : Term}
    (iht : FundTermMotive eqrel Γ t A')
    (ihEq : FundTypeEqMotive eqrel Γ A' A) :
    FundTermMotive eqrel Γ t A := by
  rcases iht with ⟨_, hA', ht⟩
  rcases ihEq with ⟨hΓ₁, hA'₁, hA, hA'A⟩
  have ht' : ValidTerm hA'₁ t := irrelevanceValidTerm hA' hA'₁ ht
  exact ⟨hΓ₁, hA, convValid hA'₁ hA hA'A ht'⟩

theorem fund_typeEq_fromUniv {eqrel : EqRelSet} {Γ : Context} {A B : Term}
    (ihEq : FundTermEqMotive eqrel Γ A B .univ) :
    FundTypeEqMotive eqrel Γ A B := by
  rcases ihEq with ⟨hΓ, hU, hAt, hBt, hABt⟩
  have hA : ValidType eqrel .one Γ A := univValid (l' := .one) hU hAt
  have hB : ValidType eqrel .one Γ B := univValid (l' := .one) hU hBt
  exact ⟨hΓ, hA, hB, fun {Δ σ} hΔ hσ ↦ univEqEq (hU hΔ hσ).red (hA hΔ hσ).red (hABt hΔ hσ)⟩

theorem fund_typeEq_refl {eqrel : EqRelSet} {Γ : Context} {A : Term}
    (ihA : FundTypeMotive eqrel Γ A) :
    FundTypeEqMotive eqrel Γ A A :=
  ⟨ihA.1, ihA.2, ihA.2, fun {_ _} hΔ hσ ↦ reflEq (ihA.2 hΔ hσ).red⟩

theorem fund_typeEq_symm {eqrel : EqRelSet} {Γ : Context} {A B : Term}
    (ihEq : FundTypeEqMotive eqrel Γ B A) :
    FundTypeEqMotive eqrel Γ A B := by
  rcases ihEq with ⟨hΓ, hB, hA, hBA⟩
  exact ⟨hΓ, hA, hB, fun {Δ σ} hΔ hσ ↦ symEq (hB hΔ hσ).red (hA hΔ hσ).red (hBA hΔ hσ)⟩

theorem fund_typeEq_trans {eqrel : EqRelSet} {Γ : Context} {A B₁ B : Term}
    (ih₁ : FundTypeEqMotive eqrel Γ A B₁)
    (ih₂ : FundTypeEqMotive eqrel Γ B₁ B) :
    FundTypeEqMotive eqrel Γ A B := by
  rcases ih₁ with ⟨hΓ, hA, hB₁, hAB₁⟩
  rcases ih₂ with ⟨_, hB₁', hB, hB₁B⟩
  exact ⟨hΓ, hA, hB, fun {Δ σ} hΔ hσ ↦
    transEq (hA hΔ hσ).red (hB₁ hΔ hσ).red (hB hΔ hσ).red
      (hAB₁ hΔ hσ)
      (irrelevanceEq (hB₁' hΔ hσ).red (hB₁ hΔ hσ).red (hB₁B hΔ hσ))⟩

theorem fund_typeEq_pi {eqrel : EqRelSet} {Γ : Context} {F H G E : Term}
    (ihFH : FundTypeEqMotive eqrel Γ F H)
    (ihGE : FundTypeEqMotive eqrel (F :: Γ) G E) :
    FundTypeEqMotive eqrel Γ (.pi F G) (.pi H E) := by
  rcases ihFH with ⟨hΓ, hF, hH, hFH⟩
  rcases ihGE with ⟨_, hG, hE, hGE⟩
  have hE' : ValidType eqrel .one (H :: Γ) E := irrelevanceLift hF hH hFH hE
  exact ⟨hΓ, piValid hF hG, piValid hH hE', piCongValid hF hG hH hE' hFH hGE⟩

theorem fund_termEq_refl {eqrel : EqRelSet} {Γ : Context} {t A : Term}
    (iht : FundTermMotive eqrel Γ t A) :
    FundTermEqMotive eqrel Γ t t A := by
  rcases iht with ⟨hΓ, hA, ht⟩
  exact ⟨hΓ, hA, ht, ht, fun {Δ σ} hΔ hσ ↦ reflEqTerm (hA hΔ hσ).red (ht hΔ hσ).term⟩

theorem fund_termEq_symm {eqrel : EqRelSet} {Γ : Context} {t t' A : Term}
    (ihEq : FundTermEqMotive eqrel Γ t' t A) :
    FundTermEqMotive eqrel Γ t t' A := by
  rcases ihEq with ⟨hΓ, hA, ht', ht, ht't⟩
  exact ⟨hΓ, hA, ht, ht', fun {Δ σ} hΔ hσ ↦ symEqTerm (hA hΔ hσ).red (ht't hΔ hσ)⟩

theorem fund_termEq_trans {eqrel : EqRelSet} {Γ : Context} {t u r A : Term}
    (ih₁ : FundTermEqMotive eqrel Γ t u A)
    (ih₂ : FundTermEqMotive eqrel Γ u r A) :
    FundTermEqMotive eqrel Γ t r A := by
  rcases ih₁ with ⟨hΓ, hA, ht, _, htu⟩
  rcases ih₂ with ⟨_, hA₁, _, hr, hur⟩
  have hr' : ValidTerm hA r := irrelevanceValidTerm hA₁ hA hr
  exact ⟨hΓ, hA, ht, hr', fun {Δ σ} hΔ hσ ↦
    transEqTerm (hA hΔ hσ).red (htu hΔ hσ)
      (irrelevanceEqTerm (hA₁ hΔ hσ).red (hA hΔ hσ).red (hur hΔ hσ))⟩

theorem fund_termEq_conv {eqrel : EqRelSet} {Γ : Context} {t u A' A : Term}
    (ihEq : FundTermEqMotive eqrel Γ t u A')
    (ihAB : FundTypeEqMotive eqrel Γ A' A) :
    FundTermEqMotive eqrel Γ t u A := by
  rcases ihEq with ⟨_, hA', ht, hu, htu⟩
  rcases ihAB with ⟨hΓ₁, hA'₁, hA, hA'A⟩
  have ht' : ValidTerm hA t := convValid hA'₁ hA hA'A (irrelevanceValidTerm hA' hA'₁ ht)
  have hu' : ValidTerm hA u := convValid hA'₁ hA hA'A (irrelevanceValidTerm hA' hA'₁ hu)
  exact ⟨hΓ₁, hA, ht', hu', fun {Δ σ} hΔ hσ ↦
    convEqTerm₁ (hA'₁ hΔ hσ).red (hA hΔ hσ).red (hA'A hΔ hσ)
      (irrelevanceEqTerm (hA' hΔ hσ).red (hA'₁ hΔ hσ).red (htu hΔ hσ))⟩

theorem fund_termEq_pi {eqrel : EqRelSet} {Γ : Context} {E F G H : Term}
    (ihF : FundTypeMotive eqrel Γ F)
    (ihFH : FundTermEqMotive eqrel Γ F H .univ)
    (ihGE : FundTermEqMotive eqrel (F :: Γ) G E .univ) :
    FundTermEqMotive eqrel Γ (.pi F G) (.pi H E) .univ := by
  rcases ihF with ⟨hΓ, hF⟩
  rcases ihFH with ⟨_, hU₀, hFt, hHt, hFHt⟩
  rcases ihGE with ⟨_, hU₁, hGt, hEt, hGEt⟩
  have hU' : ValidType eqrel .one Γ .univ := UValid
  have hFt' : ValidTerm hU' F := irrelevanceValidTerm hU₀ hU' hFt
  have hHt' : ValidTerm hU' H := irrelevanceValidTerm hU₀ hU' hHt
  have hH : ValidType eqrel .one Γ H := univValid hU' hHt'
  have hFH : ValidTypeEq hF H := univEqValid hU₀ hF hFHt
  have hU₁' : ValidType eqrel .one (F :: Γ) .univ := UValid
  have hU₂' : ValidType eqrel .one (H :: Γ) .univ := UValid
  have hGt' : ValidTerm hU₁' G := irrelevanceValidTerm hU₁ hU₁' hGt
  have hEt_F : ValidTerm hU₁' E := irrelevanceValidTerm hU₁ hU₁' hEt
  have hEt' : ValidTerm hU₂' E :=
    irrelevanceValidTerm (irrelevanceLift hF hH hFH hU₁') hU₂'
      (irrelevanceTermLift hF hH hFH hU₁' hEt_F)
  have hFHt' : ValidTermEq hU' F H := irrelevanceValidEqTerm hU₀ hU' hFHt
  have hGEt' : ValidTermEq hU₁' G E := irrelevanceValidEqTerm hU₁ hU₁' hGEt
  exact ⟨hΓ, hU',
    piTermValid hF hU₁' hFt' hGt',
    piTermValid hH hU₂' hHt' hEt',
    piCongTermValid hF hH hU₁' hU₂' hFt' hGt' hHt' hEt' hFHt' hGEt'⟩

theorem fund_termEq_app {eqrel : EqRelSet} {Γ : Context} {f g a b F G : Term}
    (ihfg : FundTermEqMotive eqrel Γ f g (.pi F G))
    (ihab : FundTermEqMotive eqrel Γ a b F) :
    FundTermEqMotive eqrel Γ (.app f a) (.app g b) (subst0 G a) := by
  rcases ihfg with ⟨_, hPiFG, hf, hg, hfg⟩
  rcases ihab with ⟨hΓ₁, hF, ha, hb, hab⟩
  have hGa : ValidType eqrel .one Γ (subst0 G a) := substSPi hF hPiFG ha
  have hGb : ValidType eqrel .one Γ (subst0 G b) := substSPi hF hPiFG hb
  have hGaGb : ValidTypeEq hGa (subst0 G b) :=
    substSPiEq hF hF hPiFG hPiFG (reflValid hPiFG) ha hb hab
  exact ⟨hΓ₁, hGa,
    appValid hF hPiFG hf ha,
    conv2Valid hGa hGb hGaGb (appValid hF hPiFG hg hb),
    appCongValid hF hPiFG hfg ha hb hab⟩

theorem fund_termEq_beta {eqrel : EqRelSet} {Γ : Context} {a b F G : Term}
    (ihb : FundTermMotive eqrel (F :: Γ) b G)
    (iha : FundTermMotive eqrel Γ a F) :
    FundTermEqMotive eqrel Γ (.app (.lam b) a) (subst0 b a) (subst0 G a) := by
  rcases ihb with ⟨_, hG, hb⟩
  rcases iha with ⟨hΓ, hF₁, ha⟩
  have hGa : ValidType eqrel .one Γ (subst0 G a) := substS hF₁ hG ha
  have hba : ValidTerm hGa (subst0 b a) := substSTerm hF₁ hG hb ha
  have hRed : ValidRedTerm eqrel Γ (.app (.lam b) a) (subst0 b a) (subst0 G a) := by
    intro Δ σ hΔ hσ
    have hLiftσ := liftSubstS hΔ hF₁ hσ
    have wfσF : TypeWf Δ (subst σ F) := escape (hF₁ hΔ hσ).red
    have wfσb : HasType (subst σ F :: Δ) (subst (liftSubst σ) b) (subst (liftSubst σ) G) :=
      escapeTerm (hG (.cons hΔ wfσF) hLiftσ).red (hb (.cons hΔ wfσF) hLiftσ).term
    have wfσa : HasType Δ (subst σ a) (subst σ F) :=
      escapeTerm (hF₁ hΔ hσ).red (ha hΔ hσ).term
    have hBeta := Step.beta wfσF wfσb wfσa
    rwa [← singleSubstLift b a, ← singleSubstLift G a] at hBeta
  rcases redSubstTermValid hRed hGa hba with ⟨hLam, hEq⟩
  exact ⟨hΓ, hGa, hLam, hba, hEq⟩

theorem fund_termEq_eta {eqrel : EqRelSet} {Γ : Context} {f g F G : Term}
    (ihF : FundTypeMotive eqrel Γ F)
    (ihf : FundTermMotive eqrel Γ f (.pi F G))
    (ihg : FundTermMotive eqrel Γ g (.pi F G))
    (ihfg : FundTermEqMotive eqrel (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G) :
    FundTermEqMotive eqrel Γ f g (.pi F G) := by
  rcases ihF with ⟨_, hF⟩
  rcases ihf with ⟨hΓ₁, hPiFG, hf⟩
  rcases ihg with ⟨_, hPiFG₁, hg⟩
  rcases ihfg with ⟨_, hG, _, _, hf0g0⟩
  have hg' : ValidTerm hPiFG g := irrelevanceValidTerm hPiFG₁ hPiFG hg
  have hPiFG'' : ValidType eqrel .one Γ (.pi F G) := piValid hF hG
  have hf'' : ValidTerm hPiFG'' f := irrelevanceValidTerm hPiFG hPiFG'' hf
  have hg'' : ValidTerm hPiFG'' g := irrelevanceValidTerm hPiFG₁ hPiFG'' hg
  have hfg : ValidTermEq hPiFG'' f g := etaEqValid hF hG hf'' hg'' hf0g0
  have hfg' : ValidTermEq hPiFG f g := irrelevanceValidEqTerm hPiFG'' hPiFG hfg
  exact ⟨hΓ₁, hPiFG, hf, hg', hfg'⟩

theorem fund_termEq_suc {eqrel : EqRelSet} {Γ : Context} {m n : Term}
    (ihmn : FundTermEqMotive eqrel Γ m n .nat) :
    FundTermEqMotive eqrel Γ (.succ m) (.succ n) .nat := by
  rcases ihmn with ⟨hΓ, hA, hm, hn, hmn⟩
  exact ⟨hΓ, hA, sucValid hA hm, sucValid hA hn,
    fun {Δ σ} hΔ hσ ↦ sucEqTerm (hA hΔ hσ).red (hmn hΔ hσ)⟩

theorem fund_termEq_natrec {eqrel : EqRelSet} {Γ : Context}
    {z z' s s' n n' F F' : Term}
    (ihFF' : FundTypeEqMotive eqrel (.nat :: Γ) F F')
    (ihzz' : FundTermEqMotive eqrel Γ z z' (subst0 F .zero))
    (ihss' : FundTermEqMotive eqrel Γ s s' (recStepType F))
    (ihnn' : FundTermEqMotive eqrel Γ n n' .nat) :
    FundTermEqMotive eqrel Γ (.natrec F z s n) (.natrec F' z' s' n') (subst0 F n) := by
  rcases ihFF' with ⟨_, hF, hF', hFF'⟩
  rcases ihzz' with ⟨_, hF0, hz, hz', hzz'⟩
  rcases ihss' with ⟨_, hFStep, hs, hs', hss'⟩
  rcases ihnn' with ⟨hΓ₃, hNat, hn, hn', hnn'⟩
  have h0 : ValidTerm hNat .zero :=
    irrelevanceValidTerm (natValid (l := .one)) hNat (zeroValid (l := .one))
  have hFn : ValidType eqrel .one Γ (subst0 F n) := substS hNat hF hn
  have hF0'' : ValidType eqrel .one Γ (subst0 F .zero) := substS hNat hF h0
  have hF'0 : ValidType eqrel .one Γ (subst0 F' .zero) := substS hNat hF' h0
  have hF'Step : ValidType eqrel .one Γ (recStepType F') := sucCase hNat hF'
  have hF'n' : ValidType eqrel .one Γ (subst0 F' n') := substS hNat hF' hn'
  have hNatRefl : ValidTypeEq hNat .nat := reflValid hNat
  have h0Refl : ValidTermEq hNat .zero .zero := reflValidTerm hNat h0
  have hF0F'0_raw : ValidTypeEq hF0'' (subst0 F' .zero) :=
    substSEq hNat hNat hNatRefl hF hF' hFF' h0 h0 h0Refl
  have hF0F'0 : ValidTypeEq hF0 (subst0 F' .zero) :=
    irrelevanceValidEq hF0'' hF0 hF0F'0_raw
  have hFStepEq_raw : ValidTypeEq (sucCase hNat hF) (recStepType F') :=
    sucCaseCong hNat hF hF' hFF'
  have hFStepEq : ValidTypeEq hFStep (recStepType F') :=
    irrelevanceValidEq (sucCase hNat hF) hFStep hFStepEq_raw
  have hFnF'n' : ValidTypeEq hFn (subst0 F' n') :=
    substSEq hNat hNat hNatRefl hF hF' hFF' hn hn' hnn'
  have hz'_conv : ValidTerm hF'0 z' := convValid hF0 hF'0 hF0F'0 hz'
  have hs'_conv : ValidTerm hF'Step s' := convValid hFStep hF'Step hFStepEq hs'
  exact ⟨hΓ₃, hFn,
    natrecValid hNat hF hF0 hFStep hFn hz hs hn,
    conv2Valid hFn hF'n' hFnF'n'
      (natrecValid hNat hF' hF'0 hF'Step hF'n' hz'_conv hs'_conv hn'),
    natrecCongValid hNat hF hF' hFF' hF0 hF'0 hF0F'0
      hFStep hF'Step hFStepEq hFn hz hz'_conv hzz' hs hs'_conv hss' hn hn' hnn'⟩

theorem fund_termEq_natrecZero {eqrel : EqRelSet} {Γ : Context} {z s F : Term}
    (ihF : FundTypeMotive eqrel (.nat :: Γ) F)
    (ihz : FundTermMotive eqrel Γ z (subst0 F .zero))
    (ihs : FundTermMotive eqrel Γ s (recStepType F)) :
    FundTermEqMotive eqrel Γ (.natrec F z s .zero) z (subst0 F .zero) := by
  rcases ihF with ⟨_, hF⟩
  rcases ihz with ⟨hΓ₁, hF0, hz⟩
  rcases ihs with ⟨_, hFStep, hs⟩
  have hNat : ValidType eqrel .one Γ .nat := natValid (l := .one)
  have hRed : ValidRedTerm eqrel Γ (.natrec F z s .zero) z (subst0 F .zero) := by
    intro Δ σ hΔ hσ
    have wfNat : TypeWf Δ .nat := escape (hNat hΔ hσ).red
    have wfF : TypeWf (.nat :: Δ) (subst (liftSubst σ) F) :=
      escape (hF (.cons hΔ wfNat) (liftSubstS hΔ hNat hσ)).red
    have wfz : HasType Δ (subst σ z) (subst0 (subst (liftSubst σ) F) .zero) := by
      have h := escapeTerm (hF0 hΔ hσ).red (hz hΔ hσ).term
      rwa [singleSubstLift F .zero] at h
    have wfs : HasType Δ (subst σ s) (recStepType (subst (liftSubst σ) F)) := by
      have h := escapeTerm (hFStep hΔ hσ).red (hs hΔ hσ).term
      rwa [natrecSucCase σ F] at h
    have hStep := Step.natrecZero wfF wfz wfs
    rw [singleSubstLift F .zero]
    exact hStep
  rcases redSubstTermValid hRed hF0 hz with ⟨hd, hr⟩
  exact ⟨hΓ₁, hF0, hd, hz, hr⟩

theorem fund_termEq_natrecSucc {eqrel : EqRelSet} {Γ : Context} {n z s F : Term}
    (ihn : FundTermMotive eqrel Γ n .nat)
    (ihF : FundTypeMotive eqrel (.nat :: Γ) F)
    (ihz : FundTermMotive eqrel Γ z (subst0 F .zero))
    (ihs : FundTermMotive eqrel Γ s (recStepType F)) :
    FundTermEqMotive eqrel Γ (.natrec F z s (.succ n))
      (.app (.app s n) (.natrec F z s n)) (subst0 F (.succ n)) := by
  rcases ihn with ⟨_, hNat, hn⟩
  rcases ihF with ⟨_, hF⟩
  rcases ihz with ⟨_, hF0, hz⟩
  rcases ihs with ⟨hΓ₃, hFStep, hs⟩
  have hSucn : ValidTerm hNat (.succ n) := sucValid hNat hn
  have hFsucn : ValidType eqrel .one Γ (subst0 F (.succ n)) := substS hNat hF hSucn
  have hFn : ValidType eqrel .one Γ (subst0 F n) := substS hNat hF hn
  have hNatrec_n : ValidTerm hFn (.natrec F z s n) :=
    natrecValid hNat hF hF0 hFStep hFn hz hs hn
  let t := Term.app (.app s n) (.natrec F z s n)
  let q := subst (liftSubst (sgSubst n)) (wk1 (substKeep F (.succ (.var 0))))
  have hStep_n : ValidType eqrel .one Γ (.pi (subst0 F n) q) :=
    substSPi hNat hFStep hn
  have hApp1 : ValidTerm hStep_n (.app s n) := appValid hNat hFStep hs hn
  have hApp2 : ValidTerm (substSPi hFn hStep_n hNatrec_n) t :=
    appValid hFn hStep_n hApp1 hNatrec_n
  have hy : ValidTerm hFsucn t :=
    irrelevanceValidTerm' (natrecIrrelevantSubst' F z s n)
      (substSPi hFn hStep_n hNatrec_n) hFsucn hApp2
  have hRed : ValidRedTerm eqrel Γ (.natrec F z s (.succ n)) t (subst0 F (.succ n)) := by
    intro Δ σ hΔ hσ
    have wfn : HasType Δ (subst σ n) .nat :=
      escapeTerm (hNat hΔ hσ).red (hn hΔ hσ).term
    have wfNat : TypeWf Δ .nat := escape (hNat hΔ hσ).red
    have wfF : TypeWf (.nat :: Δ) (subst (liftSubst σ) F) :=
      escape (hF (.cons hΔ wfNat) (liftSubstS hΔ hNat hσ)).red
    have wfz : HasType Δ (subst σ z) (subst0 (subst (liftSubst σ) F) .zero) := by
      have h := escapeTerm (hF0 hΔ hσ).red (hz hΔ hσ).term
      rwa [singleSubstLift F .zero] at h
    have wfs : HasType Δ (subst σ s) (recStepType (subst (liftSubst σ) F)) := by
      have h := escapeTerm (hFStep hΔ hσ).red (hs hΔ hσ).term
      rwa [natrecSucCase σ F] at h
    have hStep := Step.natrecSucc wfn wfF wfz wfs
    rw [singleSubstLift F (.succ n)]
    exact hStep
  rcases redSubstTermValid hRed hFsucn hy with ⟨hd, hr⟩
  exact ⟨hΓ₃, hFsucn, hd, hy, hr⟩

/-- Fundamental theorem for contexts (`valid`, Theorem 3.21). -/
theorem valid {eqrel : EqRelSet} {Γ : Context} (d : CtxWf Γ) : ValidCtx eqrel Γ :=
  @CtxWf.rec
    (fun Γ _ ↦ FundCtxMotive eqrel Γ)
    (fun Γ A _ ↦ FundTypeMotive eqrel Γ A)
    (fun Γ t A _ ↦ FundTermMotive eqrel Γ t A)
    (fun Γ A B _ ↦ FundTypeEqMotive eqrel Γ A B)
    (fun Γ t u A _ ↦ FundTermEqMotive eqrel Γ t u A)
    .nil
    (fun _ _ _ ihA ↦ .cons ihA.1 ihA.2)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid⟩)
    (fun _ _ ihF ihG ↦ ⟨ihF.1, piValid ihF.2 ihG.2⟩)
    (fun _ ihA ↦ fund_type_fromUniv ihA)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, natTermValid⟩)
    (fun _ _ ihF ihG ↦ fund_term_pi ihF ihG)
    (fun _ hm ihΓ ↦ ⟨ihΓ, fundamentalVar hm ihΓ⟩)
    (fun _ _ ihF iht ↦ fund_term_lam ihF iht)
    (fun _ _ ihg iha ↦ fund_term_app ihg iha)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid, zeroValid⟩)
    (fun _ ihn ↦ fund_term_suc ihn)
    (fun _ _ _ _ ihG ihz ihs ihn ↦ fund_term_natrec ihG ihz ihs ihn)
    (fun _ _ iht ihEq ↦ fund_term_conv iht ihEq)
    (fun _ ihEq ↦ fund_typeEq_fromUniv ihEq)
    (fun _ ihA ↦ fund_typeEq_refl ihA)
    (fun _ ihEq ↦ fund_typeEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_typeEq_trans ih₁ ih₂)
    (fun _ _ _ _ ihFH ihGE ↦ fund_typeEq_pi ihFH ihGE)
    (fun _ iht ↦ fund_termEq_refl iht)
    (fun _ ihEq ↦ fund_termEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_termEq_trans ih₁ ih₂)
    (fun _ _ ihEq ihAB ↦ fund_termEq_conv ihEq ihAB)
    (fun _ _ _ ihF ihFH ihGE ↦ fund_termEq_pi ihF ihFH ihGE)
    (fun _ _ ihfg ihab ↦ fund_termEq_app ihfg ihab)
    (fun _ _ _ _ ihb iha ↦ fund_termEq_beta ihb iha)
    (fun _ _ _ _ ihF ihf ihg ihfg ↦ fund_termEq_eta ihF ihf ihg ihfg)
    (fun _ ihmn ↦ fund_termEq_suc ihmn)
    (fun _ _ _ _ ihFF' ihzz' ihss' ihnn' ↦ fund_termEq_natrec ihFF' ihzz' ihss' ihnn')
    (fun _ _ _ ihF ihz ihs ↦ fund_termEq_natrecZero ihF ihz ihs)
    (fun _ _ _ _ ihn ihF ihz ihs ↦ fund_termEq_natrecSucc ihn ihF ihz ihs)
    Γ d

/-- Fundamental theorem for types (`fundamental`, Theorem 3.21). -/
theorem fundamental {eqrel : EqRelSet} {Γ : Context} {A : Term} (d : TypeWf Γ A) :
    ValidCtx eqrel Γ ∧ ValidType eqrel .one Γ A :=
  @TypeWf.rec
    (fun Γ _ ↦ FundCtxMotive eqrel Γ)
    (fun Γ A _ ↦ FundTypeMotive eqrel Γ A)
    (fun Γ t A _ ↦ FundTermMotive eqrel Γ t A)
    (fun Γ A B _ ↦ FundTypeEqMotive eqrel Γ A B)
    (fun Γ t u A _ ↦ FundTermEqMotive eqrel Γ t u A)
    .nil
    (fun _ _ _ ihA ↦ .cons ihA.1 ihA.2)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid⟩)
    (fun _ _ ihF ihG ↦ ⟨ihF.1, piValid ihF.2 ihG.2⟩)
    (fun _ ihA ↦ fund_type_fromUniv ihA)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, natTermValid⟩)
    (fun _ _ ihF ihG ↦ fund_term_pi ihF ihG)
    (fun _ hm ihΓ ↦ ⟨ihΓ, fundamentalVar hm ihΓ⟩)
    (fun _ _ ihF iht ↦ fund_term_lam ihF iht)
    (fun _ _ ihg iha ↦ fund_term_app ihg iha)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid, zeroValid⟩)
    (fun _ ihn ↦ fund_term_suc ihn)
    (fun _ _ _ _ ihG ihz ihs ihn ↦ fund_term_natrec ihG ihz ihs ihn)
    (fun _ _ iht ihEq ↦ fund_term_conv iht ihEq)
    (fun _ ihEq ↦ fund_typeEq_fromUniv ihEq)
    (fun _ ihA ↦ fund_typeEq_refl ihA)
    (fun _ ihEq ↦ fund_typeEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_typeEq_trans ih₁ ih₂)
    (fun _ _ _ _ ihFH ihGE ↦ fund_typeEq_pi ihFH ihGE)
    (fun _ iht ↦ fund_termEq_refl iht)
    (fun _ ihEq ↦ fund_termEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_termEq_trans ih₁ ih₂)
    (fun _ _ ihEq ihAB ↦ fund_termEq_conv ihEq ihAB)
    (fun _ _ _ ihF ihFH ihGE ↦ fund_termEq_pi ihF ihFH ihGE)
    (fun _ _ ihfg ihab ↦ fund_termEq_app ihfg ihab)
    (fun _ _ _ _ ihb iha ↦ fund_termEq_beta ihb iha)
    (fun _ _ _ _ ihF ihf ihg ihfg ↦ fund_termEq_eta ihF ihf ihg ihfg)
    (fun _ ihmn ↦ fund_termEq_suc ihmn)
    (fun _ _ _ _ ihFF' ihzz' ihss' ihnn' ↦ fund_termEq_natrec ihFF' ihzz' ihss' ihnn')
    (fun _ _ _ ihF ihz ihs ↦ fund_termEq_natrecZero ihF ihz ihs)
    (fun _ _ _ _ ihn ihF ihz ihs ↦ fund_termEq_natrecSucc ihn ihF ihz ihs)
    Γ A d

/-- Fundamental theorem for terms (`fundamentalTerm`, Theorem 3.21). -/
theorem fundamentalTerm {eqrel : EqRelSet} {Γ : Context} {t A : Term} (d : HasType Γ t A) :
    FundTermMotive eqrel Γ t A :=
  @HasType.rec
    (fun Γ _ ↦ FundCtxMotive eqrel Γ)
    (fun Γ A _ ↦ FundTypeMotive eqrel Γ A)
    (fun Γ t A _ ↦ FundTermMotive eqrel Γ t A)
    (fun Γ A B _ ↦ FundTypeEqMotive eqrel Γ A B)
    (fun Γ t u A _ ↦ FundTermEqMotive eqrel Γ t u A)
    .nil
    (fun _ _ _ ihA ↦ .cons ihA.1 ihA.2)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid⟩)
    (fun _ _ ihF ihG ↦ ⟨ihF.1, piValid ihF.2 ihG.2⟩)
    (fun _ ihA ↦ fund_type_fromUniv ihA)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, natTermValid⟩)
    (fun _ _ ihF ihG ↦ fund_term_pi ihF ihG)
    (fun _ hm ihΓ ↦ ⟨ihΓ, fundamentalVar hm ihΓ⟩)
    (fun _ _ ihF iht ↦ fund_term_lam ihF iht)
    (fun _ _ ihg iha ↦ fund_term_app ihg iha)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid, zeroValid⟩)
    (fun _ ihn ↦ fund_term_suc ihn)
    (fun _ _ _ _ ihG ihz ihs ihn ↦ fund_term_natrec ihG ihz ihs ihn)
    (fun _ _ iht ihEq ↦ fund_term_conv iht ihEq)
    (fun _ ihEq ↦ fund_typeEq_fromUniv ihEq)
    (fun _ ihA ↦ fund_typeEq_refl ihA)
    (fun _ ihEq ↦ fund_typeEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_typeEq_trans ih₁ ih₂)
    (fun _ _ _ _ ihFH ihGE ↦ fund_typeEq_pi ihFH ihGE)
    (fun _ iht ↦ fund_termEq_refl iht)
    (fun _ ihEq ↦ fund_termEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_termEq_trans ih₁ ih₂)
    (fun _ _ ihEq ihAB ↦ fund_termEq_conv ihEq ihAB)
    (fun _ _ _ ihF ihFH ihGE ↦ fund_termEq_pi ihF ihFH ihGE)
    (fun _ _ ihfg ihab ↦ fund_termEq_app ihfg ihab)
    (fun _ _ _ _ ihb iha ↦ fund_termEq_beta ihb iha)
    (fun _ _ _ _ ihF ihf ihg ihfg ↦ fund_termEq_eta ihF ihf ihg ihfg)
    (fun _ ihmn ↦ fund_termEq_suc ihmn)
    (fun _ _ _ _ ihFF' ihzz' ihss' ihnn' ↦ fund_termEq_natrec ihFF' ihzz' ihss' ihnn')
    (fun _ _ _ ihF ihz ihs ↦ fund_termEq_natrecZero ihF ihz ihs)
    (fun _ _ _ _ ihn ihF ihz ihs ↦ fund_termEq_natrecSucc ihn ihF ihz ihs)
    Γ t A d

/-- Fundamental theorem for type equality (`fundamentalEq`, Theorem 3.21). -/
theorem fundamentalEq {eqrel : EqRelSet} {Γ : Context} {A B : Term} (d : TypeEq Γ A B) :
    FundTypeEqMotive eqrel Γ A B :=
  @TypeEq.rec
    (fun Γ _ ↦ FundCtxMotive eqrel Γ)
    (fun Γ A _ ↦ FundTypeMotive eqrel Γ A)
    (fun Γ t A _ ↦ FundTermMotive eqrel Γ t A)
    (fun Γ A B _ ↦ FundTypeEqMotive eqrel Γ A B)
    (fun Γ t u A _ ↦ FundTermEqMotive eqrel Γ t u A)
    .nil
    (fun _ _ _ ihA ↦ .cons ihA.1 ihA.2)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid⟩)
    (fun _ _ ihF ihG ↦ ⟨ihF.1, piValid ihF.2 ihG.2⟩)
    (fun _ ihA ↦ fund_type_fromUniv ihA)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, natTermValid⟩)
    (fun _ _ ihF ihG ↦ fund_term_pi ihF ihG)
    (fun _ hm ihΓ ↦ ⟨ihΓ, fundamentalVar hm ihΓ⟩)
    (fun _ _ ihF iht ↦ fund_term_lam ihF iht)
    (fun _ _ ihg iha ↦ fund_term_app ihg iha)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid, zeroValid⟩)
    (fun _ ihn ↦ fund_term_suc ihn)
    (fun _ _ _ _ ihG ihz ihs ihn ↦ fund_term_natrec ihG ihz ihs ihn)
    (fun _ _ iht ihEq ↦ fund_term_conv iht ihEq)
    (fun _ ihEq ↦ fund_typeEq_fromUniv ihEq)
    (fun _ ihA ↦ fund_typeEq_refl ihA)
    (fun _ ihEq ↦ fund_typeEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_typeEq_trans ih₁ ih₂)
    (fun _ _ _ _ ihFH ihGE ↦ fund_typeEq_pi ihFH ihGE)
    (fun _ iht ↦ fund_termEq_refl iht)
    (fun _ ihEq ↦ fund_termEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_termEq_trans ih₁ ih₂)
    (fun _ _ ihEq ihAB ↦ fund_termEq_conv ihEq ihAB)
    (fun _ _ _ ihF ihFH ihGE ↦ fund_termEq_pi ihF ihFH ihGE)
    (fun _ _ ihfg ihab ↦ fund_termEq_app ihfg ihab)
    (fun _ _ _ _ ihb iha ↦ fund_termEq_beta ihb iha)
    (fun _ _ _ _ ihF ihf ihg ihfg ↦ fund_termEq_eta ihF ihf ihg ihfg)
    (fun _ ihmn ↦ fund_termEq_suc ihmn)
    (fun _ _ _ _ ihFF' ihzz' ihss' ihnn' ↦ fund_termEq_natrec ihFF' ihzz' ihss' ihnn')
    (fun _ _ _ ihF ihz ihs ↦ fund_termEq_natrecZero ihF ihz ihs)
    (fun _ _ _ _ ihn ihF ihz ihs ↦ fund_termEq_natrecSucc ihn ihF ihz ihs)
    Γ A B d

/-- Fundamental theorem for term equality (`fundamentalTermEq`, Theorem 3.21). -/
theorem fundamentalTermEq {eqrel : EqRelSet} {Γ : Context} {t u A : Term} (d : TermEq Γ t u A) :
    FundTermEqMotive eqrel Γ t u A :=
  @TermEq.rec
    (fun Γ _ ↦ FundCtxMotive eqrel Γ)
    (fun Γ A _ ↦ FundTypeMotive eqrel Γ A)
    (fun Γ t A _ ↦ FundTermMotive eqrel Γ t A)
    (fun Γ A B _ ↦ FundTypeEqMotive eqrel Γ A B)
    (fun Γ t u A _ ↦ FundTermEqMotive eqrel Γ t u A)
    .nil
    (fun _ _ _ ihA ↦ .cons ihA.1 ihA.2)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid⟩)
    (fun _ _ ihF ihG ↦ ⟨ihF.1, piValid ihF.2 ihG.2⟩)
    (fun _ ihA ↦ fund_type_fromUniv ihA)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, natTermValid⟩)
    (fun _ _ ihF ihG ↦ fund_term_pi ihF ihG)
    (fun _ hm ihΓ ↦ ⟨ihΓ, fundamentalVar hm ihΓ⟩)
    (fun _ _ ihF iht ↦ fund_term_lam ihF iht)
    (fun _ _ ihg iha ↦ fund_term_app ihg iha)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid, zeroValid⟩)
    (fun _ ihn ↦ fund_term_suc ihn)
    (fun _ _ _ _ ihG ihz ihs ihn ↦ fund_term_natrec ihG ihz ihs ihn)
    (fun _ _ iht ihEq ↦ fund_term_conv iht ihEq)
    (fun _ ihEq ↦ fund_typeEq_fromUniv ihEq)
    (fun _ ihA ↦ fund_typeEq_refl ihA)
    (fun _ ihEq ↦ fund_typeEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_typeEq_trans ih₁ ih₂)
    (fun _ _ _ _ ihFH ihGE ↦ fund_typeEq_pi ihFH ihGE)
    (fun _ iht ↦ fund_termEq_refl iht)
    (fun _ ihEq ↦ fund_termEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_termEq_trans ih₁ ih₂)
    (fun _ _ ihEq ihAB ↦ fund_termEq_conv ihEq ihAB)
    (fun _ _ _ ihF ihFH ihGE ↦ fund_termEq_pi ihF ihFH ihGE)
    (fun _ _ ihfg ihab ↦ fund_termEq_app ihfg ihab)
    (fun _ _ _ _ ihb iha ↦ fund_termEq_beta ihb iha)
    (fun _ _ _ _ ihF ihf ihg ihfg ↦ fund_termEq_eta ihF ihf ihg ihfg)
    (fun _ ihmn ↦ fund_termEq_suc ihmn)
    (fun _ _ _ _ ihFF' ihzz' ihss' ihnn' ↦ fund_termEq_natrec ihFF' ihzz' ihss' ihnn')
    (fun _ _ _ ihF ihz ihs ↦ fund_termEq_natrecZero ihF ihz ihs)
    (fun _ _ _ _ ihn ihF ihz ihs ↦ fund_termEq_natrecSucc ihn ihF ihz ihs)
    Γ t u A d

/-- Fundamental theorem for substitutions (`fundamentalSubst`, Theorem 3.23). -/
theorem fundamentalSubst {eqrel : EqRelSet} {Γ Δ : Context} {σ : Subst}
    (hΓ : CtxWf Γ) (hΔ : CtxWf Δ) (hσ : SubstWf Δ σ Γ) :
    ValidCtx eqrel Γ ∧ ValidSubst eqrel Δ σ Γ := by
  induction hσ with
  | nil => exact ⟨.nil, trivial⟩
  | @cons Γ A σ _ hHead ih =>
      cases hΓ with
      | cons wfΓ wfA =>
          rcases fundamental (eqrel := eqrel) wfA with ⟨vΓ, hA⟩
          rcases fundamentalTerm (eqrel := eqrel) hHead with ⟨vΔ, hA', ht⟩
          rcases ih wfΓ with ⟨_, hTail⟩
          have idA := (hA' (soundContext vΔ) (idSubstS vΔ)).red
          have idA' := (hA hΔ hTail).red
          have idt := (ht (soundContext vΔ) (idSubstS vΔ)).term
          exact ⟨.cons vΓ hA,
            ValidSubst.cons hTail idA'
              (irrelevanceTerm'' (subst_id _) (subst_id _) idA idA' idt)⟩

/-- Fundamental theorem for substitution equality (`fundamentalSubstEq`, Theorem 3.23). -/
theorem fundamentalSubstEq {eqrel : EqRelSet} {Γ Δ : Context} {σ σ' : Subst}
    (hΓ : CtxWf Γ) (hΔ : CtxWf Δ) (hσσ' : SubstEq Δ σ σ' Γ) :
    ValidCtx eqrel Γ ∧ ValidSubst eqrel Δ σ Γ ∧ ValidSubst eqrel Δ σ' Γ ∧
    ValidSubstEq eqrel Δ σ σ' Γ := by
  induction hσσ' with
  | nil => exact ⟨.nil, trivial, trivial, trivial⟩
  | @cons Γ A σ σ' _ hHeadEq ih =>
      cases hΓ with
      | cons wfΓ wfA =>
          rcases fundamental (eqrel := eqrel) wfA with ⟨vΓ, hA⟩
          rcases ih wfΓ with ⟨_, hTail, hTail', hTailEq⟩
          rcases fundamentalTermEq (eqrel := eqrel) hHeadEq with ⟨vΔ, hA', ht, ht', htt'⟩
          have idA := (hA' (soundContext vΔ) (idSubstS vΔ)).red
          have idA' := (hA hΔ hTail).red
          have idA'' := (hA hΔ hTail').red
          have idt := (ht (soundContext vΔ) (idSubstS vΔ)).term
          have idt' := (ht' (soundContext vΔ) (idSubstS vΔ)).term
          have idtt' := htt' (soundContext vΔ) (idSubstS vΔ)
          exact ⟨.cons vΓ hA,
            ValidSubst.cons hTail idA'
              (irrelevanceTerm'' (subst_id _) (subst_id _) idA idA' idt),
            ValidSubst.cons hTail' idA''
              (convTerm₁ idA' idA'' ((hA hΔ hTail).eq hTail' hTailEq)
                (irrelevanceTerm'' (subst_id _) (subst_id _) idA idA' idt')),
            ValidSubstEq.cons hTailEq idA'
              (irrelevanceEqTerm'' (subst_id _) (subst_id _) (subst_id _) idA idA' idtt')⟩

/-!
## Reducibility Corollaries (`Definition/LogicalRelation/Fundamental/Reducibility.agda`)
-/

/-- Well-formed types are reducible (`reducible`). -/
theorem reducible {eqrel : EqRelSet} {Γ : Context} {A : Term} (hA : TypeWf Γ A) :
    RedType eqrel .one Γ A := by
  rcases fundamental (eqrel := eqrel) hA with ⟨vΓ, vA⟩
  exact reducibleValid vΓ vA

/-- Well-formed type equality is reducible (`reducibleEq`). -/
theorem reducibleEq {eqrel : EqRelSet} {Γ : Context} {A B : Term} (hAB : TypeEq Γ A B) :
    ∃ (pA : RedType eqrel .one Γ A), RedType eqrel .one Γ B ∧ RedEq pA B := by
  rcases fundamentalEq (eqrel := eqrel) hAB with ⟨vΓ, vA, vB, vAB⟩
  exact ⟨reducibleValid vΓ vA, reducibleValid vΓ vB, reducibleValidEq vΓ vA vAB⟩

/-- Well-formed terms are reducible (`reducibleTerm`). -/
theorem reducibleTerm {eqrel : EqRelSet} {Γ : Context} {t A : Term} (ht : HasType Γ t A) :
    ∃ (pA : RedType eqrel .one Γ A), RedTerm pA t := by
  rcases fundamentalTerm (eqrel := eqrel) ht with ⟨vΓ, vA, vt⟩
  exact ⟨reducibleValid vΓ vA, reducibleValidTerm vΓ vA vt⟩

/-- Well-formed term equality is reducible (`reducibleEqTerm`). -/
theorem reducibleEqTerm {eqrel : EqRelSet} {Γ : Context} {t u A : Term} (htu : TermEq Γ t u A) :
    ∃ (pA : RedType eqrel .one Γ A), RedTermEq pA t u := by
  rcases fundamentalTermEq (eqrel := eqrel) htu with ⟨vΓ, vA, _, _, vtu⟩
  exact ⟨reducibleValid vΓ vA, reducibleValidEqTerm vΓ vA vtu⟩

end Abel2018

/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/Typed/Consequences/Syntactic.agda,
Definition/Typed/Consequences/Injectivity.agda,
Definition/Typed/Consequences/Equality.agda,
Definition/Typed/Consequences/Inequality.agda,
Definition/Typed/Consequences/Substitution.agda,
Definition/Typed/Consequences/Inversion.agda,
Definition/Typed/Consequences/InverseUniv.agda,
Definition/Typed/Consequences/NeTypeEq.agda,
Definition/Typed/Consequences/SucCong.agda,
Definition/Typed/Consequences/Reduction.agda,
Definition/Typed/Consequences/Canonicity.agda,
Definition/Typed/Consequences/Consistency.agda.
-/

namespace Abel2018

/-!
## Single-Sort Induction Helpers for `CtxWf`, `TypeWf`, and `TypeEq`
-/

theorem CtxWf.indOnly
    {motive : ∀ (Γ : Context), CtxWf Γ → Prop}
    (nil : motive [] .nil)
    (cons : ∀ {Γ A} (hΓ : CtxWf Γ) (hA : TypeWf Γ A),
      motive Γ hΓ → motive (A :: Γ) (.cons hΓ hA))
    {Γ : Context} (d : CtxWf Γ) : motive Γ d :=
  @CtxWf.rec
    motive
    (fun _ _ _ ↦ True)
    (fun _ _ _ _ ↦ True)
    (fun _ _ _ _ ↦ True)
    (fun _ _ _ _ _ ↦ True)
    nil
    (fun hΓ hA ihΓ _ ↦ cons hΓ hA ihΓ)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    Γ d

theorem TypeWf.indOnly
    {motive : ∀ (Γ : Context) (A : Term), TypeWf Γ A → Prop}
    (nat : ∀ {Γ} (hΓ : CtxWf Γ), motive Γ .nat (.nat hΓ))
    (univ : ∀ {Γ} (hΓ : CtxWf Γ), motive Γ .univ (.univ hΓ))
    (pi : ∀ {Γ F G} (hF : TypeWf Γ F) (hG : TypeWf (F :: Γ) G),
      motive Γ F hF → motive (F :: Γ) G hG → motive Γ (.pi F G) (.pi hF hG))
    (fromUniv : ∀ {Γ A} (hA : HasType Γ A .univ), motive Γ A (.fromUniv hA))
    {Γ : Context} {A : Term} (d : TypeWf Γ A) : motive Γ A d :=
  @TypeWf.rec
    (fun _ _ ↦ True)
    motive
    (fun _ _ _ _ ↦ True)
    (fun _ _ _ _ ↦ True)
    (fun _ _ _ _ _ ↦ True)
    trivial
    (fun _ _ _ _ ↦ trivial)
    (fun hΓ _ ↦ nat hΓ)
    (fun hΓ _ ↦ univ hΓ)
    (fun hF hG ihF ihG ↦ pi hF hG ihF ihG)
    (fun hA _ ↦ fromUniv hA)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    Γ A d

theorem TypeEq.indOnly
    {motive : ∀ (Γ : Context) (A B : Term), TypeEq Γ A B → Prop}
    (fromUniv : ∀ {Γ A B} (h : TermEq Γ A B .univ), motive Γ A B (.fromUniv h))
    (refl : ∀ {Γ A} (hA : TypeWf Γ A), motive Γ A A (.refl hA))
    (symm : ∀ {Γ A B} (h : TypeEq Γ A B), motive Γ A B h → motive Γ B A (.symm h))
    (trans : ∀ {Γ A B C} (h₁ : TypeEq Γ A B) (h₂ : TypeEq Γ B C),
      motive Γ A B h₁ → motive Γ B C h₂ → motive Γ A C (.trans h₁ h₂))
    (pi : ∀ {Γ F H G E} (hF : TypeWf Γ F) (hFH : TypeEq Γ F H) (hGE : TypeEq (F :: Γ) G E),
      motive Γ F H hFH → motive (F :: Γ) G E hGE →
      motive Γ (.pi F G) (.pi H E) (.pi hF hFH hGE))
    {Γ : Context} {A B : Term} (d : TypeEq Γ A B) : motive Γ A B d :=
  @TypeEq.rec
    (fun _ _ ↦ True)
    (fun _ _ _ ↦ True)
    (fun _ _ _ _ ↦ True)
    motive
    (fun _ _ _ _ _ ↦ True)
    trivial
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun h _ ↦ fromUniv h)
    (fun hA _ ↦ refl hA)
    (fun h ih ↦ symm h ih)
    (fun h₁ h₂ ih₁ ih₂ ↦ trans h₁ h₂ ih₁ ih₂)
    (fun hF hFH hGE _ ihFH ihGE ↦ pi hF hFH hGE ihFH ihGE)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    Γ A B d

/-!
## Syntactic Validity (`Definition/Typed/Consequences/Syntactic.agda`, Theorem 3.24)
-/

/-- Syntactic validity of type equality (`syntacticEq`). -/
theorem syntacticEq {Γ : Context} {A B : Term} (hAB : TypeEq Γ A B) :
    TypeWf Γ A ∧ TypeWf Γ B := by
  rcases reducibleEq (eqrel := synEqRel) hAB with ⟨pA, pB, _⟩
  exact ⟨escape pA, escape pB⟩

/-- Syntactic validity of terms: the type of a well-formed term is well-formed (`syntacticTerm`). -/
theorem syntacticTerm {Γ : Context} {t A : Term} (ht : HasType Γ t A) :
    TypeWf Γ A := by
  rcases reducibleTerm (eqrel := synEqRel) ht with ⟨pA, _⟩
  exact escape pA

/-- Syntactic validity of term equality (`syntacticEqTerm`). -/
theorem syntacticEqTerm {Γ : Context} {t u A : Term} (htu : TermEq Γ t u A) :
    TypeWf Γ A ∧ HasType Γ t A ∧ HasType Γ u A := by
  rcases fundamentalTermEq (eqrel := synEqRel) htu with ⟨vΓ, vA, vt, vu, _⟩
  exact ⟨escape (reducibleValid vΓ vA),
    escapeTerm (reducibleValid vΓ vA) (reducibleValidTerm vΓ vA vt),
    escapeTerm (reducibleValid vΓ vA) (reducibleValidTerm vΓ vA vu)⟩

/-- Syntactic validity of type reduction (`syntacticRed`). -/
theorem syntacticRed {Γ : Context} {A B : Term} (hAB : TypeStar Γ A B) :
    TypeWf Γ A ∧ TypeWf Γ B :=
  syntacticEq (subsetStar hAB)

/-- Syntactic validity of term reduction (`syntacticRedTerm`). -/
theorem syntacticRedTerm {Γ : Context} {t u A : Term} (htu : Star Γ t u A) :
    TypeWf Γ A ∧ HasType Γ t A ∧ HasType Γ u A :=
  syntacticEqTerm (subsetStarTerm htu)

/-- Syntactic validity of `Π`-types (`syntacticΠ`). -/
theorem syntacticPi {Γ : Context} {F G : Term} (hPi : TypeWf Γ (.pi F G)) :
    TypeWf Γ F ∧ TypeWf (F :: Γ) G := by
  have pPi := reducible (eqrel := synEqRel) hPi
  rcases elimPiAt' (.refl hPi) pPi with ⟨_, piA⟩
  exact ⟨piA.hF, piA.hG⟩

/-!
## Injectivity of `Π`-Types (`Definition/Typed/Consequences/Injectivity.agda`, Theorem 3.26)
-/

/-- Injectivity of `Π` for type equality (`injectivity`, Theorem 3.26). -/
theorem injectivity {Γ : Context} {F G H E : Term}
    (h : TypeEq Γ (.pi F G) (.pi H E)) :
    TypeEq Γ F H ∧ TypeEq (F :: Γ) G E := by
  rcases reducibleEq (eqrel := synEqRel) h with ⟨pFG, _pHE, hEq⟩
  rcases elimPiAt' (.refl (escape pFG)) pFG with ⟨l₀, piFG⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ rel ↦ LogRelAt synEqRel l₀ Δ (wk ρ F) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ a rel ↦ LogRelAt synEqRel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel
  have hAt : LogRelAt synEqRel l₀ Γ (.pi F G) (RedPiRel synEqRel Γ F G relF₀ relG₀) :=
    .pi piFG.D piFG.hF piFG.hG piFG.AeqA relF₀ relG₀
      piFG.redF (fun _ _ _ hr ↦ hr) piFG.redG (fun _ _ _ _ hs ↦ hs) piFG.Gext
  have pFG₀ : RedType synEqRel l₀ Γ (.pi F G) := ⟨_, hAt⟩
  have hPiEq : RedPiEq synEqRel Γ F G relF₀ relG₀ (.pi H E) :=
    (RedEq_of_LogRelAt hAt pFG₀).mp (irrelevanceEq pFG pFG₀ hEq)
  rcases hPiEq with ⟨F', G', D', _AeqB, FeqF', GeqG'⟩
  have hHE : Term.pi H E = Term.pi F' G' := whnfRedStar D' .pi
  injection hHE with hH hE
  subst hH hE
  have hΓ : CtxWf Γ := wfType piFG.hF
  have hFH_wk : TypeEq Γ (wk .id F) (wk .id H) :=
    escapeEq (piFG.redF .id hΓ) (FeqF' .id hΓ)
  rw [wk_id, wk_id] at hFH_wk
  have hρ₁ : WkCtx (.step .id) (F :: Γ) Γ := .step .id
  have hΔ₁ : CtxWf (F :: Γ) := .cons hΓ piFG.hF
  have hVar0 : HasType (F :: Γ) (.var 0) (wk (.step .id) F) := .var hΔ₁ .here
  have ha0 : RedTerm (piFG.redF hρ₁ hΔ₁) (.var 0) :=
    neuTerm (piFG.redF hρ₁ hΔ₁) (.var 0) hVar0 (.refl hVar0)
  have hGE_wk : TypeEq (F :: Γ)
      (subst0 (wk (.lift (.step .id)) G) (.var 0))
      (subst0 (wk (.lift (.step .id)) E) (.var 0)) :=
    escapeEq (piFG.redG hρ₁ hΔ₁ ha0) (GeqG' hρ₁ hΔ₁ ha0)
  rw [wkSingleSubstId, wkSingleSubstId] at hGE_wk
  exact ⟨hFH_wk, hGE_wk⟩

/-!
## Equality Characterization (`Definition/Typed/Consequences/Equality.agda`, Theorem 3.33)
-/

/-- The only type equal to `U` is `U` (`U≡A`). -/
theorem U_eq_A {Γ : Context} {A : Term} (h : TypeEq Γ .univ A) : A = .univ := by
  rcases reducibleEq (eqrel := synEqRel) h with ⟨pU, _pA, hEq⟩
  have hU := elimU pU
  rcases hU with ⟨l', lt, wf⟩
  have hAt : LogRelAt synEqRel .one Γ .univ
      (RedURel synEqRel (logRelRec synEqRel .one l' lt) Γ) :=
    .U ⟨lt, wf⟩
  exact (RedEq_of_LogRelAt hAt pU).mp hEq

/-- Any type equal to `U` reduces to `U`. -/
theorem U_eq_A_star {Γ : Context} {A : Term} (h : TypeEq Γ .univ A) :
    TypeStar Γ A .univ := by
  have hA := U_eq_A h
  subst hA
  exact .refl (syntacticEq h).1

/-- Any type equal to `ℕ` reduces to `ℕ` (`ℕ≡A`). -/
theorem nat_eq_A {Γ : Context} {A : Term} (h : TypeEq Γ .nat A) :
    TypeStar Γ A .nat := by
  rcases reducibleEq (eqrel := synEqRel) h with ⟨pNat, _pA, hEq⟩
  have D := elimNat pNat
  have hAt : LogRelAt synEqRel .one Γ .nat (RedNatRel synEqRel Γ) := .nat D
  exact (RedEq_of_LogRelAt hAt pNat).mp hEq

/-- Any type equal to a neutral type reduces to a neutral type (`ne≡A`). -/
theorem ne_eq_A {Γ : Context} {K A : Term} (neK : Neutral K) (h : TypeEq Γ K A) :
    ∃ M, TypeStarWf Γ A M ∧ Neutral M := by
  rcases reducibleEq (eqrel := synEqRel) h with ⟨pK, _pA, hEq⟩
  have neA := elimNeAt' (.refl (escape pK)) neK pK
  have hAt : LogRelAt synEqRel .one Γ K (RedNeRel synEqRel Γ K) := .ne neA
  rcases (RedEq_of_LogRelAt hAt pK).mp hEq with ⟨M, D', neM, _⟩
  exact ⟨M, D', neM⟩

/-- Any type equal to a `Π`-type reduces to a `Π`-type (`Π≡A`). -/
theorem pi_eq_A {Γ : Context} {F G A : Term} (h : TypeEq Γ (.pi F G) A) :
    ∃ H E, TypeStar Γ A (.pi H E) := by
  rcases reducibleEq (eqrel := synEqRel) h with ⟨pFG, _pA, hEq⟩
  rcases elimPiAt' (.refl (escape pFG)) pFG with ⟨l₀, piFG⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ rel ↦ LogRelAt synEqRel l₀ Δ (wk ρ F) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ a rel ↦ LogRelAt synEqRel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel
  have hAt : LogRelAt synEqRel l₀ Γ (.pi F G) (RedPiRel synEqRel Γ F G relF₀ relG₀) :=
    .pi piFG.D piFG.hF piFG.hG piFG.AeqA relF₀ relG₀
      piFG.redF (fun _ _ _ hr ↦ hr) piFG.redG (fun _ _ _ _ hs ↦ hs) piFG.Gext
  have pFG₀ : RedType synEqRel l₀ Γ (.pi F G) := ⟨_, hAt⟩
  rcases (RedEq_of_LogRelAt hAt pFG₀).mp (irrelevanceEq pFG pFG₀ hEq) with ⟨H, E, D', _, _, _⟩
  exact ⟨H, E, D'⟩

/-!
## Inequality of Type Constructors (`Definition/Typed/Consequences/Inequality.agda`, Theorem 3.25)
-/

/-- `U` is not judgmentally equal to `ℕ` (`U≢ℕ`). -/
theorem U_ne_nat {Γ : Context} : ¬ TypeEq Γ .univ .nat := by
  intro h
  have hEq := U_eq_A h
  cases hEq

/-- `U` is not judgmentally equal to any type reducing to `ℕ` (`U≢ℕ-red`). -/
theorem U_ne_nat_red {Γ : Context} {A : Term} (hU : TypeEq Γ .univ A) (D : TypeStar Γ A .nat) :
    False :=
  U_ne_nat (.trans hU (subsetStar D))

/-- `U` is not judgmentally equal to any `Π`-type (`U≢Π`). -/
theorem U_ne_pi {Γ : Context} {F G : Term} : ¬ TypeEq Γ .univ (.pi F G) := by
  intro h
  have hEq := U_eq_A h
  cases hEq

/-- `U` is not judgmentally equal to any type reducing to a `Π`-type (`U≢Π-red`). -/
theorem U_ne_pi_red {Γ : Context} {A F G : Term}
    (hU : TypeEq Γ .univ A) (D : TypeStar Γ A (.pi F G)) : False :=
  U_ne_pi (.trans hU (subsetStar D))

/-- `U` is not judgmentally equal to any neutral type (`U≢ne`). -/
theorem U_ne_ne {Γ : Context} {K : Term} (neK : Neutral K) : ¬ TypeEq Γ .univ K := by
  intro h
  have hEq := U_eq_A h
  subst hEq
  cases neK

/-- `U` is not judgmentally equal to any type reducing to a neutral type (`U≢ne-red`). -/
theorem U_ne_ne_red {Γ : Context} {A K : Term} (neK : Neutral K)
    (hU : TypeEq Γ .univ A) (D : TypeStar Γ A K) : False :=
  U_ne_ne neK (.trans hU (subsetStar D))

/-- `ℕ` is not judgmentally equal to any `Π`-type (`ℕ≢Π`). -/
theorem nat_ne_pi {Γ : Context} {F G : Term} : ¬ TypeEq Γ .nat (.pi F G) := by
  intro h
  have hRed := nat_eq_A h
  have hEq := whnfRedStar hRed .pi
  cases hEq

/-- Any type reducing to `ℕ` is not judgmentally equal to any type reducing to `Π` (`ℕ≢Π-red`). -/
theorem nat_ne_pi_red {Γ : Context} {A B F G : Term}
    (hAB : TypeEq Γ A B) (DA : TypeStar Γ A .nat) (DB : TypeStar Γ B (.pi F G)) : False :=
  nat_ne_pi (.trans (.symm (subsetStar DA)) (.trans hAB (subsetStar DB)))

/-- `ℕ` is not judgmentally equal to any neutral type (`ℕ≢ne`). -/
theorem nat_ne_ne {Γ : Context} {K : Term} (neK : Neutral K) : ¬ TypeEq Γ .nat K := by
  intro h
  have hRed := nat_eq_A h
  have hEq := whnfRedStar hRed (.neutral neK)
  subst hEq
  cases neK

/-- Any type reducing to `ℕ` is not judgmentally equal to any type reducing to a neutral (`ℕ≢ne-red`). -/
theorem nat_ne_ne_red {Γ : Context} {A B K : Term} (neK : Neutral K)
    (hAB : TypeEq Γ A B) (DA : TypeStar Γ A .nat) (DB : TypeStar Γ B K) : False :=
  nat_ne_ne neK (.trans (.symm (subsetStar DA)) (.trans hAB (subsetStar DB)))

/-- A `Π`-type is not judgmentally equal to any neutral type (`Π≢ne`). -/
theorem pi_ne_ne {Γ : Context} {F G K : Term} (neK : Neutral K) : ¬ TypeEq Γ (.pi F G) K := by
  intro h
  rcases pi_eq_A h with ⟨H, E, hRed⟩
  have hEq := whnfRedStar hRed (.neutral neK)
  subst hEq
  cases neK

/-- Any type reducing to `Π` is not judgmentally equal to any type reducing to a neutral (`Π≢ne-red`). -/
theorem pi_ne_ne_red {Γ : Context} {A B F G K : Term} (neK : Neutral K)
    (hAB : TypeEq Γ A B) (DA : TypeStar Γ A (.pi F G)) (DB : TypeStar Γ B K) : False :=
  pi_ne_ne neK (.trans (.symm (subsetStar DA)) (.trans hAB (subsetStar DB)))

/-!
## Syntactic Substitution Consequences (`Definition/Typed/Consequences/Substitution.agda`, Theorem 3.32)
-/

/-- Syntactic substitution of well-formed types (`substitution`, Theorem 3.32). -/
theorem substitution {Γ Δ : Context} {A : Term} {σ : Subst}
    (hA : TypeWf Γ A) (hσ : SubstWf Δ σ Γ) (hΔ : CtxWf Δ) :
    TypeWf Δ (subst σ A) := by
  rcases fundamental (eqrel := synEqRel) hA with ⟨vΓ, vA⟩
  rcases fundamentalSubst (eqrel := synEqRel) (soundContext vΓ) hΔ hσ with ⟨_, vσ⟩
  exact escape (vA hΔ vσ).red

/-- Syntactic substitution of type equality (`substitutionEq`, Theorem 3.32). -/
theorem substitutionEq {Γ Δ : Context} {A B : Term} {σ σ' : Subst}
    (hAB : TypeEq Γ A B) (hσσ' : SubstEq Δ σ σ' Γ) (hΔ : CtxWf Δ) :
    TypeEq Δ (subst σ A) (subst σ' B) := by
  rcases fundamentalEq (eqrel := synEqRel) hAB with ⟨vΓ, vA, vB, vAB⟩
  rcases fundamentalSubstEq (eqrel := synEqRel) (soundContext vΓ) hΔ hσσ' with ⟨_, vσ, vσ', vσσ'⟩
  exact escapeEq (vA hΔ vσ).red
    (transEq (vA hΔ vσ).red (vA hΔ vσ').red (vB hΔ vσ').red
      ((vA hΔ vσ).eq vσ' vσσ')
      (vAB hΔ vσ'))

/-- Syntactic substitution of well-formed terms (`substitutionTerm`, Theorem 3.32). -/
theorem substitutionTerm {Γ Δ : Context} {t A : Term} {σ : Subst}
    (ht : HasType Γ t A) (hσ : SubstWf Δ σ Γ) (hΔ : CtxWf Δ) :
    HasType Δ (subst σ t) (subst σ A) := by
  rcases fundamentalTerm (eqrel := synEqRel) ht with ⟨vΓ, vA, vt⟩
  rcases fundamentalSubst (eqrel := synEqRel) (soundContext vΓ) hΔ hσ with ⟨_, vσ⟩
  exact escapeTerm (vA hΔ vσ).red (vt hΔ vσ).term

/-- Syntactic substitution of term equality (`substitutionEqTerm`, Theorem 3.32). -/
theorem substitutionEqTerm {Γ Δ : Context} {t u A : Term} {σ σ' : Subst}
    (htu : TermEq Γ t u A) (hσσ' : SubstEq Δ σ σ' Γ) (hΔ : CtxWf Δ) :
    TermEq Δ (subst σ t) (subst σ' u) (subst σ A) := by
  rcases fundamentalTermEq (eqrel := synEqRel) htu with ⟨vΓ, vA, _vt, vu, vtu⟩
  rcases fundamentalSubstEq (eqrel := synEqRel) (soundContext vΓ) hΔ hσσ' with ⟨_, vσ, vσ', vσσ'⟩
  have pσA := (vA hΔ vσ).red
  exact escapeTermEq pσA
    (transEqTerm pσA (vtu hΔ vσ) ((vu hΔ vσ).eq vσ' vσσ'))

/-- Reflexivity of well-formed substitution (`substRefl`). -/
theorem substRefl {Γ Δ : Context} {σ : Subst} (hσ : SubstWf Δ σ Γ) :
    SubstEq Δ σ σ Γ := by
  induction hσ with
  | nil => exact .nil
  | cons _ hHead ih => exact .cons ih (.refl hHead)

/-- Weakening of well-formed substitution (`wkSubst′`). -/
theorem wkSubst' {ρ : Wk} {σ : Subst} {Γ Δ Δ' : Context}
    (hΓ : CtxWf Γ) (_hΔ : CtxWf Δ) (hΔ' : CtxWf Δ')
    (hρ : WkCtx ρ Δ' Δ) (hσ : SubstWf Δ σ Γ) :
    SubstWf Δ' (wkSubst ρ σ) Γ := by
  induction hσ with
  | nil => exact .nil
  | @cons Γ A σ _ hHead ih =>
      cases hΓ with
      | cons wfΓ _ =>
          refine .cons (ih wfΓ) ?_
          have hHead' : HasType Δ' (wk ρ (headSubst σ)) (wk ρ (subst (tailSubst σ) A)) :=
            wkHasType hρ hΔ' hHead
          rwa [wk_subst] at hHead'

/-- Weakening of well-formed substitution by one variable (`wk1Subst′`). -/
theorem wk1Subst' {F : Term} {σ : Subst} {Γ Δ : Context}
    (hΓ : CtxWf Γ) (hΔ : CtxWf Δ) (hF : TypeWf Δ F) (hσ : SubstWf Δ σ Γ) :
    SubstWf (F :: Δ) (wk1Subst σ) Γ :=
  wkSubst' hΓ hΔ (.cons hΔ hF) (.step .id) hσ

/-- Lifting of well-formed substitution (`liftSubst′`). -/
theorem liftSubst' {F : Term} {σ : Subst} {Γ Δ : Context}
    (hΓ : CtxWf Γ) (hΔ : CtxWf Δ) (hF : TypeWf Γ F) (hσ : SubstWf Δ σ Γ) :
    SubstWf (subst σ F :: Δ) (liftSubst σ) (F :: Γ) := by
  have wfσF : TypeWf Δ (subst σ F) := substitution hF hσ hΔ
  have wfΔF : CtxWf (subst σ F :: Δ) := .cons hΔ wfσF
  refine .cons (wkSubst' hΓ hΔ wfΔF (.step .id) hσ) ?_
  have hVar0 : HasType (subst σ F :: Δ) (.var 0) (wk (.step .id) (subst σ F)) :=
    .var wfΔF .here
  change HasType (subst σ F :: Δ) (.var 0) (subst (wkSubst (.step .id) σ) F)
  rwa [← wk_subst]

/-- Well-formed identity substitution (`idSubst′`). -/
theorem idSubst' {Γ : Context} (hΓ : CtxWf Γ) : SubstWf Γ idSubst Γ := by
  induction hΓ using CtxWf.indOnly with
  | nil => exact .nil
  | @cons Γ A wfΓ wfA ih =>
      refine .cons (wk1Subst' wfΓ wfΓ wfA ih) ?_
      have hVar0 : HasType (A :: Γ) (.var 0) (wk1 A) := .var (.cons wfΓ wfA) .here
      rwa [wk1_tailId] at hVar0

/-- Well-formed substitution composition (`substComp′`). -/
theorem substComp' {σ σ' : Subst} {Γ Δ Δ' : Context}
    (hΓ : CtxWf Γ) (_hΔ : CtxWf Δ) (hΔ' : CtxWf Δ')
    (hσ : SubstWf Δ' σ Δ) (hσ' : SubstWf Δ σ' Γ) :
    SubstWf Δ' (compSubst σ σ') Γ := by
  induction hσ' with
  | nil => exact .nil
  | @cons Γ A σ' _ hHead ih =>
      cases hΓ with
      | cons wfΓ _ =>
          refine .cons (ih wfΓ) ?_
          have hHead' : HasType Δ' (subst σ (headSubst σ')) (subst σ (subst (tailSubst σ') A)) :=
            substitutionTerm hHead hσ hΔ'
          rwa [substCompEq] at hHead'

/-- Well-formed singleton substitution (`singleSubst`). -/
theorem singleSubst {Γ : Context} {A t : Term} (ht : HasType Γ t A) :
    SubstWf Γ (sgSubst t) (A :: Γ) := by
  have hΓ := wfTerm ht
  refine .cons (idSubst' hΓ) ?_
  change HasType Γ t (subst idSubst A)
  rwa [subst_id]

/-- Well-formed singleton substitution equality (`singleSubstEq`). -/
theorem singleSubstEq {Γ : Context} {A t u : Term} (htu : TermEq Γ t u A) :
    SubstEq Γ (sgSubst t) (sgSubst u) (A :: Γ) := by
  have hΓ := wfTermEq htu
  refine .cons (substRefl (idSubst' hΓ)) ?_
  change TermEq Γ t u (subst idSubst A)
  rwa [subst_id]

/-- Well-formed lifted singleton substitution (`singleSubst↑`). -/
theorem singleSubstUp {Γ : Context} {A t : Term} (ht : HasType (A :: Γ) t (wk1 A)) :
    SubstWf (A :: Γ) (consSubst (wk1Subst idSubst) t) (A :: Γ) := by
  cases wfTerm ht with
  | cons wfΓ wfA =>
      refine .cons (wk1Subst' wfΓ wfΓ wfA (idSubst' wfΓ)) ?_
      change HasType (A :: Γ) t (subst (wkSubst (.step .id) idSubst) A)
      rw [← wk_subst, subst_id]
      exact ht

/-- Well-formed lifted singleton substitution equality (`singleSubst↑Eq`). -/
theorem singleSubstUpEq {Γ : Context} {A t u : Term}
    (htu : TermEq (A :: Γ) t u (wk1 A)) :
    SubstEq (A :: Γ) (consSubst (wk1Subst idSubst) t) (consSubst (wk1Subst idSubst) u) (A :: Γ) := by
  cases wfTermEq htu with
  | cons wfΓ wfA =>
      refine .cons (substRefl (wk1Subst' wfΓ wfΓ wfA (idSubst' wfΓ))) ?_
      change TermEq (A :: Γ) t u (subst (wkSubst (.step .id) idSubst) A)
      rw [← wk_subst, subst_id]
      exact htu

/-- Single variable substitution in types (`substType`). -/
theorem substType {Γ : Context} {F G t : Term}
    (hG : TypeWf (F :: Γ) G) (ht : HasType Γ t F) :
    TypeWf Γ (subst0 G t) :=
  substitution hG (singleSubst ht) (wfTerm ht)

/-- Single variable substitution in type equality (`substTypeEq`). -/
theorem substTypeEq {Γ : Context} {F G E t u : Term}
    (hGE : TypeEq (F :: Γ) G E) (htu : TermEq Γ t u F) :
    TypeEq Γ (subst0 G t) (subst0 E u) :=
  substitutionEq hGE (singleSubstEq htu) (wfTermEq htu)

/-- Single variable substitution in terms (`substTerm`). -/
theorem substTerm {Γ : Context} {F G t f : Term}
    (hf : HasType (F :: Γ) f G) (ht : HasType Γ t F) :
    HasType Γ (subst0 f t) (subst0 G t) :=
  substitutionTerm hf (singleSubst ht) (wfTerm ht)

/-- Single variable substitution in the codomain of a well-formed `Π`-type (`substTypeΠ`). -/
theorem substTypePi {Γ : Context} {F G t : Term}
    (hPi : TypeWf Γ (.pi F G)) (ht : HasType Γ t F) :
    TypeWf Γ (subst0 G t) :=
  substType (syntacticPi hPi).2 ht

/-- Lifted single variable substitution in types (`subst↑Type`). -/
theorem substUpType {Γ : Context} {F G t : Term}
    (hG : TypeWf (F :: Γ) G) (ht : HasType (F :: Γ) t (wk1 F)) :
    TypeWf (F :: Γ) (substKeep G t) :=
  substitution hG (singleSubstUp ht) (wfTerm ht)

/-- Lifted single variable substitution in type equality (`subst↑TypeEq`). -/
theorem substUpTypeEq {Γ : Context} {F G E t u : Term}
    (hGE : TypeEq (F :: Γ) G E) (htu : TermEq (F :: Γ) t u (wk1 F)) :
    TypeEq (F :: Γ) (substKeep G t) (substKeep E u) :=
  substitutionEq hGE (singleSubstUpEq htu) (wfTermEq htu)

/-!
## Inversion of Typing (`Definition/Typed/Consequences/Inversion.agda`)
-/

/-- Inversion of typing for variables. -/
theorem inversion_var {Γ : Context} {x : Nat} {A : Term}
    (h : HasType Γ (.var x) A) :
    ∃ B, Member x B Γ ∧ TypeEq Γ A B := by
  generalize ht : Term.var x = t at h
  induction h using HasType.indOnly with
  | var hΓ hx =>
      injection ht with hx'
      subst hx'
      exact ⟨_, hx, .refl (syntacticTerm (.var hΓ hx))⟩
  | conv _ hAB ih =>
      rcases ih ht with ⟨B, hx, hEq⟩
      exact ⟨B, hx, .trans (.symm hAB) hEq⟩
  | _ => cases ht

/-- Inversion of typing for `ℕ` (`inversion-ℕ`). -/
theorem inversion_nat {Γ : Context} {A : Term}
    (h : HasType Γ .nat A) : TypeEq Γ A .univ := by
  generalize ht : Term.nat = t at h
  induction h using HasType.indOnly with
  | nat hΓ => exact .refl (.univ hΓ)
  | conv _ hAB ih => exact .trans (.symm hAB) (ih ht)
  | _ => cases ht

/-- Inversion of typing for `Π F ▹ G` (`inversion-Π`). -/
theorem inversion_pi {Γ : Context} {F G A : Term}
    (h : HasType Γ (.pi F G) A) :
    HasType Γ F .univ ∧ HasType (F :: Γ) G .univ ∧ TypeEq Γ A .univ := by
  generalize ht : Term.pi F G = t at h
  induction h using HasType.indOnly with
  | pi hF hG =>
      injection ht with hF' hG'
      subst hF' hG'
      exact ⟨hF, hG, .refl (.univ (wfTerm hF))⟩
  | conv _ hAB ih =>
      rcases ih ht with ⟨hF, hG, hEq⟩
      exact ⟨hF, hG, .trans (.symm hAB) hEq⟩
  | _ => cases ht

/-- Inversion of typing for `zero` (`inversion-zero`). -/
theorem inversion_zero {Γ : Context} {A : Term}
    (h : HasType Γ .zero A) : TypeEq Γ A .nat := by
  generalize ht : Term.zero = t at h
  induction h using HasType.indOnly with
  | zero hΓ => exact .refl (.nat hΓ)
  | conv _ hAB ih => exact .trans (.symm hAB) (ih ht)
  | _ => cases ht

/-- Inversion of typing for `suc n` (`inversion-suc`). -/
theorem inversion_suc {Γ : Context} {n A : Term}
    (h : HasType Γ (.succ n) A) :
    HasType Γ n .nat ∧ TypeEq Γ A .nat := by
  generalize ht : Term.succ n = t at h
  induction h using HasType.indOnly with
  | succ hn =>
      injection ht with hn'
      subst hn'
      exact ⟨hn, .refl (.nat (wfTerm hn))⟩
  | conv _ hAB ih =>
      rcases ih ht with ⟨hn, hEq⟩
      exact ⟨hn, .trans (.symm hAB) hEq⟩
  | _ => cases ht

/-- Inversion of typing for `natrec F z s n` (`inversion-natrec`). -/
theorem inversion_natrec {Γ : Context} {F z s n A : Term}
    (h : HasType Γ (.natrec F z s n) A) :
    TypeWf (.nat :: Γ) F ∧ HasType Γ z (subst0 F .zero) ∧
    HasType Γ s (recStepType F) ∧ HasType Γ n .nat ∧
    TypeEq Γ A (subst0 F n) := by
  generalize ht : Term.natrec F z s n = t at h
  induction h using HasType.indOnly with
  | natrec hF hz hs hn =>
      injection ht with hF' hz' hs' hn'
      subst hF' hz' hs' hn'
      exact ⟨hF, hz, hs, hn, .refl (substType hF hn)⟩
  | conv _ hAB ih =>
      rcases ih ht with ⟨hF, hz, hs, hn, hEq⟩
      exact ⟨hF, hz, hs, hn, .trans (.symm hAB) hEq⟩
  | _ => cases ht

/-- Inversion of typing for `f ∘ a` (`inversion-∘`). -/
theorem inversion_app {Γ : Context} {f a A : Term}
    (h : HasType Γ (.app f a) A) :
    ∃ F G, HasType Γ f (.pi F G) ∧ HasType Γ a F ∧ TypeEq Γ A (subst0 G a) := by
  generalize ht : Term.app f a = t at h
  induction h using HasType.indOnly with
  | app hf ha =>
      injection ht with hf' ha'
      subst hf' ha'
      exact ⟨_, _, hf, ha, .refl (substTypePi (syntacticTerm hf) ha)⟩
  | conv _ hAB ih =>
      rcases ih ht with ⟨F, G, hf, ha, hEq⟩
      exact ⟨F, G, hf, ha, .trans (.symm hAB) hEq⟩
  | _ => cases ht

/-- Inversion of typing for `lam t` (`inversion-lam`). -/
theorem inversion_lam {Γ : Context} {t A : Term}
    (h : HasType Γ (.lam t) A) :
    ∃ F G, TypeWf Γ F ∧ HasType (F :: Γ) t G ∧ TypeEq Γ A (.pi F G) := by
  generalize ht : Term.lam t = u at h
  induction h using HasType.indOnly with
  | lam hF htBody =>
      injection ht with ht'
      subst ht'
      exact ⟨_, _, hF, htBody, .refl (.pi hF (syntacticTerm htBody))⟩
  | conv _ hAB ih =>
      rcases ih ht with ⟨F, G, hF, htBody, hEq⟩
      exact ⟨F, G, hF, htBody, .trans (.symm hAB) hEq⟩
  | _ => cases ht

/-!
## Universe Inversion (`Definition/Typed/Consequences/InverseUniv.agda`)
-/

/-- Predicate characterizing terms that contain `U` (`UFull`). -/
inductive UFull : Term → Prop where
  | univ : UFull .univ
  | pi1 {F G : Term} : UFull F → UFull (.pi F G)
  | pi2 {F G : Term} : UFull G → UFull (.pi F G)

/-- Well-typed terms cannot contain `U` (`noU`). -/
theorem noU {Γ : Context} {t A : Term} (ht : HasType Γ t A) : ¬ UFull t := by
  induction ht using HasType.indOnly with
  | pi _ _ ihF ihG =>
      intro hU
      cases hU with
      | pi1 uF => exact ihF uF
      | pi2 uG => exact ihG uG
  | conv _ _ ih => exact ih
  | _ => intro hU; cases hU

/-- Neutral terms cannot contain `U` (`noUNe`). -/
theorem noUNe {A : Term} (neA : Neutral A) : ¬ UFull A := by
  intro hU
  cases neA <;> cases hU

/-- If a well-formed type `A` does not contain `U`, then `A` is a term of `U` (`inverseUniv`). -/
theorem inverseUniv {Γ : Context} {A : Term}
    (hNotU : ¬ UFull A) (hA : TypeWf Γ A) : HasType Γ A .univ := by
  induction hA using TypeWf.indOnly with
  | nat hΓ => exact .nat hΓ
  | univ _ => exact False.elim (hNotU .univ)
  | pi _ _ ihF ihG =>
      exact .pi (ihF (fun uF ↦ hNotU (.pi1 uF))) (ihG (fun uG ↦ hNotU (.pi2 uG)))
  | fromUniv hA => exact hA

/-- If a neutral term `A` is a well-formed type, then `A` is a term of `U` (`inverseUnivNe`). -/
theorem inverseUnivNe {Γ : Context} {A : Term}
    (neA : Neutral A) (hA : TypeWf Γ A) : HasType Γ A .univ :=
  inverseUniv (noUNe neA) hA

/-- Helper for `inverseUnivEq`: if at least one endpoint of `Γ ⊢ A ≡ B` does not contain `U`,
then `Γ ⊢ A ≡ B ∷ U` (`inverseUnivEq′`). -/
theorem inverseUnivEq' {Γ : Context} {A B : Term}
    (hNotU : (¬ UFull A) ∨ (¬ UFull B)) (hAB : TypeEq Γ A B) :
    TermEq Γ A B .univ := by
  induction hAB using TypeEq.indOnly with
  | fromUniv h => exact h
  | refl hA =>
      rcases hNotU with hNotA | hNotA
      · exact .refl (inverseUniv hNotA hA)
      · exact .refl (inverseUniv hNotA hA)
  | symm _ ih =>
      exact .symm (ih hNotU.symm)
  | trans _ _ ih₁ ih₂ =>
      rcases hNotU with hNotA | hNotC
      · have w := ih₁ (.inl hNotA)
        have ⟨_, _, hB⟩ := syntacticEqTerm w
        exact .trans w (ih₂ (.inl (noU hB)))
      · have w := ih₂ (.inr hNotC)
        have ⟨_, hB, _⟩ := syntacticEqTerm w
        exact .trans (ih₁ (.inr (noU hB))) w
  | pi hF _ _ ihF ihG =>
      rcases hNotU with hNotFG | hNotHE
      · exact .pi hF
          (ihF (.inl (fun uF ↦ hNotFG (.pi1 uF))))
          (ihG (.inl (fun uG ↦ hNotFG (.pi2 uG))))
      · exact .pi hF
          (ihF (.inr (fun uH ↦ hNotHE (.pi1 uH))))
          (ihG (.inr (fun uE ↦ hNotHE (.pi2 uE))))

/-- If `Γ ⊢ A ∷ U` and `Γ ⊢ A ≡ B`, then `Γ ⊢ A ≡ B ∷ U` (`inverseUnivEq`). -/
theorem inverseUnivEq {Γ : Context} {A B : Term}
    (hA : HasType Γ A .univ) (hAB : TypeEq Γ A B) :
    TermEq Γ A B .univ :=
  inverseUnivEq' (.inl (noU hA)) hAB

/-!
## Uniqueness of Neutral Types (`Definition/Typed/Consequences/NeTypeEq.agda`)
-/

/-- The same variable index in a context has a unique lookup type (`varTypeEq′`). -/
theorem varTypeEq' {Γ : Context} {n : Nat} {R T : Term}
    (hR : Member n R Γ) (hT : Member n T Γ) : R = T := by
  induction hR generalizing T with
  | here =>
      cases hT with
      | here => rfl
  | there hR' ih =>
      cases hT with
      | there hT' =>
          rw [ih hT']

/-- The same variable in a context has judgmentally equal types (`varTypeEq`). -/
theorem varTypeEq {Γ : Context} {x : Nat} {A B : Term}
    (hA : TypeWf Γ A) (_hB : TypeWf Γ B)
    (hxA : Member x A Γ) (hxB : Member x B Γ) : TypeEq Γ A B := by
  rw [← varTypeEq' hxA hxB]
  exact .refl hA

/-- Any neutral term has a unique type up to judgmental type equality (`neTypeEq`). -/
theorem neTypeEq {Γ : Context} {t A B : Term}
    (neT : Neutral t) (htA : HasType Γ t A) (htB : HasType Γ t B) :
    TypeEq Γ A B := by
  induction neT generalizing A B with
  | var x =>
      rcases inversion_var htA with ⟨A₀, hxA₀, hAA₀⟩
      rcases inversion_var htB with ⟨B₀, hxB₀, hBB₀⟩
      have hEq := varTypeEq' hxA₀ hxB₀
      subst hEq
      exact .trans hAA₀ (.symm hBB₀)
  | app neF ih =>
      rcases inversion_app htA with ⟨F₁, G₁, hf₁, ha₁, hAG₁⟩
      rcases inversion_app htB with ⟨F₂, G₂, hf₂, _ha₂, hBG₂⟩
      have hPiEq : TypeEq Γ (.pi F₁ G₁) (.pi F₂ G₂) := ih hf₁ hf₂
      have ⟨_, hG₁G₂⟩ := injectivity hPiEq
      exact .trans hAG₁ (.trans (substTypeEq hG₁G₂ (.refl ha₁)) (.symm hBG₂))
  | natrec _ =>
      rcases inversion_natrec htA with ⟨_, _, _, _, hAFn⟩
      rcases inversion_natrec htB with ⟨_, _, _, _, hBFn⟩
      exact .trans hAFn (.symm hBFn)

/-!
## Congruence of `recStepType` (`Definition/Typed/Consequences/SucCong.agda`)
-/

/-- Congruence of the successor step type in `natrec` (`sucCong`). -/
theorem sucCong {Γ : Context} {F G : Term}
    (hFG : TypeEq (.nat :: Γ) F G) :
    TypeEq Γ (recStepType F) (recStepType G) := by
  have wfΓNat : CtxWf (.nat :: Γ) := wfTypeEq hFG
  cases wfΓNat with
  | cons wfΓ wfNat =>
      have ⟨wfF, _⟩ := syntacticEq hFG
      have hSucVar0 : HasType (.nat :: Γ) (.succ (.var 0)) (wk1 .nat) :=
        .succ (.var (.cons wfΓ wfNat) (Member.here (A := .nat)))
      exact .pi wfNat (.refl wfNat)
        (.pi wfF hFG
          (wkTypeEq (.step .id) (.cons (.cons wfΓ wfNat) wfF)
            (substUpTypeEq hFG (.refl hSucVar0))))

/-!
## Weak-Head Normalization (`Definition/Typed/Consequences/Reduction.agda`, Theorem 3.28)
-/

/-- Every reducible type reduces to a weak-head normal form (`whNorm′`). -/
theorem whNorm' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (pA : RedType eqrel l Γ A) :
    ∃ B, Whnf B ∧ TypeStarWf Γ A B := by
  rcases pA with ⟨rel, hAt⟩
  cases logRelShape_of_LogRelAt hAt with
  | U hU => exact ⟨.univ, .univ, idRedWf (.univ hU.wf)⟩
  | nat D => exact ⟨.nat, .nat, D⟩
  | ne neA => exact ⟨_, .neutral neA.neK, neA.D⟩
  | pi D _ _ _ _ _ _ _ _ _ _ => exact ⟨_, .pi, D⟩

/-- Every well-formed type reduces to a weak-head normal form (`whNorm`, Theorem 3.28). -/
theorem whNorm {Γ : Context} {A : Term} (hA : TypeWf Γ A) :
    ∃ B, Whnf B ∧ TypeStarWf Γ A B :=
  whNorm' (reducible (eqrel := synEqRel) hA)

/-- Every reducible term reduces to a weak-head normal form (`whNormTerm′`). -/
theorem whNormTerm' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A a : Term}
    (pA : RedType eqrel l Γ A) (ha : RedTerm pA a) :
    ∃ b, Whnf b ∧ StarWf Γ a b A := by
  rcases ha with ⟨rel, hAt, ha⟩
  cases logRelShape_of_LogRelAt hAt with
  | U _ =>
      rcases ha with ⟨b, d, typeB, _, _⟩
      exact ⟨b, typeB.toWhnf, d⟩
  | nat D =>
      rcases ha with ⟨_, n, d, _, prop⟩
      exact ⟨n, (natural_of_NaturalProp prop).toWhnf,
        convStarWf d (.symm (subsetStar D.reduction))⟩
  | ne neA =>
      rcases ha with ⟨k, d, nf⟩
      exact ⟨k, .neutral nf.neK,
        convStarWf d (.symm (subsetStar neA.D.reduction))⟩
  | pi D _ _ _ _ _ _ _ _ _ _ =>
      rcases ha with ⟨f, d, funcF, _, _, _⟩
      exact ⟨f, funcF.toWhnf,
        convStarWf d (.symm (subsetStar D.reduction))⟩

/-- Every well-formed term reduces to a weak-head normal form (`whNormTerm`, Theorem 3.28). -/
theorem whNormTerm {Γ : Context} {a A : Term} (ha : HasType Γ a A) :
    ∃ b, Whnf b ∧ StarWf Γ a b A := by
  rcases reducibleTerm (eqrel := synEqRel) ha with ⟨pA, pa⟩
  exact whNormTerm' pA pa

/-!
## Canonicity (`Definition/Typed/Consequences/Canonicity.agda`, Theorem 3.31)
-/



/-- Canonicity helper on `RedNatTerm` in the empty context (`canonicity′` / `canonicity″`). -/
theorem canonicity' {t : Term} (ht : RedNatTerm synEqRel [] t) :
    ∃ k, TermEq [] t (suck k) .nat :=
  @RedNatTerm.rec synEqRel []
    (fun t _ ↦ ∃ k, TermEq [] t (suck k) .nat)
    (fun n _ ↦ ∃ k, TermEq [] n (suck k) .nat)
    (fun _ _ d _ _ ih ↦ by
      rcases ih with ⟨k, hk⟩
      exact ⟨k, .trans (subsetStarTerm d.reduction) hk⟩)
    (fun _ ih ↦ by
      rcases ih with ⟨k, hk⟩
      exact ⟨k + 1, .succ hk⟩)
    ⟨0, .refl (.zero .nil)⟩
    (fun nf ↦ False.elim (noNe nf.hk nf.neK))
    t ht

/-- Canonicity for closed terms of type `ℕ` (`canonicity`, Theorem 3.31). -/
theorem canonicity {t : Term} (ht : HasType [] t .nat) :
    ∃ k, TermEq [] t (suck k) .nat := by
  rcases reducibleTerm (eqrel := synEqRel) ht with ⟨pNat, pt⟩
  have hAt : LogRelAt synEqRel .one [] .nat (RedNatRel synEqRel []) := .nat (elimNat pNat)
  exact canonicity' ((RedTerm_of_LogRelAt hAt pNat).mp pt)

/-!
## Consistency (`Definition/Typed/Consequences/Consistency.agda`, Theorem 3.35)
-/

/-- `zero` is not judgmentally equal to `suc n` in any context. -/
theorem zero_ne_succ {Γ : Context} {n : Term} :
    ¬ TermEq Γ .zero (.succ n) .nat := by
  intro h
  rcases reducibleEqTerm (eqrel := synEqRel) h with ⟨pNat, htu⟩
  have hAt : LogRelAt synEqRel .one Γ .nat (RedNatRel synEqRel Γ) := .nat (elimNat pNat)
  rcases (RedTermEq_of_LogRelAt hAt pNat).mp htu with ⟨_, _, k, k', d, d', _, prop⟩
  have hk : .zero = k := whnfRedStarTerm d.reduction .zero
  have hk' : .succ n = k' := whnfRedStarTerm d'.reduction .succ
  subst hk hk'
  cases prop with
  | ne nf => cases nf.neK

/-- Consistency: `zero` and `suc zero` are not judgmentally equal (`zero≢one`, Theorem 3.35). -/
theorem zero_ne_one : ¬ TermEq [] .zero (.succ .zero) .nat :=
  zero_ne_succ

end Abel2018

/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/Conversion/Soundness.agda,
Definition/Conversion/Stability.agda,
Definition/Conversion/Conversion.agda,
Definition/Conversion/Symmetry.agda,
Definition/Conversion/Transitivity.agda,
Definition/Conversion/Lift.agda,
Definition/Conversion/Universe.agda,
Definition/Conversion/EqRelInstance.agda,
Definition/Conversion/Consequences/Completeness.agda.
-/

namespace Abel2018

/-!
## WHNF Equality Characterization Helpers (`Definition/Typed/Consequences/Equality.agda`)
-/

/-- If `Γ ⊢ ℕ ≡ B` and `B` is in WHNF, then `B = ℕ` (`ℕ≡A`). -/
theorem nat_eq_A_whnf {Γ : Context} {B : Term}
    (h : TypeEq Γ .nat B) (hw : Whnf B) : B = .nat :=
  whnfRedStar (nat_eq_A h) hw

/-- If `Γ ⊢ K ≡ B` with `Neutral K` and `B` in WHNF, then `Neutral B` (`ne≡A`). -/
theorem ne_eq_A_whnf {Γ : Context} {K B : Term}
    (neK : Neutral K) (h : TypeEq Γ K B) (hw : Whnf B) : Neutral B := by
  rcases ne_eq_A neK h with ⟨M, D', neM⟩
  rw [whnfRedStar D'.reduction hw]
  exact neM

/-- If `Γ ⊢ Π F ▹ G ≡ B` and `B` is in WHNF, then `B = Π H ▹ E` for some `H, E` (`Π≡A`). -/
theorem pi_eq_A_whnf {Γ : Context} {F G B : Term}
    (h : TypeEq Γ (.pi F G) B) (hw : Whnf B) :
    ∃ H E, B = .pi H E := by
  rcases pi_eq_A h with ⟨H, E, D'⟩
  exact ⟨H, E, whnfRedStar D' hw⟩

/-!
## Soundness of Algorithmic Equality (`Definition/Conversion/Soundness.agda`, Lemma 4.3)
-/

/-- Soundness of `ConvNeUp` (`soundness~↑`). -/
theorem soundnessNeUp {Γ : Context} {k l A : Term} (d : ConvNeUp Γ k l A) :
    TermEq Γ k l A :=
  @ConvNeUp.rec
    (fun Γ k l A _ ↦ TermEq Γ k l A)
    (fun Γ k l A _ ↦ TermEq Γ k l A)
    (fun Γ A B _ ↦ TypeEq Γ A B)
    (fun Γ A B _ ↦ TypeEq Γ A B)
    (fun Γ t u A _ ↦ TermEq Γ t u A)
    (fun Γ t u A _ ↦ TermEq Γ t u A)
    (fun hx hxy ↦ hxy ▸ .refl hx)
    (fun _ _ ihk iht ↦ .app ihk iht)
    (fun _ _ _ _ ihFG ihab ihhg ihkl ↦ .natrec ihFG ihab ihhg ihkl)
    (fun D _ _ ih ↦ .conv ih (subsetStar D))
    (fun DA DB _ _ _ ih ↦ .trans (subsetStar DA) (.trans ih (.symm (subsetStar DB))))
    (fun hΓ ↦ .refl (.univ hΓ))
    (fun hΓ ↦ .refl (.nat hΓ))
    (fun _ ih ↦ .fromUniv ih)
    (fun hF _ _ ihFH ihGE ↦ .pi hF ihFH ihGE)
    (fun DA dt du _ _ _ _ ih ↦
      .conv (.trans (subsetStarTerm dt) (.trans ih (.symm (subsetStarTerm du))))
        (.symm (subsetStar DA)))
    (fun _ ih ↦ ih)
    (fun hk _ _ hkl ihkl ↦
      let ⟨_, neK, _⟩ := neConvNeDown hkl
      let ⟨_, hkM, _⟩ := syntacticEqTerm ihkl
      .conv ihkl (neTypeEq neK hkM hk))
    (fun hA _ _ ih ↦ inverseUnivEq hA ih)
    (fun hΓ ↦ .refl (.zero hΓ))
    (fun _ ih ↦ .succ ih)
    (fun hF hf hg _ _ _ ih ↦ .eta hF hf hg ih)
    Γ k l A d

/-- Soundness of `ConvNeDown` (`soundness~↓`). -/
theorem soundnessNeDown {Γ : Context} {k l A : Term} :
    ConvNeDown Γ k l A → TermEq Γ k l A
  | .mk D _ hkl => .conv (soundnessNeUp hkl) (subsetStar D)

/-- Soundness of `ConvTypeDown` (`soundnessConv↓`). -/
theorem soundnessConvDown {Γ : Context} {A B : Term} (d : ConvTypeDown Γ A B) :
    TypeEq Γ A B :=
  @ConvTypeDown.rec
    (fun Γ k l A _ ↦ TermEq Γ k l A)
    (fun Γ k l A _ ↦ TermEq Γ k l A)
    (fun Γ A B _ ↦ TypeEq Γ A B)
    (fun Γ A B _ ↦ TypeEq Γ A B)
    (fun Γ t u A _ ↦ TermEq Γ t u A)
    (fun Γ t u A _ ↦ TermEq Γ t u A)
    (fun hx hxy ↦ hxy ▸ .refl hx)
    (fun _ _ ihk iht ↦ .app ihk iht)
    (fun _ _ _ _ ihFG ihab ihhg ihkl ↦ .natrec ihFG ihab ihhg ihkl)
    (fun D _ _ ih ↦ .conv ih (subsetStar D))
    (fun DA DB _ _ _ ih ↦ .trans (subsetStar DA) (.trans ih (.symm (subsetStar DB))))
    (fun hΓ ↦ .refl (.univ hΓ))
    (fun hΓ ↦ .refl (.nat hΓ))
    (fun _ ih ↦ .fromUniv ih)
    (fun hF _ _ ihFH ihGE ↦ .pi hF ihFH ihGE)
    (fun DA dt du _ _ _ _ ih ↦
      .conv (.trans (subsetStarTerm dt) (.trans ih (.symm (subsetStarTerm du))))
        (.symm (subsetStar DA)))
    (fun _ ih ↦ ih)
    (fun hk _ _ hkl ihkl ↦
      let ⟨_, neK, _⟩ := neConvNeDown hkl
      let ⟨_, hkM, _⟩ := syntacticEqTerm ihkl
      .conv ihkl (neTypeEq neK hkM hk))
    (fun hA _ _ ih ↦ inverseUnivEq hA ih)
    (fun hΓ ↦ .refl (.zero hΓ))
    (fun _ ih ↦ .succ ih)
    (fun hF hf hg _ _ _ ih ↦ .eta hF hf hg ih)
    Γ A B d

/-- Soundness of `ConvTypeUp` (`soundnessConv↑`, Lemma 4.3). -/
theorem soundnessConvUp {Γ : Context} {A B : Term} :
    ConvTypeUp Γ A B → TypeEq Γ A B
  | .mk DA DB _ _ hAB =>
      .trans (subsetStar DA) (.trans (soundnessConvDown hAB) (.symm (subsetStar DB)))

/-- Soundness of `ConvTermDown` (`soundnessConv↓Term`). -/
theorem soundnessConvDownTerm {Γ : Context} {t u A : Term} (d : ConvTermDown Γ t u A) :
    TermEq Γ t u A :=
  @ConvTermDown.rec
    (fun Γ k l A _ ↦ TermEq Γ k l A)
    (fun Γ k l A _ ↦ TermEq Γ k l A)
    (fun Γ A B _ ↦ TypeEq Γ A B)
    (fun Γ A B _ ↦ TypeEq Γ A B)
    (fun Γ t u A _ ↦ TermEq Γ t u A)
    (fun Γ t u A _ ↦ TermEq Γ t u A)
    (fun hx hxy ↦ hxy ▸ .refl hx)
    (fun _ _ ihk iht ↦ .app ihk iht)
    (fun _ _ _ _ ihFG ihab ihhg ihkl ↦ .natrec ihFG ihab ihhg ihkl)
    (fun D _ _ ih ↦ .conv ih (subsetStar D))
    (fun DA DB _ _ _ ih ↦ .trans (subsetStar DA) (.trans ih (.symm (subsetStar DB))))
    (fun hΓ ↦ .refl (.univ hΓ))
    (fun hΓ ↦ .refl (.nat hΓ))
    (fun _ ih ↦ .fromUniv ih)
    (fun hF _ _ ihFH ihGE ↦ .pi hF ihFH ihGE)
    (fun DA dt du _ _ _ _ ih ↦
      .conv (.trans (subsetStarTerm dt) (.trans ih (.symm (subsetStarTerm du))))
        (.symm (subsetStar DA)))
    (fun _ ih ↦ ih)
    (fun hk _ _ hkl ihkl ↦
      let ⟨_, neK, _⟩ := neConvNeDown hkl
      let ⟨_, hkM, _⟩ := syntacticEqTerm ihkl
      .conv ihkl (neTypeEq neK hkM hk))
    (fun hA _ _ ih ↦ inverseUnivEq hA ih)
    (fun hΓ ↦ .refl (.zero hΓ))
    (fun _ ih ↦ .succ ih)
    (fun hF hf hg _ _ _ ih ↦ .eta hF hf hg ih)
    Γ t u A d

/-- Soundness of `ConvTermUp` (`soundnessConv↑Term`, Lemma 4.3). -/
theorem soundnessConvUpTerm {Γ : Context} {t u A : Term} :
    ConvTermUp Γ t u A → TermEq Γ t u A
  | .mk DA dt du _ _ _ htu =>
      .conv (.trans (subsetStarTerm dt) (.trans (soundnessConvDownTerm htu) (.symm (subsetStarTerm du))))
        (.symm (subsetStar DA))

/-!
## Context Conversion and Stability (`Definition/Conversion/Stability.agda`)
-/



/-- Syntactic validity and identity conversion substitution for `CtxEq` (`contextConvSubst`). -/
theorem contextConvSubst {Γ Δ : Context} (h : CtxEq Γ Δ) :
    CtxWf Γ ∧ CtxWf Δ ∧ SubstWf Δ idSubst Γ := by
  induction h with
  | nil => exact ⟨.nil, .nil, .nil⟩
  | @cons Γ Δ A B _ hAB ih =>
      rcases ih with ⟨wfΓ, wfΔ, hσ⟩
      have ⟨wfA, wfB⟩ := syntacticEq hAB
      have wfB_Δ : TypeWf Δ B := by
        have q := substitution wfB hσ wfΔ
        rwa [subst_id] at q
      have hBA_Δ : TypeEq Δ B A := by
        have q := substitutionEq (.symm hAB) (substRefl hσ) wfΔ
        rwa [subst_id, subst_id] at q
      have wfΔB : CtxWf (B :: Δ) := .cons wfΔ wfB_Δ
      have hVar0 : HasType (B :: Δ) (.var 0) (wk1 B) := .var wfΔB .here
      have hEqWk : TypeEq (B :: Δ) (wk1 B) (subst (tailSubst idSubst) A) := by
        rw [← wk1_tailId A]
        exact wkTypeEq (.step .id) wfΔB hBA_Δ
      exact ⟨.cons wfΓ wfA, wfΔB,
        .cons (wk1Subst' wfΓ wfΔ wfB_Δ hσ) (.conv hVar0 hEqWk)⟩

/-- Stability of well-formed types under `CtxEq` (`stability`). -/
theorem stability {Γ Δ : Context} {A : Term} (hΓΔ : CtxEq Γ Δ) (hA : TypeWf Γ A) :
    TypeWf Δ A := by
  rcases contextConvSubst hΓΔ with ⟨_, wfΔ, hσ⟩
  have q := substitution hA hσ wfΔ
  rwa [subst_id] at q

/-- Stability of type equality under `CtxEq` (`stabilityEq`). -/
theorem stabilityEq {Γ Δ : Context} {A B : Term} (hΓΔ : CtxEq Γ Δ) (hAB : TypeEq Γ A B) :
    TypeEq Δ A B := by
  rcases contextConvSubst hΓΔ with ⟨_, wfΔ, hσ⟩
  have q := substitutionEq hAB (substRefl hσ) wfΔ
  rwa [subst_id, subst_id] at q

/-- Reflexivity of `CtxEq` (`reflConEq`). -/
theorem reflConEq {Γ : Context} (hΓ : CtxWf Γ) : CtxEq Γ Γ := by
  induction hΓ using CtxWf.indOnly with
  | nil => exact .nil
  | cons _ wfA ih => exact .cons ih (.refl wfA)

/-- Symmetry of `CtxEq` (`symConEq`). -/
theorem symConEq {Γ Δ : Context} (hΓΔ : CtxEq Γ Δ) : CtxEq Δ Γ := by
  induction hΓΔ with
  | nil => exact .nil
  | cons hΓΔ hAB ih => exact .cons ih (stabilityEq hΓΔ (.symm hAB))

/-- Transitivity of `CtxEq`. -/
theorem transConEq {Γ Δ Ε : Context} (h₁ : CtxEq Γ Δ) (h₂ : CtxEq Δ Ε) : CtxEq Γ Ε := by
  induction h₁ generalizing Ε with
  | nil => exact h₂
  | cons h₁ hAB ih =>
      cases h₂ with
      | cons h₂ hBC =>
          exact .cons (ih h₂) (.trans hAB (stabilityEq (symConEq h₁) hBC))

/-- Stability of well-typed terms under `CtxEq` (`stabilityTerm`). -/
theorem stabilityTerm {Γ Δ : Context} {t A : Term}
    (hΓΔ : CtxEq Γ Δ) (ht : HasType Γ t A) : HasType Δ t A := by
  rcases contextConvSubst hΓΔ with ⟨_, wfΔ, hσ⟩
  have q := substitutionTerm ht hσ wfΔ
  rwa [subst_id, subst_id] at q

/-- Stability of single-step term reduction under `CtxEq` (`stabilityRedTerm`). -/
theorem stabilityRedTerm {Γ Δ : Context} {t u A : Term}
    (hΓΔ : CtxEq Γ Δ) (d : Step Γ t u A) : Step Δ t u A := by
  induction d generalizing Δ with
  | conv _ hAB ih => exact .conv (ih hΓΔ) (stabilityEq hΓΔ hAB)
  | app _ ha ih => exact .app (ih hΓΔ) (stabilityTerm hΓΔ ha)
  | beta hF ht ha =>
      exact .beta (stability hΓΔ hF) (stabilityTerm (.cons hΓΔ (.refl hF)) ht)
        (stabilityTerm hΓΔ ha)
  | natrec hF hz hs _ ih =>
      rcases contextConvSubst hΓΔ with ⟨wfΓ, _, _⟩
      exact .natrec (stability (.cons hΓΔ (.refl (.nat wfΓ))) hF)
        (stabilityTerm hΓΔ hz) (stabilityTerm hΓΔ hs) (ih hΓΔ)
  | natrecZero hF hz hs =>
      rcases contextConvSubst hΓΔ with ⟨wfΓ, _, _⟩
      exact .natrecZero (stability (.cons hΓΔ (.refl (.nat wfΓ))) hF)
        (stabilityTerm hΓΔ hz) (stabilityTerm hΓΔ hs)
  | natrecSucc hn hF hz hs =>
      rcases contextConvSubst hΓΔ with ⟨wfΓ, _, _⟩
      exact .natrecSucc (stabilityTerm hΓΔ hn)
        (stability (.cons hΓΔ (.refl (.nat wfΓ))) hF)
        (stabilityTerm hΓΔ hz) (stabilityTerm hΓΔ hs)

/-- Stability of single-step type reduction under `CtxEq` (`stabilityRed`). -/
theorem stabilityRed {Γ Δ : Context} {A B : Term}
    (hΓΔ : CtxEq Γ Δ) : TypeStep Γ A B → TypeStep Δ A B
  | .fromUniv d => .fromUniv (stabilityRedTerm hΓΔ d)

/-- Stability of multi-step type reduction under `CtxEq` (`stabilityRed*`). -/
theorem stabilityRedStar {Γ Δ : Context} {A B : Term}
    (hΓΔ : CtxEq Γ Δ) (D : TypeStar Γ A B) : TypeStar Δ A B := by
  induction D with
  | refl hA => exact .refl (stability hΓΔ hA)
  | step h₁ _ ih => exact .step (stabilityRed hΓΔ h₁) ih

/-- Stability of multi-step term reduction under `CtxEq` (`stabilityRed*Term`). -/
theorem stabilityRedStarTerm {Γ Δ : Context} {t u A : Term}
    (hΓΔ : CtxEq Γ Δ) (d : Star Γ t u A) : Star Δ t u A := by
  induction d with
  | refl ht => exact .refl (stabilityTerm hΓΔ ht)
  | step h₁ _ ih => exact .step (stabilityRedTerm hΓΔ h₁) ih

private abbrev StabNeUpMotive (Γ : Context) (k l A : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvNeUp Δ k l A
private abbrev StabNeDownMotive (Γ : Context) (k l A : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvNeDown Δ k l A
private abbrev StabTypeUpMotive (Γ : Context) (A B : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvTypeUp Δ A B
private abbrev StabTypeDownMotive (Γ : Context) (A B : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvTypeDown Δ A B
private abbrev StabTermUpMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvTermUp Δ t u A
private abbrev StabTermDownMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvTermDown Δ t u A

/-- Stability of `ConvNeUp` under `CtxEq` (`stability~↑`). -/
theorem stabilityNeUp {Γ Δ : Context} {k l A : Term}
    (hΓΔ : CtxEq Γ Δ) (d : ConvNeUp Γ k l A) : ConvNeUp Δ k l A :=
  (@ConvNeUp.rec
    (fun Γ k l A _ ↦ StabNeUpMotive Γ k l A)
    (fun Γ k l A _ ↦ StabNeDownMotive Γ k l A)
    (fun Γ A B _ ↦ StabTypeUpMotive Γ A B)
    (fun Γ A B _ ↦ StabTypeDownMotive Γ A B)
    (fun Γ t u A _ ↦ StabTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ StabTermDownMotive Γ t u A)
    (fun hx hxy _ hΓΔ ↦ .var (stabilityTerm hΓΔ hx) hxy)
    (fun _ _ ihk iht _ hΓΔ ↦ .app (ihk hΓΔ) (iht hΓΔ))
    (fun _ _ _ _ ihFG ihab ihhg ihkl _ hΓΔ ↦
      let ⟨wfΓ, _, _⟩ := contextConvSubst hΓΔ
      .natrec (ihFG (.cons hΓΔ (.refl (.nat wfΓ)))) (ihab hΓΔ) (ihhg hΓΔ) (ihkl hΓΔ))
    (fun D hw _ ih _ hΓΔ ↦ .mk (stabilityRedStar hΓΔ D) hw (ih hΓΔ))
    (fun DA DB hwA hwB _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStar hΓΔ DB) hwA hwB (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .univRefl (contextConvSubst hΓΔ).2.1)
    (fun _ _ hΓΔ ↦ .natRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ .ne (ih hΓΔ))
    (fun hF _ _ ihFH ihGE _ hΓΔ ↦
      .piCong (stability hΓΔ hF) (ihFH hΓΔ) (ihGE (.cons hΓΔ (.refl hF))))
    (fun DA dt du hwB hwt hwu _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStarTerm hΓΔ dt) (stabilityRedStarTerm hΓΔ du)
        hwB hwt hwu (ih hΓΔ))
    (fun _ ih _ hΓΔ ↦ .natIns (ih hΓΔ))
    (fun hk hl neN _ ih _ hΓΔ ↦
      .neIns (stabilityTerm hΓΔ hk) (stabilityTerm hΓΔ hl) neN (ih hΓΔ))
    (fun hA hB _ ih _ hΓΔ ↦
      .univ (stabilityTerm hΓΔ hA) (stabilityTerm hΓΔ hB) (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .zeroRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ .succCong (ih hΓΔ))
    (fun hF hf hg hwf hwg _ ih _ hΓΔ ↦
      .etaEq (stability hΓΔ hF) (stabilityTerm hΓΔ hf) (stabilityTerm hΓΔ hg)
        hwf hwg (ih (.cons hΓΔ (.refl hF))))
    Γ k l A d) hΓΔ

/-- Stability of `ConvNeDown` under `CtxEq` (`stability~↓`). -/
theorem stabilityNeDown {Γ Δ : Context} {k l A : Term}
    (hΓΔ : CtxEq Γ Δ) : ConvNeDown Γ k l A → ConvNeDown Δ k l A
  | .mk D hw hkl => .mk (stabilityRedStar hΓΔ D) hw (stabilityNeUp hΓΔ hkl)

/-- Stability of `ConvTypeDown` under `CtxEq` (`stabilityConv↓`). -/
theorem stabilityConvDown {Γ Δ : Context} {A B : Term}
    (hΓΔ : CtxEq Γ Δ) (d : ConvTypeDown Γ A B) : ConvTypeDown Δ A B :=
  (@ConvTypeDown.rec
    (fun Γ k l A _ ↦ StabNeUpMotive Γ k l A)
    (fun Γ k l A _ ↦ StabNeDownMotive Γ k l A)
    (fun Γ A B _ ↦ StabTypeUpMotive Γ A B)
    (fun Γ A B _ ↦ StabTypeDownMotive Γ A B)
    (fun Γ t u A _ ↦ StabTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ StabTermDownMotive Γ t u A)
    (fun hx hxy _ hΓΔ ↦ .var (stabilityTerm hΓΔ hx) hxy)
    (fun _ _ ihk iht _ hΓΔ ↦ .app (ihk hΓΔ) (iht hΓΔ))
    (fun _ _ _ _ ihFG ihab ihhg ihkl _ hΓΔ ↦
      let ⟨wfΓ, _, _⟩ := contextConvSubst hΓΔ
      .natrec (ihFG (.cons hΓΔ (.refl (.nat wfΓ)))) (ihab hΓΔ) (ihhg hΓΔ) (ihkl hΓΔ))
    (fun D hw _ ih _ hΓΔ ↦ .mk (stabilityRedStar hΓΔ D) hw (ih hΓΔ))
    (fun DA DB hwA hwB _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStar hΓΔ DB) hwA hwB (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .univRefl (contextConvSubst hΓΔ).2.1)
    (fun _ _ hΓΔ ↦ .natRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ .ne (ih hΓΔ))
    (fun hF _ _ ihFH ihGE _ hΓΔ ↦
      .piCong (stability hΓΔ hF) (ihFH hΓΔ) (ihGE (.cons hΓΔ (.refl hF))))
    (fun DA dt du hwB hwt hwu _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStarTerm hΓΔ dt) (stabilityRedStarTerm hΓΔ du)
        hwB hwt hwu (ih hΓΔ))
    (fun _ ih _ hΓΔ ↦ .natIns (ih hΓΔ))
    (fun hk hl neN _ ih _ hΓΔ ↦
      .neIns (stabilityTerm hΓΔ hk) (stabilityTerm hΓΔ hl) neN (ih hΓΔ))
    (fun hA hB _ ih _ hΓΔ ↦
      .univ (stabilityTerm hΓΔ hA) (stabilityTerm hΓΔ hB) (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .zeroRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ .succCong (ih hΓΔ))
    (fun hF hf hg hwf hwg _ ih _ hΓΔ ↦
      .etaEq (stability hΓΔ hF) (stabilityTerm hΓΔ hf) (stabilityTerm hΓΔ hg)
        hwf hwg (ih (.cons hΓΔ (.refl hF))))
    Γ A B d) hΓΔ

/-- Stability of `ConvTypeUp` under `CtxEq` (`stabilityConv↑`). -/
theorem stabilityConvUp {Γ Δ : Context} {A B : Term}
    (hΓΔ : CtxEq Γ Δ) : ConvTypeUp Γ A B → ConvTypeUp Δ A B
  | .mk DA DB hwA hwB hAB =>
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStar hΓΔ DB)
        hwA hwB (stabilityConvDown hΓΔ hAB)

/-- Stability of `ConvTermDown` under `CtxEq` (`stabilityConv↓Term`). -/
theorem stabilityConvDownTerm {Γ Δ : Context} {t u A : Term}
    (hΓΔ : CtxEq Γ Δ) (d : ConvTermDown Γ t u A) : ConvTermDown Δ t u A :=
  (@ConvTermDown.rec
    (fun Γ k l A _ ↦ StabNeUpMotive Γ k l A)
    (fun Γ k l A _ ↦ StabNeDownMotive Γ k l A)
    (fun Γ A B _ ↦ StabTypeUpMotive Γ A B)
    (fun Γ A B _ ↦ StabTypeDownMotive Γ A B)
    (fun Γ t u A _ ↦ StabTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ StabTermDownMotive Γ t u A)
    (fun hx hxy _ hΓΔ ↦ .var (stabilityTerm hΓΔ hx) hxy)
    (fun _ _ ihk iht _ hΓΔ ↦ .app (ihk hΓΔ) (iht hΓΔ))
    (fun _ _ _ _ ihFG ihab ihhg ihkl _ hΓΔ ↦
      let ⟨wfΓ, _, _⟩ := contextConvSubst hΓΔ
      .natrec (ihFG (.cons hΓΔ (.refl (.nat wfΓ)))) (ihab hΓΔ) (ihhg hΓΔ) (ihkl hΓΔ))
    (fun D hw _ ih _ hΓΔ ↦ .mk (stabilityRedStar hΓΔ D) hw (ih hΓΔ))
    (fun DA DB hwA hwB _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStar hΓΔ DB) hwA hwB (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .univRefl (contextConvSubst hΓΔ).2.1)
    (fun _ _ hΓΔ ↦ .natRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ .ne (ih hΓΔ))
    (fun hF _ _ ihFH ihGE _ hΓΔ ↦
      .piCong (stability hΓΔ hF) (ihFH hΓΔ) (ihGE (.cons hΓΔ (.refl hF))))
    (fun DA dt du hwB hwt hwu _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStarTerm hΓΔ dt) (stabilityRedStarTerm hΓΔ du)
        hwB hwt hwu (ih hΓΔ))
    (fun _ ih _ hΓΔ ↦ .natIns (ih hΓΔ))
    (fun hk hl neN _ ih _ hΓΔ ↦
      .neIns (stabilityTerm hΓΔ hk) (stabilityTerm hΓΔ hl) neN (ih hΓΔ))
    (fun hA hB _ ih _ hΓΔ ↦
      .univ (stabilityTerm hΓΔ hA) (stabilityTerm hΓΔ hB) (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .zeroRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ .succCong (ih hΓΔ))
    (fun hF hf hg hwf hwg _ ih _ hΓΔ ↦
      .etaEq (stability hΓΔ hF) (stabilityTerm hΓΔ hf) (stabilityTerm hΓΔ hg)
        hwf hwg (ih (.cons hΓΔ (.refl hF))))
    Γ t u A d) hΓΔ

/-- Stability of `ConvTermUp` under `CtxEq` (`stabilityConv↑Term`). -/
theorem stabilityConvUpTerm {Γ Δ : Context} {t u A : Term}
    (hΓΔ : CtxEq Γ Δ) : ConvTermUp Γ t u A → ConvTermUp Δ t u A
  | .mk DA dt du hwB hwt hwu htu =>
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStarTerm hΓΔ dt) (stabilityRedStarTerm hΓΔ du)
        hwB hwt hwu (stabilityConvDownTerm hΓΔ htu)

/-!
## Type Conversion of Algorithmic Term Equality (`Definition/Conversion/Conversion.agda`)
-/

private abbrev ConvTermUpMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {B : Term}, CtxEq Γ Δ → TypeEq Γ A B → ConvTermUp Δ t u B

private abbrev ConvTermDownMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {B : Term}, CtxEq Γ Δ → TypeEq Γ A B → Whnf B → ConvTermDown Δ t u B

/-- Conversion of `ConvTermDown` (`convConv↓Term`). -/
theorem convConvDownTerm {Γ Δ : Context} {t u A B : Term}
    (hΓΔ : CtxEq Γ Δ) (hAB : TypeEq Γ A B) (hwB : Whnf B) (d : ConvTermDown Γ t u A) :
    ConvTermDown Δ t u B :=
  (@ConvTermDown.rec
    (fun _ _ _ _ _ ↦ True)
    (fun _ _ _ _ _ ↦ True)
    (fun _ _ _ _ ↦ True)
    (fun _ _ _ _ ↦ True)
    (fun Γ t u A _ ↦ ConvTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ ConvTermDownMotive Γ t u A)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ ↦ trivial)
    (fun _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ _ ↦ trivial)
    -- ConvTermUp.mk
    (fun DA dt du _ hwt hwu _ ih _ _ hΓΔ hAB ↦ by
      have ⟨_, wfB⟩ := syntacticEq hAB
      rcases whNorm wfB with ⟨B', hwB', D'⟩
      have hB₁B' : TypeEq _ _ B' :=
        .trans (.symm (subsetStar DA)) (.trans hAB (subsetStar D'.reduction))
      exact .mk (stabilityRedStar hΓΔ D'.reduction)
        (stabilityRedStarTerm hΓΔ (dt.conv hB₁B'))
        (stabilityRedStarTerm hΓΔ (du.conv hB₁B'))
        hwB' hwt hwu (ih hΓΔ hB₁B' hwB'))
    -- ConvTermDown.natIns
    (fun hkl _ _ _ hΓΔ hAB hwB ↦ by
      rw [nat_eq_A_whnf hAB hwB]
      exact .natIns (stabilityNeDown hΓΔ hkl))
    -- ConvTermDown.neIns
    (fun hk hl neN hkl _ _ _ hΓΔ hAB hwB ↦ by
      have neB : Neutral _ := ne_eq_A_whnf neN hAB hwB
      exact .neIns (stabilityTerm hΓΔ (.conv hk hAB))
        (stabilityTerm hΓΔ (.conv hl hAB)) neB (stabilityNeDown hΓΔ hkl))
    -- ConvTermDown.univ
    (fun hA hB hAB_down _ _ _ hΓΔ hAB _ ↦ by
      rw [U_eq_A hAB]
      exact .univ (stabilityTerm hΓΔ hA) (stabilityTerm hΓΔ hB) (stabilityConvDown hΓΔ hAB_down))
    -- ConvTermDown.zeroRefl
    (fun _ _ _ hΓΔ hAB hwB ↦ by
      rw [nat_eq_A_whnf hAB hwB]
      exact .zeroRefl (contextConvSubst hΓΔ).2.1)
    -- ConvTermDown.succCong
    (fun hmn _ _ _ hΓΔ hAB hwB ↦ by
      rw [nat_eq_A_whnf hAB hwB]
      exact .succCong (stabilityConvUpTerm hΓΔ hmn))
    -- ConvTermDown.etaEq
    (fun _ hf hg hwf hwg _ ih _ _ hΓΔ hAB hwB ↦ by
      rcases pi_eq_A_whnf hAB hwB with ⟨F', G', hB_eq⟩
      subst hB_eq
      have ⟨hFF', hGG'⟩ := injectivity hAB
      have ⟨_, wfF'⟩ := syntacticEq hFF'
      exact .etaEq (stability hΓΔ wfF')
        (stabilityTerm hΓΔ (.conv hf hAB))
        (stabilityTerm hΓΔ (.conv hg hAB))
        hwf hwg
        (ih (.cons hΓΔ hFF') hGG'))
    Γ t u A d) hΓΔ hAB hwB

/-- Conversion of `ConvTermUp` (`convConv↑Term`). -/
theorem convConvUpTerm {Γ Δ : Context} {t u A B : Term}
    (hΓΔ : CtxEq Γ Δ) (hAB : TypeEq Γ A B) :
    ConvTermUp Γ t u A → ConvTermUp Δ t u B
  | .mk DA dt du _ hwt hwu htu => by
      have ⟨_, wfB⟩ := syntacticEq hAB
      rcases whNorm wfB with ⟨B', hwB', D'⟩
      have hB₁B' : TypeEq Γ _ B' :=
        .trans (.symm (subsetStar DA)) (.trans hAB (subsetStar D'.reduction))
      exact .mk (stabilityRedStar hΓΔ D'.reduction)
        (stabilityRedStarTerm hΓΔ (dt.conv hB₁B'))
        (stabilityRedStarTerm hΓΔ (du.conv hB₁B'))
        hwB' hwt hwu (convConvDownTerm hΓΔ hB₁B' hwB' htu)

/-- Conversion of `ConvTermUp` in the same context (`convConvTerm`). -/
theorem convConvTerm {Γ : Context} {t u A B : Term}
    (htu : ConvTermUp Γ t u A) (hAB : TypeEq Γ A B) :
    ConvTermUp Γ t u B :=
  convConvUpTerm (reflConEq (wfTypeEq hAB)) hAB htu

/-!
## Symmetry of Algorithmic Equality (`Definition/Conversion/Symmetry.agda`)
-/

private abbrev SymNeUpMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ∃ B, TypeEq Γ A B ∧ ConvNeUp Δ u t B
private abbrev SymNeDownMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ∃ B, Whnf B ∧ TypeEq Γ A B ∧ ConvNeDown Δ u t B
private abbrev SymTypeUpMotive (Γ : Context) (A B : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvTypeUp Δ B A
private abbrev SymTypeDownMotive (Γ : Context) (A B : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvTypeDown Δ B A
private abbrev SymTermUpMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvTermUp Δ u t A
private abbrev SymTermDownMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvTermDown Δ u t A

private theorem sym_var_case {Γ : Context} {x y : Nat} {A : Term}
    (hx : HasType Γ (.var x) A) (hxy : x = y) :
    SymNeUpMotive Γ (.var x) (.var y) A := by
  intro Δ hΓΔ
  refine ⟨A, .refl (syntacticTerm hx), ?_⟩
  subst hxy
  exact .var (stabilityTerm hΓΔ hx) rfl

private theorem sym_app_case {Γ : Context} {k l t v F G : Term}
    (_hkl : ConvNeDown Γ k l (.pi F G)) (htv : ConvTermUp Γ t v F)
    (ihkl : SymNeDownMotive Γ k l (.pi F G))
    (ihtv : SymTermUpMotive Γ t v F) :
    SymNeUpMotive Γ (.app k t) (.app l v) (subst0 G t) := by
  intro Δ hΓΔ
  rcases ihkl hΓΔ with ⟨B, hwB, hAB, hlk⟩
  rcases pi_eq_A_whnf hAB hwB with ⟨F', G', hB_eq⟩
  subst hB_eq
  have ⟨hFF', hGG'⟩ := injectivity hAB
  exact ⟨subst0 G' v, substTypeEq hGG' (soundnessConvUpTerm htv),
    .app hlk (convConvTerm (ihtv hΓΔ) (stabilityEq hΓΔ hFF'))⟩

private theorem sym_natrec_case {Γ : Context} {k l h g a₀ b₀ F G : Term}
    (hFG : ConvTypeUp (.nat :: Γ) F G)
    (_hab : ConvTermUp Γ a₀ b₀ (subst0 F .zero))
    (_hhg : ConvTermUp Γ h g (recStepType F))
    (hkl : ConvNeDown Γ k l .nat)
    (ihFG : SymTypeUpMotive (.nat :: Γ) F G)
    (ihab : SymTermUpMotive Γ a₀ b₀ (subst0 F .zero))
    (ihhg : SymTermUpMotive Γ h g (recStepType F))
    (ihkl : SymNeDownMotive Γ k l .nat) :
    SymNeUpMotive Γ (.natrec F a₀ h k) (.natrec G b₀ g l) (subst0 F k) := by
  intro Δ hΓΔ
  rcases contextConvSubst hΓΔ with ⟨wfΓ, wfΔ, _⟩
  rcases ihkl hΓΔ with ⟨B, hwB, hAB, hlk⟩
  have hB_eq : B = .nat := nat_eq_A_whnf hAB hwB
  subst hB_eq
  have hFG_eq : TypeEq (.nat :: Δ) F G :=
    stabilityEq (.cons hΓΔ (.refl (.nat wfΓ))) (soundnessConvUp hFG)
  have hF0G0 : TypeEq Δ (subst0 F .zero) (subst0 G .zero) :=
    substTypeEq hFG_eq (.refl (.zero wfΔ))
  refine ⟨subst0 G l, substTypeEq (soundnessConvUp hFG) (soundnessNeDown hkl),
    .natrec (ihFG (.cons hΓΔ (.refl (.nat wfΓ))))
      (convConvTerm (ihab hΓΔ) hF0G0)
      (convConvTerm (ihhg hΓΔ) (sucCong hFG_eq))
      hlk⟩

private theorem sym_neDown_case {Γ : Context} {k l A B : Term}
    (D : TypeStar Γ A B) (_hw : Whnf B) (_hkl : ConvNeUp Γ k l A)
    (ihkl : SymNeUpMotive Γ k l A) :
    SymNeDownMotive Γ k l B := by
  intro Δ hΓΔ
  rcases ihkl hΓΔ with ⟨B₁, hAB₁, hlk⟩
  have ⟨_, wfB₁⟩ := syntacticEq hAB₁
  rcases whNorm wfB₁ with ⟨B', hwB', D'⟩
  have hBB' : TypeEq Γ B B' :=
    .trans (.symm (subsetStar D)) (.trans hAB₁ (subsetStar D'.reduction))
  exact ⟨B', hwB', hBB', .mk (stabilityRedStar hΓΔ D'.reduction) hwB' hlk⟩

private theorem sym_piCong_case {Γ : Context} {F G H E : Term}
    (_hF : TypeWf Γ F) (hFH : ConvTypeUp Γ F H) (_hGE : ConvTypeUp (F :: Γ) G E)
    (ihFH : SymTypeUpMotive Γ F H) (ihGE : SymTypeUpMotive (F :: Γ) G E) :
    SymTypeDownMotive Γ (.pi F G) (.pi H E) := by
  intro Δ hΓΔ
  have hFH_eq : TypeEq Γ F H := soundnessConvUp hFH
  have ⟨_, wfH⟩ := syntacticEq (stabilityEq hΓΔ hFH_eq)
  exact .piCong wfH (ihFH hΓΔ) (ihGE (.cons hΓΔ hFH_eq))

/-- Symmetry of `ConvNeUp` (`sym~↑`). -/
theorem symNeUp {Γ Δ : Context} {t u A : Term}
    (hΓΔ : CtxEq Γ Δ) (d : ConvNeUp Γ t u A) :
    ∃ B, TypeEq Γ A B ∧ ConvNeUp Δ u t B :=
  (@ConvNeUp.rec
    (fun Γ t u A _ ↦ SymNeUpMotive Γ t u A)
    (fun Γ t u A _ ↦ SymNeDownMotive Γ t u A)
    (fun Γ A B _ ↦ SymTypeUpMotive Γ A B)
    (fun Γ A B _ ↦ SymTypeDownMotive Γ A B)
    (fun Γ t u A _ ↦ SymTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ SymTermDownMotive Γ t u A)
    (fun hx hxy ↦ sym_var_case hx hxy)
    (fun hkl htv ihkl ihtv ↦ sym_app_case hkl htv ihkl ihtv)
    (fun hFG hab hhg hkl ihFG ihab ihhg ihkl ↦
      sym_natrec_case hFG hab hhg hkl ihFG ihab ihhg ihkl)
    (fun D hw hkl ihkl ↦ sym_neDown_case D hw hkl ihkl)
    (fun DA DB hwA hwB _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DB) (stabilityRedStar hΓΔ DA) hwB hwA (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .univRefl (contextConvSubst hΓΔ).2.1)
    (fun _ _ hΓΔ ↦ .natRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ by
      rcases ih hΓΔ with ⟨B, _, hUB, hBA⟩
      rw [U_eq_A hUB] at hBA
      exact .ne hBA)
    (fun hF hFH hGE ihFH ihGE ↦ sym_piCong_case hF hFH hGE ihFH ihGE)
    (fun DA dt du hwB hwt hwu _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStarTerm hΓΔ du) (stabilityRedStarTerm hΓΔ dt)
        hwB hwu hwt (ih hΓΔ))
    (fun _ ih _ hΓΔ ↦ by
      rcases ih hΓΔ with ⟨B, hwB, hAB, hlk⟩
      rw [nat_eq_A_whnf hAB hwB] at hlk
      exact .natIns hlk)
    (fun hk hl neN _ ih _ hΓΔ ↦ by
      rcases ih hΓΔ with ⟨_, _, _, hlk⟩
      exact .neIns (stabilityTerm hΓΔ hl) (stabilityTerm hΓΔ hk) neN hlk)
    (fun hA hB _ ih _ hΓΔ ↦
      .univ (stabilityTerm hΓΔ hB) (stabilityTerm hΓΔ hA) (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .zeroRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ .succCong (ih hΓΔ))
    (fun hF hf hg hwf hwg _ ih _ hΓΔ ↦
      .etaEq (stability hΓΔ hF) (stabilityTerm hΓΔ hg) (stabilityTerm hΓΔ hf)
        hwg hwf (ih (.cons hΓΔ (.refl hF))))
    Γ t u A d) hΓΔ

/-- Symmetry of `ConvNeDown` (`sym~↓`). -/
theorem symNeDown {Γ Δ : Context} {t u A : Term}
    (hΓΔ : CtxEq Γ Δ) :
    ConvNeDown Γ t u A → ∃ B, Whnf B ∧ TypeEq Γ A B ∧ ConvNeDown Δ u t B
  | .mk D hw hkl => sym_neDown_case D hw hkl (fun hΓΔ' ↦ symNeUp hΓΔ' hkl) hΓΔ

/-- Symmetry of `ConvTypeDown` (`symConv↓`). -/
theorem symConvDown {Γ Δ : Context} {A B : Term}
    (hΓΔ : CtxEq Γ Δ) (d : ConvTypeDown Γ A B) : ConvTypeDown Δ B A :=
  (@ConvTypeDown.rec
    (fun Γ t u A _ ↦ SymNeUpMotive Γ t u A)
    (fun Γ t u A _ ↦ SymNeDownMotive Γ t u A)
    (fun Γ A B _ ↦ SymTypeUpMotive Γ A B)
    (fun Γ A B _ ↦ SymTypeDownMotive Γ A B)
    (fun Γ t u A _ ↦ SymTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ SymTermDownMotive Γ t u A)
    (fun hx hxy ↦ sym_var_case hx hxy)
    (fun hkl htv ihkl ihtv ↦ sym_app_case hkl htv ihkl ihtv)
    (fun hFG hab hhg hkl ihFG ihab ihhg ihkl ↦
      sym_natrec_case hFG hab hhg hkl ihFG ihab ihhg ihkl)
    (fun D hw hkl ihkl ↦ sym_neDown_case D hw hkl ihkl)
    (fun DA DB hwA hwB _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DB) (stabilityRedStar hΓΔ DA) hwB hwA (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .univRefl (contextConvSubst hΓΔ).2.1)
    (fun _ _ hΓΔ ↦ .natRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ by
      rcases ih hΓΔ with ⟨B, _, hUB, hBA⟩
      rw [U_eq_A hUB] at hBA
      exact .ne hBA)
    (fun hF hFH hGE ihFH ihGE ↦ sym_piCong_case hF hFH hGE ihFH ihGE)
    (fun DA dt du hwB hwt hwu _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStarTerm hΓΔ du) (stabilityRedStarTerm hΓΔ dt)
        hwB hwu hwt (ih hΓΔ))
    (fun _ ih _ hΓΔ ↦ by
      rcases ih hΓΔ with ⟨B, hwB, hAB, hlk⟩
      rw [nat_eq_A_whnf hAB hwB] at hlk
      exact .natIns hlk)
    (fun hk hl neN _ ih _ hΓΔ ↦ by
      rcases ih hΓΔ with ⟨_, _, _, hlk⟩
      exact .neIns (stabilityTerm hΓΔ hl) (stabilityTerm hΓΔ hk) neN hlk)
    (fun hA hB _ ih _ hΓΔ ↦
      .univ (stabilityTerm hΓΔ hB) (stabilityTerm hΓΔ hA) (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .zeroRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ .succCong (ih hΓΔ))
    (fun hF hf hg hwf hwg _ ih _ hΓΔ ↦
      .etaEq (stability hΓΔ hF) (stabilityTerm hΓΔ hg) (stabilityTerm hΓΔ hf)
        hwg hwf (ih (.cons hΓΔ (.refl hF))))
    Γ A B d) hΓΔ

/-- Symmetry of `ConvTypeUp` (`symConv↑`). -/
theorem symConvUp {Γ Δ : Context} {A B : Term}
    (hΓΔ : CtxEq Γ Δ) : ConvTypeUp Γ A B → ConvTypeUp Δ B A
  | .mk DA DB hwA hwB hAB =>
      .mk (stabilityRedStar hΓΔ DB) (stabilityRedStar hΓΔ DA)
        hwB hwA (symConvDown hΓΔ hAB)

/-- Symmetry of `ConvTermDown` (`symConv↓Term`). -/
theorem symConvDownTerm {Γ Δ : Context} {t u A : Term}
    (hΓΔ : CtxEq Γ Δ) (d : ConvTermDown Γ t u A) : ConvTermDown Δ u t A :=
  (@ConvTermDown.rec
    (fun Γ t u A _ ↦ SymNeUpMotive Γ t u A)
    (fun Γ t u A _ ↦ SymNeDownMotive Γ t u A)
    (fun Γ A B _ ↦ SymTypeUpMotive Γ A B)
    (fun Γ A B _ ↦ SymTypeDownMotive Γ A B)
    (fun Γ t u A _ ↦ SymTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ SymTermDownMotive Γ t u A)
    (fun hx hxy ↦ sym_var_case hx hxy)
    (fun hkl htv ihkl ihtv ↦ sym_app_case hkl htv ihkl ihtv)
    (fun hFG hab hhg hkl ihFG ihab ihhg ihkl ↦
      sym_natrec_case hFG hab hhg hkl ihFG ihab ihhg ihkl)
    (fun D hw hkl ihkl ↦ sym_neDown_case D hw hkl ihkl)
    (fun DA DB hwA hwB _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DB) (stabilityRedStar hΓΔ DA) hwB hwA (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .univRefl (contextConvSubst hΓΔ).2.1)
    (fun _ _ hΓΔ ↦ .natRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ by
      rcases ih hΓΔ with ⟨B, _, hUB, hBA⟩
      rw [U_eq_A hUB] at hBA
      exact .ne hBA)
    (fun hF hFH hGE ihFH ihGE ↦ sym_piCong_case hF hFH hGE ihFH ihGE)
    (fun DA dt du hwB hwt hwu _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStarTerm hΓΔ du) (stabilityRedStarTerm hΓΔ dt)
        hwB hwu hwt (ih hΓΔ))
    (fun _ ih _ hΓΔ ↦ by
      rcases ih hΓΔ with ⟨B, hwB, hAB, hlk⟩
      rw [nat_eq_A_whnf hAB hwB] at hlk
      exact .natIns hlk)
    (fun hk hl neN _ ih _ hΓΔ ↦ by
      rcases ih hΓΔ with ⟨_, _, _, hlk⟩
      exact .neIns (stabilityTerm hΓΔ hl) (stabilityTerm hΓΔ hk) neN hlk)
    (fun hA hB _ ih _ hΓΔ ↦
      .univ (stabilityTerm hΓΔ hB) (stabilityTerm hΓΔ hA) (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .zeroRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ .succCong (ih hΓΔ))
    (fun hF hf hg hwf hwg _ ih _ hΓΔ ↦
      .etaEq (stability hΓΔ hF) (stabilityTerm hΓΔ hg) (stabilityTerm hΓΔ hf)
        hwg hwf (ih (.cons hΓΔ (.refl hF))))
    Γ t u A d) hΓΔ

/-- Symmetry of `ConvTermUp` (`symConv↑Term`). -/
theorem symConvUpTerm {Γ Δ : Context} {t u A : Term}
    (hΓΔ : CtxEq Γ Δ) : ConvTermUp Γ t u A → ConvTermUp Δ u t A
  | .mk DA dt du hwB hwt hwu htu =>
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStarTerm hΓΔ du)
        (stabilityRedStarTerm hΓΔ dt) hwB hwu hwt (symConvDownTerm hΓΔ htu)

/-- Symmetry of `ConvTypeUp` in the same context (`symConv`). -/
theorem symConv {Γ : Context} {A B : Term} (hAB : ConvTypeUp Γ A B) :
    ConvTypeUp Γ B A :=
  symConvUp (reflConEq (wfTypeEq (soundnessConvUp hAB))) hAB

/-- Symmetry of `ConvTermUp` in the same context (`symConvTerm`). -/
theorem symConvTerm {Γ : Context} {t u A : Term} (htu : ConvTermUp Γ t u A) :
    ConvTermUp Γ u t A :=
  symConvUpTerm (reflConEq (wfTermEq (soundnessConvUpTerm htu))) htu

/-!
## Transitivity of Algorithmic Equality (`Definition/Conversion/Transitivity.agda`)
-/

private abbrev TransNeUpMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {v B : Term}, CtxEq Γ Δ → ConvNeUp Δ u v B → ConvNeUp Γ t v A ∧ TypeEq Γ A B
private abbrev TransNeDownMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {v B : Term}, CtxEq Γ Δ → ConvNeDown Δ u v B → ConvNeDown Γ t v A ∧ TypeEq Γ A B
private abbrev TransTypeUpMotive (Γ : Context) (A B : Term) : Prop :=
  ∀ {Δ : Context} {C : Term}, CtxEq Γ Δ → ConvTypeUp Δ B C → ConvTypeUp Γ A C
private abbrev TransTypeDownMotive (Γ : Context) (A B : Term) : Prop :=
  ∀ {Δ : Context} {C : Term}, CtxEq Γ Δ → ConvTypeDown Δ B C → ConvTypeDown Γ A C
private abbrev TransTermUpMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {v B : Term}, CtxEq Γ Δ → TypeEq Γ A B → ConvTermUp Δ u v B → ConvTermUp Γ t v A
private abbrev TransTermDownMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {v B : Term}, CtxEq Γ Δ → TypeEq Γ A B → ConvTermDown Δ u v B → ConvTermDown Γ t v A

private theorem trans_var_case {Γ : Context} {x y : Nat} {A : Term}
    (hx : HasType Γ (.var x) A) (hxy : x = y) :
    TransNeUpMotive Γ (.var x) (.var y) A := by
  intro Δ v B hΓΔ huv
  generalize hy' : Term.var y = u₀ at huv
  cases huv with
  | @var _ y₀ z _ hy₀ hyz =>
      injection hy' with hy_eq
      subst hy_eq
      refine ⟨.var hx (hxy.trans hyz), ?_⟩
      have hy_Γ : HasType Γ (.var x) B := by
        rw [hxy]
        exact stabilityTerm (symConEq hΓΔ) hy₀
      exact neTypeEq (.var x) hx hy_Γ
  | app _ _ => cases hy'
  | natrec _ _ _ _ => cases hy'

private theorem trans_app_case {Γ : Context} {k l t v F G : Term}
    (_hkl : ConvNeDown Γ k l (.pi F G)) (htv : ConvTermUp Γ t v F)
    (ihkl : TransNeDownMotive Γ k l (.pi F G))
    (ihtv : TransTermUpMotive Γ t v F) :
    TransNeUpMotive Γ (.app k t) (.app l v) (subst0 G t) := by
  intro Δ w B hΓΔ hlw
  generalize hu' : Term.app l v = u₀ at hlw
  cases hlw with
  | var _ _ => cases hu'
  | @app _ l₀ m v₀ c F₁ G₁ hlm hvc =>
      injection hu' with hl_eq hv_eq
      subst hl_eq hv_eq
      rcases ihkl hΓΔ hlm with ⟨hkm, hPiEq⟩
      have ⟨hFF₁, hGG₁⟩ := injectivity hPiEq
      exact ⟨.app hkm (ihtv hΓΔ hFF₁ hvc),
        substTypeEq hGG₁ (soundnessConvUpTerm htv)⟩
  | natrec _ _ _ _ => cases hu'

private theorem trans_natrec_case {Γ : Context} {k l h g a₀ b₀ F G : Term}
    (hFG : ConvTypeUp (.nat :: Γ) F G)
    (_hab : ConvTermUp Γ a₀ b₀ (subst0 F .zero))
    (_hhg : ConvTermUp Γ h g (recStepType F))
    (hkl : ConvNeDown Γ k l .nat)
    (ihFG : TransTypeUpMotive (.nat :: Γ) F G)
    (ihab : TransTermUpMotive Γ a₀ b₀ (subst0 F .zero))
    (ihhg : TransTermUpMotive Γ h g (recStepType F))
    (ihkl : TransNeDownMotive Γ k l .nat) :
    TransNeUpMotive Γ (.natrec F a₀ h k) (.natrec G b₀ g l) (subst0 F k) := by
  intro Δ w B hΓΔ hlw
  generalize hu' : Term.natrec G b₀ g l = u₀ at hlw
  cases hlw with
  | var _ _ => cases hu'
  | app _ _ => cases hu'
  | @natrec _ l₀ m g₀ c b₁ c₀ G₀ H hGH hbc hgc hlm =>
      injection hu' with hG_eq hb_eq hg_eq hl_eq
      subst hG_eq hb_eq hg_eq hl_eq
      rcases contextConvSubst hΓΔ with ⟨wfΓ, _, _⟩
      have hFG_eq : TypeEq (.nat :: Γ) F G := soundnessConvUp hFG
      have hF0G0 : TypeEq Γ (subst0 F .zero) (subst0 G .zero) :=
        substTypeEq hFG_eq (.refl (.zero wfΓ))
      have hStepEq : TypeEq Γ (recStepType F) (recStepType G) := sucCong hFG_eq
      exact ⟨.natrec (ihFG (.cons hΓΔ (.refl (.nat wfΓ))) hGH)
          (ihab hΓΔ hF0G0 hbc) (ihhg hΓΔ hStepEq hgc) (ihkl hΓΔ hlm).1,
        substTypeEq hFG_eq (soundnessNeDown hkl)⟩

private theorem trans_neDown_case {Γ : Context} {k l A B : Term}
    (D : TypeStar Γ A B) (hw : Whnf B) (_hkl : ConvNeUp Γ k l A)
    (ihkl : TransNeUpMotive Γ k l A) :
    TransNeDownMotive Γ k l B := by
  intro Δ v B₂ hΓΔ hlv
  cases hlv with
  | mk D₁ _ hlv_up =>
      rcases ihkl hΓΔ hlv_up with ⟨hkv, hA₁A₂⟩
      exact ⟨.mk D hw hkv,
        .trans (.symm (subsetStar D))
          (.trans hA₁A₂ (subsetStar (stabilityRedStar (symConEq hΓΔ) D₁)))⟩

private theorem trans_typeUp_case {Γ : Context} {A B A' B' : Term}
    (DA : TypeStar Γ A A') (DB : TypeStar Γ B B')
    (hwA : Whnf A') (hwB : Whnf B')
    (_hAB : ConvTypeDown Γ A' B')
    (ihAB : TransTypeDownMotive Γ A' B') :
    TransTypeUpMotive Γ A B := by
  intro Δ C hΓΔ hBC
  cases hBC with
  | @mk _ _ _ A'' B'' D₁ D'' hwA'' hwB'' hA''B'' =>
      have hEq : A'' = B' :=
        whrDetStar ⟨D₁, hwA''⟩ ⟨stabilityRedStar hΓΔ DB, hwB⟩
      subst hEq
      exact .mk DA (stabilityRedStar (symConEq hΓΔ) D'') hwA hwB'' (ihAB hΓΔ hA''B'')

private theorem trans_typeDown_univ_case {Γ : Context} (hΓ : CtxWf Γ) :
    TransTypeDownMotive Γ .univ .univ := by
  intro Δ C _ hBC
  generalize hB : Term.univ = B₀ at hBC
  cases hBC with
  | univRefl _ => exact .univRefl hΓ
  | ne hne =>
      subst hB
      have ⟨_, neK, _⟩ := neConvNeDown hne
      cases neK
  | _ => cases hB

private theorem trans_typeDown_nat_case {Γ : Context} (hΓ : CtxWf Γ) :
    TransTypeDownMotive Γ .nat .nat := by
  intro Δ C _ hBC
  generalize hB : Term.nat = B₀ at hBC
  cases hBC with
  | natRefl _ => exact .natRefl hΓ
  | ne hne =>
      subst hB
      have ⟨_, neK, _⟩ := neConvNeDown hne
      cases neK
  | _ => cases hB

private theorem trans_typeDown_ne_case {Γ : Context} {K L : Term}
    (hKL : ConvNeDown Γ K L .univ) (ihKL : TransNeDownMotive Γ K L .univ) :
    TransTypeDownMotive Γ K L := by
  intro Δ C hΓΔ hLC
  have ⟨_, _, neL⟩ := neConvNeDown hKL
  cases hLC with
  | univRefl _ => cases neL
  | natRefl _ => cases neL
  | ne hLC_ne => exact .ne (ihKL hΓΔ hLC_ne).1
  | piCong _ _ _ => cases neL

private theorem trans_typeDown_pi_case {Γ : Context} {F G H E : Term}
    (hF : TypeWf Γ F) (hFH : ConvTypeUp Γ F H) (_hGE : ConvTypeUp (F :: Γ) G E)
    (ihFH : TransTypeUpMotive Γ F H) (ihGE : TransTypeUpMotive (F :: Γ) G E) :
    TransTypeDownMotive Γ (.pi F G) (.pi H E) := by
  intro Δ C hΓΔ hBC
  generalize hB : Term.pi H E = B₀ at hBC
  cases hBC with
  | ne hne =>
      subst hB
      have ⟨_, neK, _⟩ := neConvNeDown hne
      cases neK
  | piCong _ hHK hEK =>
      injection hB with hH_eq hE_eq
      subst hH_eq hE_eq
      exact .piCong hF (ihFH hΓΔ hHK) (ihGE (.cons hΓΔ (soundnessConvUp hFH)) hEK)
  | _ => cases hB

private theorem trans_termUp_case {Γ : Context} {t u A B₁ t' u' : Term}
    (DA : TypeStar Γ A B₁) (dt : Star Γ t t' B₁) (du : Star Γ u u' B₁)
    (hwB : Whnf B₁) (hwt : Whnf t') (hwu : Whnf u')
    (_htu : ConvTermDown Γ t' u' B₁)
    (ihtu : TransTermDownMotive Γ t' u' B₁) :
    TransTermUpMotive Γ t u A := by
  intro Δ v B hΓΔ hAB huv
  cases huv with
  | @mk _ _ _ _ B₂ t'' u'' D₁ d₁ d'' _ hwt'' hwu'' htu₁ =>
      have hB₁B₂ : TypeEq Γ B₁ B₂ :=
        .trans (.symm (subsetStar DA))
          (.trans hAB (subsetStar (stabilityRedStar (symConEq hΓΔ) D₁)))
      have d₁'' : Star Γ v u'' B₁ :=
        (stabilityRedStarTerm (symConEq hΓΔ) d'').conv (.symm hB₁B₂)
      have d₁' : Star Δ u u' B₂ :=
        stabilityRedStarTerm hΓΔ (du.conv hB₁B₂)
      have hEq : t'' = u' := whrDetStarTerm ⟨d₁, hwt''⟩ ⟨d₁', hwu⟩
      subst hEq
      exact .mk DA dt d₁'' hwB hwt hwu'' (ihtu hΓΔ hB₁B₂ htu₁)

private theorem trans_termDown_natIns_case {Γ : Context} {k l : Term}
    (hkl : ConvNeDown Γ k l .nat) (ihkl : TransNeDownMotive Γ k l .nat) :
    TransTermDownMotive Γ k l .nat := by
  intro Δ v B hΓΔ hAB hlv
  have ⟨_, _, neL⟩ := neConvNeDown hkl
  cases hlv with
  | natIns hlv_ne => exact .natIns (ihkl hΓΔ hlv_ne).1
  | neIns _ _ neB _ => exact False.elim (nat_ne_ne neB hAB)
  | univ _ _ _ => exact False.elim (U_ne_nat (.symm hAB))
  | zeroRefl _ => cases neL
  | succCong _ => cases neL
  | etaEq _ _ _ _ _ _ => exact False.elim (nat_ne_pi hAB)

private theorem trans_termDown_neIns_case {Γ : Context} {k l M N : Term}
    (hk : HasType Γ k N) (_hl : HasType Γ l N) (neN : Neutral N)
    (hkl : ConvNeDown Γ k l M) (ihkl : TransNeDownMotive Γ k l M) :
    TransTermDownMotive Γ k l N := by
  intro Δ v B hΓΔ hAB hlv
  have ⟨_, _, neL⟩ := neConvNeDown hkl
  cases hlv with
  | natIns _ => exact False.elim (nat_ne_ne neN (.symm hAB))
  | neIns _ hv _ hlv_ne =>
      exact .neIns hk (.conv (stabilityTerm (symConEq hΓΔ) hv) (.symm hAB))
        neN (ihkl hΓΔ hlv_ne).1
  | univ _ _ _ => exact False.elim (U_ne_ne neN (.symm hAB))
  | zeroRefl _ => cases neL
  | succCong _ => cases neL
  | etaEq _ _ _ _ _ _ => exact False.elim (pi_ne_ne neN (.symm hAB))

private theorem trans_termDown_univ_case {Γ : Context} {A B : Term}
    (hA : HasType Γ A .univ) (_hB : HasType Γ B .univ)
    (_hAB_down : ConvTypeDown Γ A B) (ihAB : TransTypeDownMotive Γ A B) :
    TransTermDownMotive Γ A B .univ := by
  intro Δ v C hΓΔ hUC hBv
  cases hBv with
  | natIns _ => exact False.elim (U_ne_nat hUC)
  | neIns _ _ neC _ => exact False.elim (U_ne_ne neC hUC)
  | univ _ hv hBv_down =>
      exact .univ hA (stabilityTerm (symConEq hΓΔ) hv) (ihAB hΓΔ hBv_down)
  | zeroRefl _ => exact False.elim (U_ne_nat hUC)
  | succCong _ => exact False.elim (U_ne_nat hUC)
  | etaEq _ _ _ _ _ _ => exact False.elim (U_ne_pi hUC)

private theorem trans_termDown_zero_case {Γ : Context} (hΓ : CtxWf Γ) :
    TransTermDownMotive Γ .zero .zero .nat := by
  intro Δ v B _ hAB hzv
  generalize hz : Term.zero = z₀ at hzv
  cases hzv with
  | natIns hne =>
      subst hz
      have ⟨_, neZ, _⟩ := neConvNeDown hne
      cases neZ
  | neIns _ _ _ hne =>
      subst hz
      have ⟨_, neZ, _⟩ := neConvNeDown hne
      cases neZ
  | univ _ _ _ => exact False.elim (U_ne_nat (.symm hAB))
  | zeroRefl _ => exact .zeroRefl hΓ
  | succCong _ => cases hz
  | etaEq _ _ _ _ _ _ => exact False.elim (nat_ne_pi hAB)

private theorem trans_termDown_succ_case {Γ : Context} {m n : Term}
    (_hmn : ConvTermUp Γ m n .nat) (ihmn : TransTermUpMotive Γ m n .nat) :
    TransTermDownMotive Γ (.succ m) (.succ n) .nat := by
  intro Δ v B hΓΔ hAB hnv
  generalize hs : Term.succ n = s₀ at hnv
  cases hnv with
  | natIns hne =>
      subst hs
      have ⟨_, neS, _⟩ := neConvNeDown hne
      cases neS
  | neIns _ _ _ hne =>
      subst hs
      have ⟨_, neS, _⟩ := neConvNeDown hne
      cases neS
  | univ _ _ _ => exact False.elim (U_ne_nat (.symm hAB))
  | zeroRefl _ => cases hs
  | succCong hnp =>
      injection hs with hn_eq
      subst hn_eq
      exact .succCong (ihmn hΓΔ hAB hnp)
  | etaEq _ _ _ _ _ _ => exact False.elim (nat_ne_pi hAB)

private theorem trans_termDown_eta_case {Γ : Context} {f g F G : Term}
    (hF : TypeWf Γ F) (hf : HasType Γ f (.pi F G)) (_hg : HasType Γ g (.pi F G))
    (hwf : Whnf f) (_hwg : Whnf g)
    (_hfg : ConvTermUp (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G)
    (ihfg : TransTermUpMotive (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G) :
    TransTermDownMotive Γ f g (.pi F G) := by
  intro Δ v B hΓΔ hAB hgv
  cases hgv with
  | natIns _ => exact False.elim (nat_ne_pi (.symm hAB))
  | neIns _ _ neB _ => exact False.elim (pi_ne_ne neB hAB)
  | univ _ _ _ => exact False.elim (U_ne_pi (.symm hAB))
  | zeroRefl _ => exact False.elim (nat_ne_pi (.symm hAB))
  | succCong _ => exact False.elim (nat_ne_pi (.symm hAB))
  | etaEq _ _ hv _ hwv hgv_up =>
      have ⟨hFF', hGG'⟩ := injectivity hAB
      exact .etaEq hF hf (.conv (stabilityTerm (symConEq hΓΔ) hv) (.symm hAB))
        hwf hwv (ihfg (.cons hΓΔ hFF') hGG' hgv_up)

/-- Transitivity of `ConvNeUp` (`trans~↑`). -/
theorem transNeUp {Γ Δ : Context} {t u v A B : Term}
    (hΓΔ : CtxEq Γ Δ) (d₁ : ConvNeUp Γ t u A) (d₂ : ConvNeUp Δ u v B) :
    ConvNeUp Γ t v A ∧ TypeEq Γ A B :=
  (@ConvNeUp.rec
    (fun Γ t u A _ ↦ TransNeUpMotive Γ t u A)
    (fun Γ t u A _ ↦ TransNeDownMotive Γ t u A)
    (fun Γ A B _ ↦ TransTypeUpMotive Γ A B)
    (fun Γ A B _ ↦ TransTypeDownMotive Γ A B)
    (fun Γ t u A _ ↦ TransTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ TransTermDownMotive Γ t u A)
    (fun hx hxy ↦ trans_var_case hx hxy)
    (fun hkl htv ihkl ihtv ↦ trans_app_case hkl htv ihkl ihtv)
    (fun hFG hab hhg hkl ihFG ihab ihhg ihkl ↦
      trans_natrec_case hFG hab hhg hkl ihFG ihab ihhg ihkl)
    (fun D hw hkl ihkl ↦ trans_neDown_case D hw hkl ihkl)
    (fun DA DB hwA hwB hAB ihAB ↦ trans_typeUp_case DA DB hwA hwB hAB ihAB)
    (fun hΓ ↦ trans_typeDown_univ_case hΓ)
    (fun hΓ ↦ trans_typeDown_nat_case hΓ)
    (fun hKL ihKL ↦ trans_typeDown_ne_case hKL ihKL)
    (fun hF hFH hGE ihFH ihGE ↦ trans_typeDown_pi_case hF hFH hGE ihFH ihGE)
    (fun DA dt du hwB hwt hwu htu ihtu ↦
      trans_termUp_case DA dt du hwB hwt hwu htu ihtu)
    (fun hkl ihkl ↦ trans_termDown_natIns_case hkl ihkl)
    (fun hk hl neN hkl ihkl ↦ trans_termDown_neIns_case hk hl neN hkl ihkl)
    (fun hA hB hAB ihAB ↦ trans_termDown_univ_case hA hB hAB ihAB)
    (fun hΓ ↦ trans_termDown_zero_case hΓ)
    (fun hmn ihmn ↦ trans_termDown_succ_case hmn ihmn)
    (fun hF hf hg hwf hwg hfg ihfg ↦
      trans_termDown_eta_case hF hf hg hwf hwg hfg ihfg)
    Γ t u A d₁) hΓΔ d₂

/-- Transitivity of `ConvNeDown` (`trans~↓`). -/
theorem transNeDown {Γ Δ : Context} {t u v A B : Term}
    (hΓΔ : CtxEq Γ Δ) (d₁ : ConvNeDown Γ t u A) (d₂ : ConvNeDown Δ u v B) :
    ConvNeDown Γ t v A ∧ TypeEq Γ A B :=
  match d₁ with
  | .mk D hw hkl => trans_neDown_case D hw hkl (fun hΓΔ' d₂' ↦ transNeUp hΓΔ' hkl d₂') hΓΔ d₂

/-- Transitivity of `ConvTypeDown` (`transConv↓`). -/
theorem transConvDown {Γ Δ : Context} {A B C : Term}
    (hΓΔ : CtxEq Γ Δ) (d₁ : ConvTypeDown Γ A B) (d₂ : ConvTypeDown Δ B C) :
    ConvTypeDown Γ A C :=
  (@ConvTypeDown.rec
    (fun Γ t u A _ ↦ TransNeUpMotive Γ t u A)
    (fun Γ t u A _ ↦ TransNeDownMotive Γ t u A)
    (fun Γ A B _ ↦ TransTypeUpMotive Γ A B)
    (fun Γ A B _ ↦ TransTypeDownMotive Γ A B)
    (fun Γ t u A _ ↦ TransTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ TransTermDownMotive Γ t u A)
    (fun hx hxy ↦ trans_var_case hx hxy)
    (fun hkl htv ihkl ihtv ↦ trans_app_case hkl htv ihkl ihtv)
    (fun hFG hab hhg hkl ihFG ihab ihhg ihkl ↦
      trans_natrec_case hFG hab hhg hkl ihFG ihab ihhg ihkl)
    (fun D hw hkl ihkl ↦ trans_neDown_case D hw hkl ihkl)
    (fun DA DB hwA hwB hAB ihAB ↦ trans_typeUp_case DA DB hwA hwB hAB ihAB)
    (fun hΓ ↦ trans_typeDown_univ_case hΓ)
    (fun hΓ ↦ trans_typeDown_nat_case hΓ)
    (fun hKL ihKL ↦ trans_typeDown_ne_case hKL ihKL)
    (fun hF hFH hGE ihFH ihGE ↦ trans_typeDown_pi_case hF hFH hGE ihFH ihGE)
    (fun DA dt du hwB hwt hwu htu ihtu ↦
      trans_termUp_case DA dt du hwB hwt hwu htu ihtu)
    (fun hkl ihkl ↦ trans_termDown_natIns_case hkl ihkl)
    (fun hk hl neN hkl ihkl ↦ trans_termDown_neIns_case hk hl neN hkl ihkl)
    (fun hA hB hAB ihAB ↦ trans_termDown_univ_case hA hB hAB ihAB)
    (fun hΓ ↦ trans_termDown_zero_case hΓ)
    (fun hmn ihmn ↦ trans_termDown_succ_case hmn ihmn)
    (fun hF hf hg hwf hwg hfg ihfg ↦
      trans_termDown_eta_case hF hf hg hwf hwg hfg ihfg)
    Γ A B d₁) hΓΔ d₂

/-- Transitivity of `ConvTypeUp` (`transConv↑`). -/
theorem transConvUp {Γ Δ : Context} {A B C : Term}
    (hΓΔ : CtxEq Γ Δ) (d₁ : ConvTypeUp Γ A B) (d₂ : ConvTypeUp Δ B C) :
    ConvTypeUp Γ A C :=
  match d₁ with
  | .mk DA DB hwA hwB hAB =>
      trans_typeUp_case DA DB hwA hwB hAB (fun hΓΔ' d₂' ↦ transConvDown hΓΔ' hAB d₂') hΓΔ d₂

/-- Transitivity of `ConvTermDown` (`transConv↓Term`). -/
theorem transConvDownTerm {Γ Δ : Context} {t u v A B : Term}
    (hΓΔ : CtxEq Γ Δ) (hAB : TypeEq Γ A B)
    (d₁ : ConvTermDown Γ t u A) (d₂ : ConvTermDown Δ u v B) :
    ConvTermDown Γ t v A :=
  (@ConvTermDown.rec
    (fun Γ t u A _ ↦ TransNeUpMotive Γ t u A)
    (fun Γ t u A _ ↦ TransNeDownMotive Γ t u A)
    (fun Γ A B _ ↦ TransTypeUpMotive Γ A B)
    (fun Γ A B _ ↦ TransTypeDownMotive Γ A B)
    (fun Γ t u A _ ↦ TransTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ TransTermDownMotive Γ t u A)
    (fun hx hxy ↦ trans_var_case hx hxy)
    (fun hkl htv ihkl ihtv ↦ trans_app_case hkl htv ihkl ihtv)
    (fun hFG hab hhg hkl ihFG ihab ihhg ihkl ↦
      trans_natrec_case hFG hab hhg hkl ihFG ihab ihhg ihkl)
    (fun D hw hkl ihkl ↦ trans_neDown_case D hw hkl ihkl)
    (fun DA DB hwA hwB hAB ihAB ↦ trans_typeUp_case DA DB hwA hwB hAB ihAB)
    (fun hΓ ↦ trans_typeDown_univ_case hΓ)
    (fun hΓ ↦ trans_typeDown_nat_case hΓ)
    (fun hKL ihKL ↦ trans_typeDown_ne_case hKL ihKL)
    (fun hF hFH hGE ihFH ihGE ↦ trans_typeDown_pi_case hF hFH hGE ihFH ihGE)
    (fun DA dt du hwB hwt hwu htu ihtu ↦
      trans_termUp_case DA dt du hwB hwt hwu htu ihtu)
    (fun hkl ihkl ↦ trans_termDown_natIns_case hkl ihkl)
    (fun hk hl neN hkl ihkl ↦ trans_termDown_neIns_case hk hl neN hkl ihkl)
    (fun hA hB hAB ihAB ↦ trans_termDown_univ_case hA hB hAB ihAB)
    (fun hΓ ↦ trans_termDown_zero_case hΓ)
    (fun hmn ihmn ↦ trans_termDown_succ_case hmn ihmn)
    (fun hF hf hg hwf hwg hfg ihfg ↦
      trans_termDown_eta_case hF hf hg hwf hwg hfg ihfg)
    Γ t u A d₁) hΓΔ hAB d₂

/-- Transitivity of `ConvTermUp` (`transConv↑Term`). -/
theorem transConvUpTerm {Γ Δ : Context} {t u v A B : Term}
    (hΓΔ : CtxEq Γ Δ) (hAB : TypeEq Γ A B)
    (d₁ : ConvTermUp Γ t u A) (d₂ : ConvTermUp Δ u v B) :
    ConvTermUp Γ t v A :=
  match d₁ with
  | .mk DA dt du hwB hwt hwu htu =>
      trans_termUp_case DA dt du hwB hwt hwu htu
        (fun hΓΔ' hAB' d₂' ↦ transConvDownTerm hΓΔ' hAB' htu d₂') hΓΔ hAB d₂

/-- Transitivity of `ConvTypeUp` in the same context (`transConv`). -/
theorem transConv {Γ : Context} {A B C : Term}
    (hAB : ConvTypeUp Γ A B) (hBC : ConvTypeUp Γ B C) : ConvTypeUp Γ A C :=
  transConvUp (reflConEq (wfTypeEq (soundnessConvUp hAB))) hAB hBC

/-- Transitivity of `ConvTermUp` in the same context (`transConvTerm`). -/
theorem transConvTerm {Γ : Context} {t u v A : Term}
    (htu : ConvTermUp Γ t u A) (huv : ConvTermUp Γ u v A) : ConvTermUp Γ t v A :=
  let htu_eq := soundnessConvUpTerm htu
  transConvUpTerm (reflConEq (wfTermEq htu_eq)) (.refl (syntacticEqTerm htu_eq).1) htu huv

/-!
## Lifting of Algorithmic Equality (`Definition/Conversion/Lift.agda` & `Universe.agda`)
-/

/-- Lift `ConvTypeDown` to `ConvTypeUp` (`liftConv`). -/
theorem liftConv {Γ : Context} {A B : Term} (hAB : ConvTypeDown Γ A B) :
    ConvTypeUp Γ A B :=
  let ⟨wfA, wfB⟩ := syntacticEq (soundnessConvDown hAB)
  let ⟨hwA, hwB⟩ := whnfConvTypeDown hAB
  .mk (.refl wfA) (.refl wfB) hwA hwB hAB

/-- Lift `ConvTermDown` to `ConvTermUp` (`liftConvTerm`). -/
theorem liftConvTerm {Γ : Context} {t u A : Term} (htu : ConvTermDown Γ t u A) :
    ConvTermUp Γ t u A :=
  let ⟨wfA, wft, wfu⟩ := syntacticEqTerm (soundnessConvDownTerm htu)
  let ⟨hwA, hwt, hwu⟩ := whnfConvTermDown htu
  .mk (.refl wfA) (.refl wft) (.refl wfu) hwA hwt hwu htu

/-- Single-level step for lifting neutral equality to `ConvTermDown` and `ConvTermUp`
(`lift~toConv↓′` and `lift~toConv↑′`). -/
theorem liftNeToConv_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A' rel},
      logRelRec eqrel l l' hlt Γ A' rel →
      (∀ {t u A}, TypeStar Γ A' A → ConvNeDown Γ t u A → ConvTermDown Γ t u A) ∧
      (∀ {t u}, ConvNeUp Γ t u A' → ConvTermUp Γ t u A'))
    {Γ : Context} {A' : Term} {rel : RedRel}
    (hA' : LogRelAt eqrel l Γ A' rel) :
    (∀ {t u A}, TypeStar Γ A' A → ConvNeDown Γ t u A → ConvTermDown Γ t u A) ∧
    (∀ {t u}, ConvNeUp Γ t u A' → ConvTermUp Γ t u A') := by
  have toUp : ∀ {Δ B} (hB : TypeWf Δ B),
      (∀ {t u C}, TypeStar Δ B C → ConvNeDown Δ t u C → ConvTermDown Δ t u C) →
      ∀ {t u}, ConvNeUp Δ t u B → ConvTermUp Δ t u B := by
    intro Δ B wfB hDown t u htu
    rcases whNorm wfB with ⟨C, hwC, D⟩
    have htu_down : ConvNeDown Δ t u C := .mk D.reduction hwC htu
    have ⟨neT, neU⟩ := neConvNeUp htu
    have ⟨_, wft, wfu⟩ := syntacticEqTerm (soundnessNeDown htu_down)
    exact .mk D.reduction (.refl wft) (.refl wfu) hwC
      (.neutral neT) (.neutral neU) (hDown D.reduction htu_down)
  induction hA' with
  | @U Γ₀ _ hU =>
      have hDown : ∀ {t u A}, TypeStar Γ₀ .univ A → ConvNeDown Γ₀ t u A → ConvTermDown Γ₀ t u A := by
        intro t u A D hkl
        cases hkl with
        | mk D₁ _ k_l =>
            have hA : Term.univ = A := whnfRedStar D Whnf.univ
            subst hA
            have ⟨_, wft, wfu⟩ := syntacticEqTerm (.conv (soundnessNeUp k_l) (subsetStar D₁))
            exact .univ wft wfu (.ne (.mk D₁ Whnf.univ k_l))
      exact ⟨hDown, toUp (.univ hU.wf) hDown⟩
  | @nat Γ₀ A₀ D =>
      have hDown : ∀ {t u A}, TypeStar Γ₀ A₀ A → ConvNeDown Γ₀ t u A → ConvTermDown Γ₀ t u A := by
        intro t u A D₁ hkl
        cases hkl with
        | mk D₂ hwB k_l =>
            have hA : .nat = A := whrDetStar ⟨D.reduction, .nat⟩ ⟨D₁, hwB⟩
            subst hA
            exact .natIns (.mk D₂ .nat k_l)
      exact ⟨hDown, toUp D.source hDown⟩
  | @ne Γ₀ A₀ K neA =>
      have hDown : ∀ {t u A}, TypeStar Γ₀ A₀ A → ConvNeDown Γ₀ t u A → ConvTermDown Γ₀ t u A := by
        intro t u A D₁ hkl
        cases hkl with
        | mk D₂ hwB k_l =>
            have hA : K = A := whrDetStar ⟨neA.D.reduction, .neutral neA.neK⟩ ⟨D₁, hwB⟩
            subst hA
            have ⟨_, wft, wfu⟩ := syntacticEqTerm (soundnessNeUp k_l)
            have hAK := subsetStar D₂
            exact .neIns (.conv wft hAK) (.conv wfu hAK) neA.neK
              (.mk D₂ (.neutral neA.neK) k_l)
      exact ⟨hDown, toUp neA.D.source hDown⟩
  | @pi Γ A' F G D hF _ _ _ _ hF_ex derivF hG_ex derivG _ ihF ihG =>
      have hDown : ∀ {t u A}, TypeStar Γ A' A → ConvNeDown Γ t u A → ConvTermDown Γ t u A := by
        intro t u A D₁ hkl
        cases hkl with
        | mk D₂ hwB k_l =>
            have hA : Term.pi F G = A := whrDetStar ⟨D.reduction, .pi⟩ ⟨D₁, hwB⟩
            subst hA
            have hkl_pi : ConvNeDown Γ t u (.pi F G) := .mk D₂ .pi k_l
            have ⟨_, wft, wfu⟩ := syntacticEqTerm (soundnessNeDown hkl_pi)
            have ⟨neT, neU⟩ := neConvNeUp k_l
            have hΓ : CtxWf Γ := wfType hF
            have hΔ₁ : CtxWf (F :: Γ) := .cons hΓ hF
            have hρ₁ : WkCtx (.step .id) (F :: Γ) Γ := .step .id
            rcases hF_ex hρ₁ hΔ₁ with ⟨relF₁, hrF₁⟩
            have pF₁ : RedType eqrel l (F :: Γ) (wk (.step .id) F) :=
              ⟨relF₁, derivF hρ₁ hΔ₁ relF₁ hrF₁⟩
            have hVar0 : HasType (F :: Γ) (.var 0) (wk (.step .id) F) := .var hΔ₁ .here
            have var0_red : RedTerm pF₁ (.var 0) :=
              neuTerm pF₁ (.var 0) hVar0 (eqrel.varRefl hVar0)
            have var0_rel : RelFHasTerm _ (.step .id) (F :: Γ) (.var 0) :=
              ⟨relF₁, hrF₁, (RedTerm_of_LogRelAt (derivF hρ₁ hΔ₁ relF₁ hrF₁) pF₁).mp var0_red⟩
            rcases hG_ex hρ₁ hΔ₁ var0_rel with ⟨relG₁, hrG₁⟩
            have h00 : ConvTermUp (F :: Γ) (.var 0) (.var 0) (wk (.step .id) F) :=
              (ihF hρ₁ hΔ₁ relF₁ hrF₁).2 (.var hVar0 rfl)
            have hApp : ConvTermUp (F :: Γ)
                (.app (wk1 t) (.var 0)) (.app (wk1 u) (.var 0))
                (subst0 (wk (.lift (.step .id)) G) (.var 0)) :=
              (ihG hρ₁ hΔ₁ var0_rel relG₁ hrG₁).2
                (.app (wkConvNeDown hρ₁ hΔ₁ hkl_pi) h00)
            rw [wkSingleSubstId G] at hApp
            exact .etaEq hF wft wfu (.neutral neT) (.neutral neU) hApp
      exact ⟨hDown, toUp D.source hDown⟩
  | emb hlt hA₀ => exact ihRec _ hlt hA₀

theorem liftNeToConvAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A' : Term}
    (pA' : RedType eqrel l Γ A') :
    (∀ {t u A}, TypeStar Γ A' A → ConvNeDown Γ t u A → ConvTermDown Γ t u A) ∧
    (∀ {t u}, ConvNeUp Γ t u A' → ConvTermUp Γ t u A') := by
  rcases pA' with ⟨rel, hA'⟩
  have h0 : ∀ {Γ A' rel}, LogRelAt eqrel .zero Γ A' rel →
      (∀ {t u A}, TypeStar Γ A' A → ConvNeDown Γ t u A → ConvTermDown Γ t u A) ∧
      (∀ {t u}, ConvNeUp Γ t u A' → ConvTermUp Γ t u A') :=
    fun h ↦ liftNeToConv_step (l := .zero) (fun _ hlt ↦ nomatch hlt) h
  cases l with
  | zero => exact h0 hA'
  | one =>
      exact liftNeToConv_step (l := .one)
        (fun _ hlt _ _ _ h ↦ by cases hlt; exact h0 h) hA'

/-- Lift `ConvNeDown` to `ConvTermDown` (`lift~toConv↓`). -/
theorem liftNeToConvDown {Γ : Context} {t u A : Term} :
    ConvNeDown Γ t u A → ConvTermDown Γ t u A
  | .mk D hwB k_l =>
      (liftNeToConvAt (reducible (eqrel := synEqRel) (syntacticRed D).1)).1
        D (.mk D hwB k_l)

/-- Lift `ConvNeUp` to `ConvTermUp` (`lift~toConv↑`). -/
theorem liftNeToConvUp {Γ : Context} {t u A : Term} (htu : ConvNeUp Γ t u A) :
    ConvTermUp Γ t u A :=
  (liftNeToConvAt (reducible (eqrel := synEqRel) (syntacticEqTerm (soundnessNeUp htu)).1)).2 htu

/-- `ConvTermDown` at `U` yields `ConvTypeDown` (`univConv↓`). -/
theorem univConvDown {Γ : Context} {A B : Term} (h : ConvTermDown Γ A B .univ) :
    ConvTypeDown Γ A B := by
  generalize hU : Term.univ = U₀ at h
  cases h with
  | neIns _ _ neU _ =>
      subst hU
      cases neU
  | univ _ _ hAB => exact hAB
  | _ => cases hU

/-- `ConvTermUp` at `U` yields `ConvTypeUp` (`univConv↑`). -/
theorem univConvUp {Γ : Context} {A B : Term} :
    ConvTermUp Γ A B .univ → ConvTypeUp Γ A B
  | .mk D d d' _ hwt' hwu' htu => by
      have hB : Term.univ = _ := whnfRedStar D Whnf.univ
      subst hB
      exact reductionConvTypeUp (.fromUniv d) (.fromUniv d') hwt' hwu'
        (liftConv (univConvDown htu))

/-!
## Algorithmic Equality Instance of `EqRelSet` (`Definition/Conversion/EqRelInstance.agda`)
-/



theorem convNeEq_var {Γ : Context} {x : Nat} {A : Term} (hx : HasType Γ (.var x) A) :
    ConvNeEq Γ (.var x) (.var x) A :=
  ⟨.refl (syntacticTerm hx), .var hx rfl⟩

theorem convNeEq_app {Γ : Context} {f g a b F G : Term}
    (hfg : ConvNeEq Γ f g (.pi F G)) (hab : ConvTermUp Γ a b F) :
    ConvNeEq Γ (.app f a) (.app g b) (subst0 G a) := by
  rcases hfg with ⟨hAB, hfg_up⟩
  have ⟨_, wfB⟩ := syntacticEq hAB
  rcases whNorm wfB with ⟨B', hwB', D⟩
  have hPiB' : TypeEq Γ (.pi F G) B' := .trans hAB (subsetStar D.reduction)
  rcases pi_eq_A_whnf hPiB' hwB' with ⟨H, E, hB'_eq⟩
  subst hB'_eq
  have ⟨hFH, hGE⟩ := injectivity hPiB'
  have ⟨_, wfa, _⟩ := syntacticEqTerm (soundnessConvUpTerm hab)
  exact ⟨substTypeEq hGE (.refl wfa),
    .app (.mk D.reduction .pi hfg_up) (convConvTerm hab hFH)⟩

theorem convNeEq_natrec {Γ : Context} {z z' s s' n n' F F' : Term}
    (hFF' : ConvTypeUp (.nat :: Γ) F F')
    (hzz' : ConvTermUp Γ z z' (subst0 F .zero))
    (hss' : ConvTermUp Γ s s' (recStepType F))
    (hnn' : ConvNeEq Γ n n' .nat) :
    ConvNeEq Γ (.natrec F z s n) (.natrec F' z' s' n') (subst0 F n) := by
  rcases hnn' with ⟨hAB, hnn'_up⟩
  have ⟨_, wfB⟩ := syntacticEq hAB
  rcases whNorm wfB with ⟨B', hwB', D⟩
  have hNatB' : TypeEq Γ .nat B' := .trans hAB (subsetStar D.reduction)
  have hB'_eq : B' = .nat := nat_eq_A_whnf hNatB' hwB'
  subst hB'_eq
  have hnn'_down : ConvNeDown Γ n n' .nat := .mk D.reduction .nat hnn'_up
  have ⟨wfF, _⟩ := syntacticEq (soundnessConvUp hFF')
  have ⟨_, wfn, _⟩ := syntacticEqTerm (soundnessNeDown hnn'_down)
  exact ⟨.refl (substType wfF wfn), .natrec hFF' hzz' hss' hnn'_down⟩

theorem convNeEq_symm {Γ : Context} {k l A : Term} :
    ConvNeEq Γ k l A → ConvNeEq Γ l k A
  | ⟨hAB, hkl⟩ => by
      rcases symNeUp (reflConEq (wfTypeEq hAB)) hkl with ⟨B', hBB', hlk⟩
      exact ⟨.trans hAB hBB', hlk⟩

theorem convNeEq_trans {Γ : Context} {k l m A : Term} :
    ConvNeEq Γ k l A → ConvNeEq Γ l m A → ConvNeEq Γ k m A
  | ⟨hAB₁, hkl⟩, ⟨_, hlm⟩ =>
      ⟨hAB₁, (transNeUp (reflConEq (wfTypeEq hAB₁)) hkl hlm).1⟩

theorem convNeEq_wk {Γ Δ : Context} {k l A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) :
    ConvNeEq Γ k l A → ConvNeEq Δ (wk ρ k) (wk ρ l) (wk ρ A)
  | ⟨hAB, hkl⟩ => ⟨wkTypeEq hρ hΔ hAB, wkConvNeUp hρ hΔ hkl⟩

theorem convNeEq_conv {Γ : Context} {k l A B : Term} :
    ConvNeEq Γ k l A → TypeEq Γ A B → ConvNeEq Γ k l B
  | ⟨hAC, hkl⟩, hAB => ⟨.trans (.symm hAB) hAC, hkl⟩

theorem convNeEq_to_conv {Γ : Context} {k l A : Term} :
    ConvNeEq Γ k l A → ConvTermUp Γ k l A
  | ⟨hAB, hkl⟩ => convConvTerm (liftNeToConvUp hkl) (.symm hAB)

/-- Algorithmic equality instance of `EqRelSet` (`eqRelInstance`). -/
def convEqRel : EqRelSet where
  TypeEqRel := ConvTypeUp
  TermEqRel := ConvTermUp
  NeEqRel := ConvNeEq
  neToTerm := convNeEq_to_conv
  typeToEq := soundnessConvUp
  termToEq := soundnessConvUpTerm
  univ := univConvUp
  symmType := symConv
  symmTerm := symConvTerm
  symmNe := convNeEq_symm
  transType := transConv
  transTerm := transConvTerm
  transNe := convNeEq_trans
  convTerm := convConvTerm
  convNe := convNeEq_conv
  wkType := wkConvTypeUp
  wkTerm := wkConvTermUp
  wkNe := convNeEq_wk
  redType := reductionConvTypeUp
  redTerm := reductionConvTermUp
  univRefl hΓ := liftConv (.univRefl hΓ)
  natRefl hΓ := liftConv (.natRefl hΓ)
  natTermRefl hΓ := liftConvTerm (.univ (.nat hΓ) (.nat hΓ) (.natRefl hΓ))
  piCong hF hFH hGE := liftConv (.piCong hF hFH hGE)
  piTermCong hF hFH_u hGE_u := by
    have ⟨_, hFU, hHU⟩ := syntacticEqTerm (soundnessConvUpTerm hFH_u)
    have ⟨_, hGU, hEU⟩ := syntacticEqTerm (soundnessConvUpTerm hGE_u)
    have hFH := univConvUp hFH_u
    have hGE := univConvUp hGE_u
    have hEU' := stabilityTerm (.cons (reflConEq (wfTerm hFU)) (soundnessConvUp hFH)) hEU
    exact liftConvTerm (.univ (.pi hFU hGU) (.pi hHU hEU') (.piCong hF hFH hGE))
  zeroRefl hΓ := liftConvTerm (.zeroRefl hΓ)
  succCong hmn := liftConvTerm (.succCong hmn)
  etaEq hF hf hg hwf hwg hfg := liftConvTerm (.etaEq hF hf hg hwf hwg hfg)
  varRefl := convNeEq_var
  appCong := convNeEq_app
  natrecCong := convNeEq_natrec

/-!
## Completeness of Algorithmic Equality (`Definition/Conversion/Consequences/Completeness.agda`, Theorem 4.11)
-/

/-- Completeness of algorithmic type equality (`completeEq`, Theorem 4.11). -/
theorem completeEq {Γ : Context} {A B : Term} (hAB : TypeEq Γ A B) :
    ConvTypeUp Γ A B := by
  rcases fundamentalEq (eqrel := convEqRel) hAB with ⟨vΓ, vA, _vB, vAB⟩
  exact escapeValidEq vΓ vA vAB

/-- Completeness of algorithmic term equality (`completeEqTerm`, Theorem 4.11). -/
theorem completeEqTerm {Γ : Context} {t u A : Term} (htu : TermEq Γ t u A) :
    ConvTermUp Γ t u A := by
  rcases fundamentalTermEq (eqrel := convEqRel) htu with ⟨vΓ, vA, _vt, _vu, vtu⟩
  exact escapeValidEqTerm vΓ vA vtu

end Abel2018

open Abel2018

theorem solution :
    (∀ {Γ : Context} {A B : Term}, ConvTypeUp Γ A B → TypeEq Γ A B) ∧
    (∀ {Γ : Context} {t u A : Term}, ConvTermUp Γ t u A → TermEq Γ t u A) ∧
    (∀ {Γ : Context} {A B : Term}, ConvTypeUp Γ A B → ConvTypeUp Γ B A) ∧
    (∀ {Γ : Context} {t u A : Term}, ConvTermUp Γ t u A → ConvTermUp Γ u t A) ∧
    (∀ {Γ : Context} {A B C : Term}, ConvTypeUp Γ A B → ConvTypeUp Γ B C → ConvTypeUp Γ A C) ∧
    (∀ {Γ : Context} {t u v A : Term}, ConvTermUp Γ t u A → ConvTermUp Γ u v A → ConvTermUp Γ t v A) ∧
    (∃ eqrel : EqRelSet,
      eqrel.TypeEqRel = ConvTypeUp ∧
      eqrel.TermEqRel = ConvTermUp ∧
      eqrel.NeEqRel = ConvNeEq) ∧
    (∀ {Γ : Context} {A B : Term}, TypeEq Γ A B → ConvTypeUp Γ A B) ∧
    (∀ {Γ : Context} {t u A : Term}, TermEq Γ t u A → ConvTermUp Γ t u A) := by
  exact ⟨soundnessConvUp, soundnessConvUpTerm, symConv, symConvTerm, transConv, transConvTerm, ⟨convEqRel, rfl, rfl, rfl⟩, completeEq, completeEqTerm⟩
