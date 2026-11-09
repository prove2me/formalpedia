-- Prove2me | solution 1 for Abel2018.logical_relation_irrelevance_and_escape
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:55:16.030129+00:00
-- url     : https://prove2.me/submissions/fc7a3007-f73e-407e-9b9e-0a25e1973fa1

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

open Abel2018

theorem solution (eqrel : EqRelSet) :
    (∀ {l₁ l₂ : TypeLevel} {Γ : Context} {A : Term} {rel₁ rel₂ : RedRel},
      LogRelAt eqrel l₁ Γ A rel₁ →
      LogRelAt eqrel l₂ Γ A rel₂ →
      RedRelEquiv rel₁ rel₂) ∧
    (∀ {l₁ l₂ : TypeLevel} {Γ : Context} {A B : Term}
      (p : RedType eqrel l₁ Γ A) (q : RedType eqrel l₂ Γ A),
      RedEq p B → RedEq q B) ∧
    (∀ {l₁ l₂ : TypeLevel} {Γ : Context} {A t : Term}
      (p : RedType eqrel l₁ Γ A) (q : RedType eqrel l₂ Γ A),
      RedTerm p t → RedTerm q t) ∧
    (∀ {l₁ l₂ : TypeLevel} {Γ : Context} {A t u : Term}
      (p : RedType eqrel l₁ Γ A) (q : RedType eqrel l₂ Γ A),
      RedTermEq p t u → RedTermEq q t u) ∧
    (∀ {l : TypeLevel} {Γ : Context} {A : Term},
      RedType eqrel l Γ A → TypeWf Γ A) ∧
    (∀ {l : TypeLevel} {Γ : Context} {A B : Term} (p : RedType eqrel l Γ A),
      RedEq p B → eqrel.TypeEqRel Γ A B) ∧
    (∀ {l : TypeLevel} {Γ : Context} {A t : Term} (p : RedType eqrel l Γ A),
      RedTerm p t → HasType Γ t A) ∧
    (∀ {l : TypeLevel} {Γ : Context} {A t u : Term} (p : RedType eqrel l Γ A),
      RedTermEq p t u → eqrel.TermEqRel Γ t u A) := by
  exact ⟨irrelLogRel, irrelevanceEq, irrelevanceTerm, irrelevanceEqTerm, escape, escapeEq, escapeTerm, escapeTermEq⟩
