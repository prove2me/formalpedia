-- Prove2me | solution 1 for Abel2018.lemmas_2_2_to_2_7_typed_reduction_and_weakening
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:52:22.861205+00:00
-- url     : https://prove2.me/submissions/a2779041-c965-41ca-88fe-b1baf550f999

import Definitions.Def_Abel2018_Judgments

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

open Abel2018

theorem solution :
    (∀ {Γ : Context} {t u A : Term}, Step Γ t u A → TermEq Γ t u A) ∧
    (∀ {Γ : Context} {A B : Term}, TypeStep Γ A B → TypeEq Γ A B) ∧
    (∀ {Γ : Context} {t u A : Term}, Step Γ t u A → Whnf t → False) ∧
    (∀ {Γ : Context} {t u A u' A' : Term}, Step Γ t u A → Step Γ t u' A' → u = u') ∧
    (∀ {Γ Δ : Context} {A : Term} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → TypeWf Γ A → TypeWf Δ (wk ρ A)) ∧
    (∀ {Γ Δ : Context} {t A : Term} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → HasType Γ t A → HasType Δ (wk ρ t) (wk ρ A)) ∧
    (∀ {Γ Δ : Context} {A B : Term} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → TypeEq Γ A B → TypeEq Δ (wk ρ A) (wk ρ B)) ∧
    (∀ {Γ Δ : Context} {t u A : Term} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → TermEq Γ t u A → TermEq Δ (wk ρ t) (wk ρ u) (wk ρ A)) ∧
    (∃ eqrel : EqRelSet,
      eqrel.TypeEqRel = TypeEq ∧
      eqrel.TermEqRel = TermEq ∧
      eqrel.NeEqRel = TermEq) := by
  exact ⟨subsetTerm, subsetType, whnfRedTerm, whrDetTerm, wkTypeWf, wkHasType, wkTypeEq, wkTermEq, ⟨synEqRel, rfl, rfl, rfl⟩⟩
