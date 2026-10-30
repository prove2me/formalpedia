-- Prove2me | solution 1 for ABKUFinite.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T18:38:56.092366+00:00
-- url     : https://prove2.me/submissions/5ce1ce31-b012-4106-834d-1ea0be1aba00

import Definitions.Def_ABKUFinite_Model
import Mathlib
set_option autoImplicit false
namespace Queelius.Balanced
open ABKUFinite

def selected {n d : ℕ} (loads : Fin (n + 1) → ℕ)
    (choices : Fin (d + 2) → Fin (n + 1)) : Fin (n + 1) :=
  (List.ofFn choices).foldl
    (fun best candidate => if loads candidate < loads best then candidate else best) (choices 0)

lemma threshold_choice {B : Type*} (loads : B → ℕ) (best candidate : B) (k : ℕ) :
    k ≤ loads (if loads candidate < loads best then candidate else best) ↔
      k ≤ loads best ∧ k ≤ loads candidate := by
  by_cases h : loads candidate < loads best
  · rw [if_pos h];omega
  · rw [if_neg h];omega

lemma threshold_fold {B : Type*} (loads : B → ℕ) (xs : List B) (best : B) (k : ℕ) :
    k ≤ loads (xs.foldl (fun best candidate => if loads candidate < loads best then candidate else best) best) ↔
      k ≤ loads best ∧ ∀ b ∈ xs,k ≤ loads b := by
  induction xs generalizing best with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons,ih,threshold_choice]
    simp only [List.forall_mem_cons]
    tauto

lemma selected_ge_iff {n d : ℕ} (loads : Fin (n + 1) → ℕ)
    (choices : Fin (d + 2) → Fin (n + 1)) (k : ℕ) :
    k ≤ loads (selected loads choices) ↔ ∀ i,k ≤ loads (choices i) := by
  rw [selected,threshold_fold]
  constructor
  · rintro ⟨h0,hall⟩ i
    exact hall _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · intro hall
    refine ⟨hall 0,?_⟩
    intro b hb
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hb
    rw [← hi]
    exact hall i

lemma selected_le_each {n d : ℕ} (loads : Fin (n + 1) → ℕ)
    (choices : Fin (d + 2) → Fin (n + 1)) (i : Fin (d + 2)) :
    loads (selected loads choices) ≤ loads (choices i) :=
  (selected_ge_iff loads choices (loads (selected loads choices))).mp le_rfl i

noncomputable def heavyChoicesEquiv {n d : ℕ} (loads : Fin (n + 1) → ℕ) (k : ℕ) :
    {choices : Fin (d + 2) → Fin (n + 1) // k ≤ loads (selected loads choices)} ≃
      (Fin (d + 2) → {b : Fin (n + 1) // k ≤ loads b}) where
  toFun c i := ⟨c.val i,(selected_ge_iff loads c.val k).mp c.property i⟩
  invFun c := ⟨fun i => (c i).val,(selected_ge_iff loads (fun i => (c i).val) k).mpr (fun i => (c i).property)⟩
  left_inv c := by apply Subtype.ext;rfl
  right_inv c := by funext i;apply Subtype.ext;rfl

lemma heavy_choices_card {n d : ℕ} (loads : Fin (n + 1) → ℕ) (k : ℕ) :
    Fintype.card {choices : Fin (d + 2) → Fin (n + 1) // k ≤ loads (selected loads choices)} =
      Fintype.card {b : Fin (n + 1) // k ≤ loads b} ^ (d + 2) := by
  rw [Fintype.card_congr (heavyChoicesEquiv loads k),Fintype.card_fun,Fintype.card_fin]

lemma one_step_probability {n d : ℕ} (loads : Fin (n + 1) → ℕ) (k : ℕ) :
    (Fintype.card {choices : Fin (d + 2) → Fin (n + 1) // k ≤ loads (selected loads choices)} : ℝ) /
      Fintype.card (Fin (d + 2) → Fin (n + 1)) =
        ((Fintype.card {b : Fin (n + 1) // k ≤ loads b} : ℝ) / (n + 1 : ℝ)) ^ (d + 2) := by
  rw [heavy_choices_card]
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_add,Nat.cast_one,div_pow]

lemma step_selected {n d : ℕ} (loads : Fin (n + 1) → ℕ)
    (choices : Fin (d + 2) → Fin (n + 1)) :
    step loads choices=Function.update loads (selected loads choices) (loads (selected loads choices) + 1) := rfl

lemma step_mass {n d : ℕ} (loads : Fin (n + 1) → ℕ)
    (choices : Fin (d + 2) → Fin (n + 1)) :
    (∑ b,step loads choices b)=(∑ b,loads b) + 1 := by
  have he (b : Fin (n + 1)) : step loads choices b=loads b + (if b=selected loads choices then 1 else 0) := by
    rw [step_selected]
    by_cases hb : b=selected loads choices
    · subst b;simp
    · simp [Function.update,hb,Ne.symm hb]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

lemma fold_mass {n d : ℕ} (loads : Fin (n + 1) → ℕ)
    (xs : List (Fin (d + 2) → Fin (n + 1))) :
    (∑ b,xs.foldl step loads b)=(∑ b,loads b) + xs.length := by
  induction xs generalizing loads with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons,ih,step_mass,List.length_cons]
    omega

lemma final_mass (n d : ℕ) (w : Trace n d) : (∑ b,finalLoads n d w b)=n + 1 := by
  rw [finalLoads,fold_mass]
  simp

lemma max_le_balls (n d : ℕ) (w : Trace n d) : maxLoad n d w ≤ n + 1 := by
  apply Finset.sup_le
  intro b hb
  exact (Finset.single_le_sum (fun i hi => Nat.zero_le _) hb).trans_eq (final_mass n d w)

lemma max_positive (n d : ℕ) (w : Trace n d) : 1 ≤ maxLoad n d w := by
  by_contra hn
  have hz : maxLoad n d w=0 := by omega
  have hb : ∀ b,finalLoads n d w b=0 := by
    intro b
    have hh : finalLoads n d w b ≤ maxLoad n d w := Finset.le_sup (Finset.mem_univ b)
    omega
  have hm := final_mass n d w
  simp_rw [hb] at hm
  simp at hm

lemma one_bin_max (d : ℕ) (w : Trace 0 d) : maxLoad 0 d w=1 :=
  le_antisymm (max_le_balls 0 d w) (max_positive 0 d w)

lemma heavy_count_mass {n : ℕ} (loads : Fin (n + 1) → ℕ) (k : ℕ) :
    k * Fintype.card {b : Fin (n + 1) // k ≤ loads b} ≤ ∑ b,loads b := by
  rw [Fintype.card_subtype]
  let H := Finset.univ.filter (fun b : Fin (n + 1) => k ≤ loads b)
  change k * H.card ≤ ∑ b,loads b
  calc
    _ = ∑ b ∈ H,k := by simp [Nat.mul_comm]
    _ ≤ ∑ b ∈ H,loads b := Finset.sum_le_sum (fun b hb => (Finset.mem_filter.mp hb).2)
    _ ≤ ∑ b,loads b := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun b hb hnb => Nat.zero_le _)

lemma final_heavy_count (n d : ℕ) (w : Trace n d) (k : ℕ) :
    k * Fintype.card {b : Fin (n + 1) // k ≤ finalLoads n d w b} ≤ n + 1 := by
  have h := heavy_count_mass (finalLoads n d w) k
  rwa [final_mass] at h

lemma step_component_mono {n d : ℕ} (loads : Fin (n + 1) → ℕ)
    (choices : Fin (d + 2) → Fin (n + 1)) (b : Fin (n + 1)) : loads b ≤ step loads choices b := by
  rw [step_selected]
  by_cases hb : b=selected loads choices
  · subst b;simp
  · simp [Function.update,hb]

lemma fold_component_mono {n d : ℕ} (loads : Fin (n + 1) → ℕ)
    (xs : List (Fin (d + 2) → Fin (n + 1))) (b : Fin (n + 1)) :
    loads b ≤ xs.foldl step loads b := by
  induction xs generalizing loads with
  | nil => exact le_rfl
  | cons a xs ih => exact (step_component_mono loads a b).trans (ih (step loads a))

lemma heavy_count_mono {n : ℕ} (loads loads' : Fin (n + 1) → ℕ)
    (h : ∀ b,loads b ≤ loads' b) (k : ℕ) :
    Fintype.card {b : Fin (n + 1) // k ≤ loads b} ≤
      Fintype.card {b : Fin (n + 1) // k ≤ loads' b} :=
  Fintype.card_subtype_mono _ _ (fun b hb => hb.trans (h b))
end Queelius.Balanced

namespace Queelius.RowIndependence
variable {A B : Type*} [DecidableEq A]
def eraseRow (t : A) (w : A → B) : {i : A // i≠t} → B := fun i => w i.val
def restoreRow (t : A) (b : B) (r : {i : A // i≠t} → B) : A → B :=
  fun i => if hi : i=t then b else r ⟨i,hi⟩
lemma restore_at (t : A) (b : B) (r : {i : A // i≠t} → B) : restoreRow t b r t=b := by
  simp [restoreRow]
lemma erase_restore (t : A) (b : B) (r : {i : A // i≠t} → B) :
    eraseRow t (restoreRow t b r)=r := by
  funext i;simp [eraseRow,restoreRow,i.property]
lemma restore_erase (t : A) (w : A → B) : restoreRow t (w t) (eraseRow t w)=w := by
  funext i;by_cases hi : i=t
  · subst i;simp [restoreRow]
  · simp [restoreRow,eraseRow,hi]
lemma restore_update (t : A) (w : A → B) (b : B) :
    restoreRow t b (eraseRow t w)=Function.update w t b := by
  funext i;by_cases hi : i=t
  · subst i;simp [restoreRow]
  · simp [restoreRow,eraseRow,Function.update,hi,Ne.symm hi]
lemma update_restore (t : A) (b c : B) (r : {i : A // i≠t} → B) :
    Function.update (restoreRow t b r) t c=restoreRow t c r := by
  funext i;by_cases hi : i=t
  · subst i;simp [restoreRow]
  · simp [restoreRow,Function.update,hi,Ne.symm hi]
noncomputable def historyEquiv (t : A) (b0 : B) (H : (A → B) → Prop)
    (hinv : ∀ w b,H (Function.update w t b) ↔ H w) :
    {w : A → B // H w} ≃ {r : {i : A // i≠t} → B // H (restoreRow t b0 r)} × B where
  toFun w := (⟨eraseRow t w.val,by
    rw [restore_update];exact (hinv w.val b0).2 w.property⟩,w.val t)
  invFun z := ⟨restoreRow t z.2 z.1.val,by
    have hh := (hinv (restoreRow t b0 z.1.val) z.2).2 z.1.property
    simpa only [update_restore] using hh⟩
  left_inv w := by apply Subtype.ext;exact restore_erase t w.val
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext;exact erase_restore t z.2 z.1.val
    · exact restore_at t z.2 z.1.val
noncomputable def jointEquiv (t : A) (b0 : B) (H : (A → B) → Prop)
    (hinv : ∀ w b,H (Function.update w t b) ↔ H w) (C : B → Prop) :
    {w : A → B // H w ∧ C (w t)} ≃
      {r : {i : A // i≠t} → B // H (restoreRow t b0 r)} × {b : B // C b} where
  toFun w := (⟨eraseRow t w.val,by
    rw [restore_update];exact (hinv w.val b0).2 w.property.1⟩,⟨w.val t,w.property.2⟩)
  invFun z := ⟨restoreRow t z.2.val z.1.val,by
    constructor
    · have hh := (hinv (restoreRow t b0 z.1.val) z.2.val).2 z.1.property
      simpa only [update_restore] using hh
    · simpa only [restore_at] using z.2.property⟩
  left_inv w := by apply Subtype.ext;exact restore_erase t w.val
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext;exact erase_restore t z.2.val z.1.val
    · apply Subtype.ext;exact restore_at t z.2.val z.1.val
lemma conditional_card [Fintype A] [Fintype B] (t : A) (b0 : B) (H : (A → B) → Prop)
    (hinv : ∀ w b,H (Function.update w t b) ↔ H w) (C : B → Prop)
    (hne : ∃ w,H w) :
    (Nat.card {w : A → B // H w ∧ C (w t)} : ℝ) / Nat.card {w : A → B // H w} =
      (Nat.card {b : B // C b} : ℝ) / Nat.card B := by
  classical
  simp only [Nat.card_eq_fintype_card]
  let R := {r : {i : A // i≠t} → B // H (restoreRow t b0 r)}
  have hn : Nonempty R := by
    obtain ⟨w,hw⟩ := hne
    exact ⟨(historyEquiv t b0 H hinv ⟨w,hw⟩).1⟩
  letI : Nonempty R := hn
  have hr : (Fintype.card R : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card R≠0)
  rw [Fintype.card_congr (jointEquiv t b0 H hinv C),Fintype.card_congr (historyEquiv t b0 H hinv)]
  simp only [Fintype.card_prod,Nat.cast_mul]
  change ((Fintype.card R:ℝ)*Fintype.card {b : B // C b})/((Fintype.card R:ℝ)*Fintype.card B)=_
  exact mul_div_mul_left _ _ hr
end Queelius.RowIndependence

namespace Queelius.BalancedTrace
open ABKUFinite Queelius.Balanced
def prefixLoads {n d : ℕ} (w : Trace n d) (k : ℕ) : Fin (n+1) → ℕ :=
  ((List.ofFn w).take k).foldl step (fun _ => 0)
lemma prefix_final (n d : ℕ) (w : Trace n d) : prefixLoads w (n+1)=finalLoads n d w := by
  unfold prefixLoads finalLoads
  have ht : (List.ofFn w).take (List.ofFn w).length=List.ofFn w := List.take_length
  simpa only [List.length_ofFn] using congrArg (fun xs => xs.foldl step (fun _ => 0)) ht
lemma prefix_update {n d : ℕ} (w : Trace n d) (t : Fin (n+1))
    (c : Fin (d+2) → Fin (n+1)) : prefixLoads (Function.update w t c) t.val=prefixLoads w t.val := by
  unfold prefixLoads
  suffices (List.ofFn (Function.update w t c)).take t.val=(List.ofFn w).take t.val by rw [this]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hit : i < t.val := by
      have hh : i < min t.val (n+1) := by simpa using hi
      omega
    simp only [List.getElem_take,List.getElem_ofFn]
    have hne : (⟨i,by omega⟩ : Fin (n+1))≠t := by intro he;have hv : i=t.val := congrArg Fin.val he;omega
    simp [Function.update,hne,Ne.symm hne]
lemma history_conditional_heavy (n d : ℕ) (t : Fin (n+1)) (loads : Fin (n+1) → ℕ)
    (k : ℕ) (hhistory : ∃ w : Trace n d,prefixLoads w t.val=loads) :
    (Nat.card {w : Trace n d // prefixLoads w t.val=loads ∧
      k ≤ loads (selected loads (w t))} : ℝ) /
        Nat.card {w : Trace n d // prefixLoads w t.val=loads} =
      ((Nat.card {b : Fin (n+1) // k ≤ loads b} : ℝ)/(n+1:ℝ))^(d+2) := by
  classical
  have hh := Queelius.RowIndependence.conditional_card t (fun _ => (0 : Fin (n+1)))
    (fun w : Trace n d => prefixLoads w t.val=loads)
    (fun w c => by rw [prefix_update])
    (fun c => k ≤ loads (selected loads c)) hhistory
  have hs := one_step_probability (d:=d) loads k
  simp only [← Nat.card_eq_fintype_card] at hs
  exact hh.trans hs

def Past {n d : ℕ} (t : Fin (n+1)) (history w : Trace n d) : Prop :=
  ∀ i : Fin (n+1),i < t → w i=history i
lemma past_invariant {n d : ℕ} (t : Fin (n+1)) (history w : Trace n d)
    (c : Fin (d+2) → Fin (n+1)) : Past t history (Function.update w t c) ↔ Past t history w := by
  unfold Past
  constructor
  · intro h i hi
    have hne : i≠t := ne_of_lt hi
    simpa [Function.update,hne] using h i hi
  · intro h i hi
    have hne : i≠t := ne_of_lt hi
    simpa [Function.update,hne] using h i hi
lemma prefix_agree {n d : ℕ} (t : Fin (n+1)) (history w : Trace n d) (hp : Past t history w) :
    prefixLoads w t.val=prefixLoads history t.val := by
  unfold prefixLoads
  suffices (List.ofFn w).take t.val=(List.ofFn history).take t.val by rw [this]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hit : i < t.val := by
      have hh : i < min t.val (n+1) := by simpa using hi
      omega
    simp only [List.getElem_take,List.getElem_ofFn]
    exact hp ⟨i,by omega⟩ hit
lemma full_history_conditional_heavy (n d : ℕ) (t : Fin (n+1)) (history : Trace n d) (k : ℕ) :
    let loads := prefixLoads history t.val
    (Nat.card {w : Trace n d // Past t history w ∧ k ≤ loads (selected loads (w t))} : ℝ) /
      Nat.card {w : Trace n d // Past t history w} =
        ((Nat.card {b : Fin (n+1) // k ≤ loads b} : ℝ)/(n+1:ℝ))^(d+2) := by
  classical
  dsimp only
  have hh := Queelius.RowIndependence.conditional_card t (fun _ => (0 : Fin (n+1)))
    (Past t history) (fun w c => past_invariant t history w c)
    (fun c => k ≤ prefixLoads history t.val (selected (prefixLoads history t.val) c))
    ⟨history,fun i hi => rfl⟩
  have hs := one_step_probability (d:=d) (prefixLoads history t.val) k
  simp only [← Nat.card_eq_fintype_card] at hs
  exact hh.trans hs

noncomputable def actualEventEquiv {n d : ℕ} (t : Fin (n+1)) (history : Trace n d) (k : ℕ) :
    {w : Trace n d // Past t history w ∧
      k ≤ prefixLoads w t.val (selected (prefixLoads w t.val) (w t))} ≃
    {w : Trace n d // Past t history w ∧
      k ≤ prefixLoads history t.val (selected (prefixLoads history t.val) (w t))} where
  toFun w := ⟨w.val,w.property.1,by
    simpa only [prefix_agree t history w.val w.property.1] using w.property.2⟩
  invFun w := ⟨w.val,w.property.1,by
    simpa only [prefix_agree t history w.val w.property.1] using w.property.2⟩
  left_inv w := rfl
  right_inv w := rfl
lemma actual_history_probability (n d : ℕ) (t : Fin (n+1)) (history : Trace n d) (k : ℕ) :
    (Nat.card {w : Trace n d // Past t history w ∧
      k ≤ prefixLoads w t.val (selected (prefixLoads w t.val) (w t))} : ℝ) /
      Nat.card {w : Trace n d // Past t history w} =
        ((Nat.card {b : Fin (n+1) // k ≤ prefixLoads history t.val b} : ℝ)/(n+1:ℝ))^(d+2) := by
  rw [Nat.card_congr (actualEventEquiv t history k)]
  exact full_history_conditional_heavy n d t history k

lemma prefix_step {n d : ℕ} (w : Trace n d) (t : Fin (n+1)) :
    prefixLoads w (t.val+1)=step (prefixLoads w t.val) (w t) := by
  unfold prefixLoads
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_ofFn] using t.isLt),List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil,List.getElem_ofFn]
lemma prefix_mass {n d : ℕ} (w : Trace n d) (k : ℕ) (hk : k ≤ n+1) :
    (∑ b,prefixLoads w k b)=k := by
  rw [prefixLoads,fold_mass]
  simp only [Finset.sum_const_zero,zero_add,List.length_take,List.length_ofFn,min_eq_left hk]
lemma chosen_height_iff {n d : ℕ} (w : Trace n d) (t : Fin (n+1)) (k : ℕ) :
    k+1 ≤ prefixLoads w (t.val+1) (selected (prefixLoads w t.val) (w t)) ↔
      k ≤ prefixLoads w t.val (selected (prefixLoads w t.val) (w t)) := by
  rw [prefix_step,step_selected,Function.update_self]
  omega
lemma next_height_probability (n d : ℕ) (t : Fin (n+1)) (history : Trace n d) (k : ℕ) :
    (Nat.card {w : Trace n d // Past t history w ∧
      k+1 ≤ prefixLoads w (t.val+1) (selected (prefixLoads w t.val) (w t))} : ℝ) /
      Nat.card {w : Trace n d // Past t history w} =
        ((Nat.card {b : Fin (n+1) // k ≤ prefixLoads history t.val b} : ℝ)/(n+1:ℝ))^(d+2) := by
  simp_rw [chosen_height_iff]
  exact actual_history_probability n d t history k

lemma history_card_positive (n d : ℕ) (t : Fin (n+1)) (history : Trace n d) :
    0 < Nat.card {w : Trace n d // Past t history w} := by
  classical
  letI : Nonempty {w : Trace n d // Past t history w} := ⟨⟨history,fun i hi => rfl⟩⟩
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_pos
lemma next_height_upper (n d : ℕ) (t : Fin (n+1)) (history : Trace n d) (k B : ℕ)
    (hb : Nat.card {b : Fin (n+1) // k ≤ prefixLoads history t.val b} ≤ B) :
    (Nat.card {w : Trace n d // Past t history w ∧
      k+1 ≤ prefixLoads w (t.val+1) (selected (prefixLoads w t.val) (w t))} : ℝ) /
      Nat.card {w : Trace n d // Past t history w} ≤ ((B:ℝ)/(n+1:ℝ))^(d+2) := by
  rw [next_height_probability]
  gcongr
end Queelius.BalancedTrace

namespace Queelius.FiniteBranching
variable {C S : Type*}
def splitFirst (k : ℕ) : (Fin (k+1) → C) ≃ C × (Fin k → C) where
  toFun w := (w 0,fun i => w i.succ)
  invFun z := Fin.cons z.1 z.2
  left_inv w := by funext i;refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv z := by rcases z with ⟨c,r⟩;rfl
def weight (T : S → C → S) (F : S → C → ℝ) : (k : ℕ) → S → (Fin k → C) → ℝ
  | 0,_,_ => 1
  | k+1,s,w => F s (w 0)*weight T F k (T s (w 0)) (fun i => w i.succ)
lemma weight_nonneg (T : S → C → S) (F : S → C → ℝ) (hF : ∀ s c,0 ≤ F s c)
    (k : ℕ) (s : S) (w : Fin k → C) : 0 ≤ weight T F k s w := by
  induction k generalizing s with
  | zero => exact zero_le_one
  | succ k ih => exact mul_nonneg (hF s (w 0)) (ih _ _)
lemma sum_succ [Fintype C] (T : S → C → S) (F : S → C → ℝ) (k : ℕ) (s : S) :
    (∑ w : Fin (k+1) → C,weight T F (k+1) s w)=
      ∑ c : C,∑ r : Fin k → C,F s c*weight T F k (T s c) r := by
  classical
  calc
    _ = ∑ z : C × (Fin k → C),F s z.1*weight T F k (T s z.1) z.2 :=
      Fintype.sum_equiv (splitFirst k) _ _ (fun w => rfl)
    _ = _ := Fintype.sum_prod_type _
lemma sum_bound [Fintype C] (T : S → C → S) (F : S → C → ℝ)
    (q : ℝ) (hq : 0 ≤ q) (hF : ∀ s c,0 ≤ F s c)
    (hmean : ∀ s,(∑ c,F s c) ≤ Fintype.card C*q) (k : ℕ) :
    ∀ s,(∑ w : Fin k → C,weight T F k s w) ≤ ((Fintype.card C:ℝ)*q)^k := by
  classical
  induction k with
  | zero => intro s;simp [weight,Fintype.card_fun]
  | succ k ih =>
    intro s
    rw [sum_succ]
    calc
      _ ≤ ∑ c : C,F s c*((Fintype.card C:ℝ)*q)^k := by
        apply Finset.sum_le_sum
        intro c hc
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (ih (T s c)) (hF s c)
      _ = (∑ c : C,F s c)*((Fintype.card C:ℝ)*q)^k := by rw [Finset.sum_mul]
      _ ≤ ((Fintype.card C:ℝ)*q)*((Fintype.card C:ℝ)*q)^k :=
        mul_le_mul_of_nonneg_right (hmean s) (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hq) _)
      _ = _ := by rw [pow_succ];ring
lemma average_bound [Fintype C] [Nonempty C] (T : S → C → S) (F : S → C → ℝ)
    (q : ℝ) (hq : 0 ≤ q) (hF : ∀ s c,0 ≤ F s c)
    (hmean : ∀ s,(∑ c,F s c) ≤ Fintype.card C*q) (k : ℕ) (s : S) :
    (∑ w : Fin k → C,weight T F k s w)/(Fintype.card (Fin k → C):ℝ) ≤ q^k := by
  have hc : (0:ℝ)<Fintype.card (Fin k → C) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hc]
  have hh := sum_bound T F q hq hF hmean k s
  simpa [Fintype.card_fun,mul_pow,Nat.cast_pow,Nat.mul_comm,mul_comm] using hh
end Queelius.FiniteBranching

namespace Queelius.BalancedMoment
open ABKUFinite Queelius.Balanced Queelius.FiniteBranching
abbrev Choices (n d : ℕ) := Fin (d+2) → Fin (n+1)
def factor (ρ : ℝ) (b : Bool) : ℝ := if b=true then ρ else 1
lemma factor_nonneg (ρ : ℝ) (hρ : 0 ≤ ρ) (b : Bool) : 0 ≤ factor ρ b := by
  cases b <;> simp [factor,hρ]
lemma sum_factor {C : Type*} [Fintype C] (J : C → Bool) (ρ : ℝ) :
    (∑ c,factor ρ (J c))=(Fintype.card C:ℝ)+(ρ-1)*(Nat.card {c : C // J c=true}:ℝ) := by
  classical
  have he : ∀ c,factor ρ (J c)=1+(ρ-1)*(if J c=true then (1:ℝ) else 0) := by
    intro c;cases J c <;> simp [factor] <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  congr 1
  · simp
  · congr 1
    simp [Nat.card_eq_fintype_card,Fintype.card_subtype]
noncomputable def stoppedHit {n d : ℕ} (k B : ℕ) (loads : Fin (n+1) → ℕ) (c : Choices n d) : Bool :=
  decide (Nat.card {b : Fin (n+1) // k ≤ loads b} ≤ B ∧ k ≤ loads (selected loads c))
lemma stopped_probability (n d k B : ℕ) (loads : Fin (n+1) → ℕ) :
    (Nat.card {c : Choices n d // stoppedHit k B loads c=true}:ℝ)/Nat.card (Choices n d) ≤
      ((B:ℝ)/(n+1:ℝ))^(d+2) := by
  classical
  by_cases hb : Nat.card {b : Fin (n+1) // k ≤ loads b} ≤ B
  · simp only [stoppedHit,decide_eq_true_eq,hb,true_and]
    have hs := one_step_probability (d:=d) loads k
    simp only [← Nat.card_eq_fintype_card] at hs
    rw [hs]
    gcongr
  · simp only [stoppedHit,decide_eq_true_eq,hb,false_and]
    simp
    positivity
lemma stopped_mean (n d k B : ℕ) (ρ : ℝ) (hρ : 1 ≤ ρ) (loads : Fin (n+1) → ℕ) :
    (∑ c : Choices n d,factor ρ (stoppedHit k B loads c)) ≤
      (Fintype.card (Choices n d):ℝ)*(1+(ρ-1)*((B:ℝ)/(n+1:ℝ))^(d+2)) := by
  classical
  have he := sum_factor (stoppedHit (d:=d) k B loads) ρ
  have hp := stopped_probability n d k B loads
  simp only [Nat.card_eq_fintype_card] at he hp
  have hc : (0:ℝ)<Fintype.card (Choices n d) := by exact_mod_cast Fintype.card_pos
  have hcnt := (div_le_iff₀ hc).mp hp
  have hm := mul_le_mul_of_nonneg_left hcnt (sub_nonneg.mpr hρ)
  rw [he]
  nlinarith
lemma stopped_moment (n d k B rounds : ℕ) (ρ : ℝ) (hρ : 1 ≤ ρ) (loads : Fin (n+1) → ℕ) :
    (∑ w : Fin rounds → Choices n d,
      weight step (fun s c => factor ρ (stoppedHit k B s c)) rounds loads w) /
        (Fintype.card (Fin rounds → Choices n d):ℝ) ≤
      (1+(ρ-1)*((B:ℝ)/(n+1:ℝ))^(d+2))^rounds := by
  apply average_bound
  · positivity
  · intro s c;exact factor_nonneg ρ (by linarith) _
  · exact stopped_mean n d k B ρ hρ
end Queelius.BalancedMoment

namespace Queelius.FiniteBranching
variable {C S : Type*}
def hits (T : S → C → S) (J : S → C → Bool) : S → List C → ℕ
  | _,[] => 0
  | s,c::cs => (if J s c=true then 1 else 0)+hits T J (T s c) cs
lemma hits_prefix (T : S → C → S) (J : S → C → Bool) (k : ℕ) (s : S) (w : Fin k → C) :
    hits T J s (List.ofFn w)=∑ t : Fin k,
      if J (((List.ofFn w).take t.val).foldl T s) (w t)=true then 1 else 0 := by
  induction k generalizing s with
  | zero => simp [hits]
  | succ k ih =>
    simp only [List.ofFn_succ,hits,Fin.sum_univ_succ,Fin.val_zero,List.take_zero,List.foldl_nil,
      Fin.val_succ,List.take_succ_cons,List.foldl_cons]
    exact congrArg (fun z : ℕ => (if J s (w 0)=true then 1 else 0)+z)
      (ih (T s (w 0)) (fun i => w i.succ))
end Queelius.FiniteBranching

namespace Queelius.BalancedMoment
open ABKUFinite Queelius.Balanced Queelius.FiniteBranching
lemma weight_hits {C S : Type*} (T : S → C → S) (J : S → C → Bool) (ρ : ℝ)
    (rounds : ℕ) (s : S) (w : Fin rounds → C) :
    weight T (fun s c => factor ρ (J s c)) rounds s w=ρ^(hits T J s (List.ofFn w)) := by
  induction rounds generalizing s with
  | zero => simp [weight,hits]
  | succ rounds ih =>
    simp only [weight,List.ofFn_succ,hits]
    rw [ih]
    cases hj : J s (w 0) <;> simp [factor,hj,pow_add]
lemma finite_tail {W : Type*} [Fintype W] [Nonempty W] (Z : W → ℕ)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (A : ℝ)
    (havg : (∑ w,ρ^(Z w))/(Fintype.card W:ℝ) ≤ A) (z : ℕ) :
    (Nat.card {w : W // z ≤ Z w}:ℝ)/Nat.card W ≤ A/ρ^z := by
  classical
  let H := Finset.univ.filter (fun w : W => z ≤ Z w)
  have hr : 0 < ρ^z := pow_pos (by linarith) _
  have hc : (0:ℝ)<Fintype.card W := by exact_mod_cast Fintype.card_pos
  have hmass : (Nat.card {w : W // z ≤ Z w}:ℝ)*ρ^z ≤ ∑ w,ρ^(Z w) := by
    calc
      _ = ∑ _w ∈ H,ρ^z := by simp [H,Nat.card_eq_fintype_card,Fintype.card_subtype,nsmul_eq_mul]
      _ ≤ ∑ w ∈ H,ρ^(Z w) := Finset.sum_le_sum (fun w hw => pow_le_pow_right₀ hρ (Finset.mem_filter.mp hw).2)
      _ ≤ ∑ w,ρ^(Z w) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun w hw hnw => pow_nonneg (by linarith) _)
  simp only [Nat.card_eq_fintype_card] at hmass ⊢
  calc
    _ = ((Fintype.card {w : W // z ≤ Z w}:ℝ)*ρ^z)/((Fintype.card W:ℝ)*ρ^z) :=
      (mul_div_mul_right _ _ hr.ne').symm
    _ ≤ (∑ w,ρ^(Z w))/((Fintype.card W:ℝ)*ρ^z) :=
      div_le_div_of_nonneg_right hmass (mul_nonneg hc.le hr.le)
    _ = ((∑ w,ρ^(Z w))/(Fintype.card W:ℝ))/ρ^z := (div_div _ _ _).symm
    _ ≤ A/ρ^z := div_le_div_of_nonneg_right havg hr.le
lemma stopped_count_moment (n d k B rounds : ℕ) (ρ : ℝ) (hρ : 1 ≤ ρ) (loads : Fin (n+1) → ℕ) :
    (∑ w : Fin rounds → Choices n d,ρ^(hits step (stoppedHit k B) loads (List.ofFn w))) /
      (Fintype.card (Fin rounds → Choices n d):ℝ) ≤
        (1+(ρ-1)*((B:ℝ)/(n+1:ℝ))^(d+2))^rounds := by
  have hh := stopped_moment n d k B rounds ρ hρ loads
  simpa only [weight_hits] using hh
lemma stopped_tail (n d k B rounds z : ℕ) (ρ : ℝ) (hρ : 1 ≤ ρ) (loads : Fin (n+1) → ℕ) :
    (Nat.card {w : Fin rounds → Choices n d // z ≤ hits step (stoppedHit k B) loads (List.ofFn w)}:ℝ) /
      Nat.card (Fin rounds → Choices n d) ≤
        (1+(ρ-1)*((B:ℝ)/(n+1:ℝ))^(d+2))^rounds/ρ^z := by
  exact finite_tail (fun w : Fin rounds → Choices n d => hits step (stoppedHit k B) loads (List.ofFn w))
    ρ hρ _ (stopped_count_moment n d k B rounds ρ hρ loads) z
lemma stopped_count_prefix (n d k B : ℕ) (w : Trace n d) :
    hits step (stoppedHit k B) (fun _ => 0) (List.ofFn w)=∑ t : Fin (n+1),
      if stoppedHit k B (Queelius.BalancedTrace.prefixLoads w t.val) (w t)=true then 1 else 0 := by
  exact hits_prefix step (stoppedHit k B) (n+1) (fun _ => 0) w
lemma full_trace_tail (n d k B z : ℕ) (ρ : ℝ) (hρ : 1 ≤ ρ) :
    probability n d (fun w => z ≤ hits step (stoppedHit k B) (fun _ => 0) (List.ofFn w)) ≤
      (1+(ρ-1)*((B:ℝ)/(n+1:ℝ))^(d+2))^(n+1)/ρ^z := by
  have hh := stopped_tail n d k B (n+1) z ρ hρ (fun _ => 0)
  simpa only [probability,← Nat.card_eq_fintype_card] using hh
end Queelius.BalancedMoment

namespace Queelius.BalancedLayer
open ABKUFinite Queelius.Balanced Queelius.FiniteBranching Queelius.BalancedMoment
noncomputable def heavy {n : ℕ} (loads : Fin (n+1) → ℕ) (k : ℕ) : ℕ := Nat.card {b : Fin (n+1) // k ≤ loads b}
lemma heavy_mono {n : ℕ} (L L' : Fin (n+1) → ℕ) (h : ∀ b,L b ≤ L' b) (k : ℕ) : heavy L k ≤ heavy L' k := by
  have hh := heavy_count_mono L L' h k
  simpa only [heavy,← Nat.card_eq_fintype_card] using hh
lemma step_heavy {n d : ℕ} (L : Fin (n+1) → ℕ) (c : Choices n d) (k : ℕ) :
    heavy (step L c) (k+1) ≤ heavy L (k+1)+(if k ≤ L (selected L c) then 1 else 0) := by
  classical
  let H := Finset.univ.filter (fun b : Fin (n+1) => k+1 ≤ L b)
  let H' := Finset.univ.filter (fun b : Fin (n+1) => k+1 ≤ step L c b)
  have hsub : H' ⊆ insert (selected L c) H := by
    intro b hb
    by_cases he : b=selected L c
    · exact Finset.mem_insert.mpr (Or.inl he)
    · apply Finset.mem_insert.mpr;apply Or.inr
      have hh := (Finset.mem_filter.mp hb).2
      rw [step_selected,Function.update_of_ne he] at hh
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩
  simp only [heavy,Nat.card_eq_fintype_card,Fintype.card_subtype]
  change H'.card ≤ H.card+(if k ≤ L (selected L c) then 1 else 0)
  by_cases hk : k ≤ L (selected L c)
  · rw [if_pos hk]
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  · simp only [if_neg hk,Nat.add_zero]
    apply Finset.card_le_card
    intro b hb
    have hh := (Finset.mem_filter.mp hb).2
    by_cases he : b=selected L c
    · subst b
      rw [step_selected,Function.update_self] at hh
      omega
    · rw [step_selected,Function.update_of_ne he] at hh
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩
lemma fold_heavy {n d : ℕ} (L : Fin (n+1) → ℕ) (xs : List (Choices n d)) (k B : ℕ)
    (hfinal : heavy (xs.foldl step L) k ≤ B) :
    heavy (xs.foldl step L) (k+1) ≤ heavy L (k+1)+hits step (stoppedHit k B) L xs := by
  induction xs generalizing L with
  | nil => simp [hits]
  | cons c cs ih =>
    have hf : heavy (cs.foldl step (step L c)) k ≤ B := hfinal
    have hh := ih (step L c) hf
    have hm := heavy_mono L ((c::cs).foldl step L) (fold_component_mono L (c::cs)) k
    have hcur : heavy L k ≤ B := hm.trans hfinal
    have hstep := step_heavy L c k
    have he : (if stoppedHit k B L c=true then 1 else 0)=(if k ≤ L (selected L c) then 1 else 0) := by
      have hcur' : Nat.card {b : Fin (n+1) // k ≤ L b} ≤ B := hcur
      simp only [stoppedHit,decide_eq_true_eq,hcur',true_and]
    simp only [List.foldl_cons,hits,he]
    omega
lemma trace_heavy {n d : ℕ} (w : Trace n d) (k B : ℕ) (hf : heavy (finalLoads n d w) k ≤ B) :
    heavy (finalLoads n d w) (k+1) ≤ hits step (stoppedHit k B) (fun _ => 0) (List.ofFn w) := by
  have hh := fold_heavy (fun _ : Fin (n+1) => 0) (List.ofFn w) k B hf
  have hz : heavy (fun _ : Fin (n+1) => 0) (k+1)=0 := by
    simp [heavy,Nat.card_eq_fintype_card,Fintype.card_subtype]
  simpa only [hz,Nat.zero_add,finalLoads] using hh
lemma probability_mono (n d : ℕ) (E F : Trace n d → Prop) (h : ∀ w,E w → F w) :
    probability n d E ≤ probability n d F := by
  classical
  simp only [probability,← Nat.card_eq_fintype_card]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hh : Nat.card {w : Trace n d // E w} ≤ Nat.card {w : Trace n d // F w} := by
    apply Nat.card_le_card_of_injective (fun w => (⟨w.val,h w.val w.property⟩ : {w : Trace n d // F w}))
    intro a b he;apply Subtype.ext;exact congrArg (fun w : {w : Trace n d // F w} => w.val) he
  exact_mod_cast hh
lemma layer_joint_tail (n d k B z : ℕ) (ρ : ℝ) (hρ : 1 ≤ ρ) :
    probability n d (fun w => z ≤ heavy (finalLoads n d w) (k+1) ∧ heavy (finalLoads n d w) k ≤ B) ≤
      (1+(ρ-1)*((B:ℝ)/(n+1:ℝ))^(d+2))^(n+1)/ρ^z := by
  apply le_trans (probability_mono n d _ _ ?_) (full_trace_tail n d k B z ρ hρ)
  intro w hw
  exact hw.1.trans (trace_heavy w k B hw.2)

lemma probability_split (n d : ℕ) (E C : Trace n d → Prop) :
    probability n d E ≤ probability n d (fun w => E w ∧ C w)+probability n d (fun w => ¬C w) := by
  classical
  have hcard : Nat.card {w : Trace n d // E w} ≤
      Nat.card {w : Trace n d // E w ∧ C w}+Nat.card {w : Trace n d // ¬C w} := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype]
    let A := Finset.univ.filter E
    let AC := Finset.univ.filter (fun w => E w ∧ C w)
    let NC := Finset.univ.filter (fun w => ¬C w)
    change A.card ≤ AC.card+NC.card
    have hsub : A ⊆ AC ∪ NC := by
      intro w hw
      have he := (Finset.mem_filter.mp hw).2
      by_cases hc : C w
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he,hc⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩))
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simp only [probability,← Nat.card_eq_fintype_card]
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hcard
lemma layer_recurrence (n d k B z : ℕ) (ρ : ℝ) (hρ : 1 ≤ ρ) :
    probability n d (fun w => z ≤ heavy (finalLoads n d w) (k+1)) ≤
      probability n d (fun w => B < heavy (finalLoads n d w) k)+
        (1+(ρ-1)*((B:ℝ)/(n+1:ℝ))^(d+2))^(n+1)/ρ^z := by
  have hs := probability_split n d (fun w => z ≤ heavy (finalLoads n d w) (k+1))
    (fun w => heavy (finalLoads n d w) k ≤ B)
  simp only [not_le] at hs
  have hj := layer_joint_tail n d k B z ρ hρ
  linarith
end Queelius.BalancedLayer

namespace Queelius.BalancedTail
open ABKUFinite Queelius.Balanced Queelius.BalancedLayer
noncomputable section

def mean (n d B : ℕ) : ℝ := (n+1:ℝ)*((B:ℝ)/(n+1:ℝ))^(d+2)
lemma mean_nonneg (n d B : ℕ) : 0 ≤ mean n d B := by unfold mean;positivity
lemma mean_pos (n d B : ℕ) (hB : 0 < B) : 0 < mean n d B := by unfold mean;positivity
lemma power_exp (u : ℝ) (hu : 0 ≤ u) (N : ℕ) : (1+u)^N ≤ Real.exp ((N:ℝ)*u) := by
  rw [Real.exp_nat_mul]
  apply pow_le_pow_left₀ (by linarith)
  simpa only [add_comm] using Real.add_one_le_exp u
lemma moment_exp (n d B : ℕ) (ρ : ℝ) (hρ : 1 ≤ ρ) :
    (1+(ρ-1)*((B:ℝ)/(n+1:ℝ))^(d+2))^(n+1) ≤ Real.exp ((ρ-1)*mean n d B) := by
  have hp : 0 ≤ ((B:ℝ)/(n+1:ℝ))^(d+2) := by positivity
  have hh := power_exp ((ρ-1)*((B:ℝ)/(n+1:ℝ))^(d+2)) (mul_nonneg (by linarith) hp) (n+1)
  simpa only [mean,Nat.cast_add,Nat.cast_one,mul_left_comm] using hh
lemma exp_parameter : 1 ≤ Real.exp 1 := by
  simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show (0:ℝ) ≤ 1 by norm_num)
lemma exponential_ratio (n d B z : ℕ) :
    (1+(Real.exp 1-1)*((B:ℝ)/(n+1:ℝ))^(d+2))^(n+1)/(Real.exp 1)^z ≤
      Real.exp ((Real.exp 1-1)*mean n d B-z) := by
  calc
    _ ≤ Real.exp ((Real.exp 1-1)*mean n d B)/(Real.exp 1)^z :=
      div_le_div_of_nonneg_right (moment_exp n d B (Real.exp 1) exp_parameter) (by positivity)
    _ = _ := by rw [← Real.exp_nat_mul,Real.exp_sub];simp
lemma exponential_small (n d B z : ℕ) (hz : 4*mean n d B ≤ z) :
    (1+(Real.exp 1-1)*((B:ℝ)/(n+1:ℝ))^(d+2))^(n+1)/(Real.exp 1)^z ≤ Real.exp (-(z:ℝ)/2) := by
  apply (exponential_ratio n d B z).trans
  apply Real.exp_le_exp.mpr
  have hm := mean_nonneg n d B
  have he := Real.exp_one_lt_three
  have hh := mul_le_mul_of_nonneg_right (show Real.exp 1-1 ≤ 2 by linarith) hm
  linarith
lemma layer_exponential (n d k B z : ℕ) (hz : 4*mean n d B ≤ z) :
    probability n d (fun w => z ≤ heavy (finalLoads n d w) (k+1)) ≤
      probability n d (fun w => B < heavy (finalLoads n d w) k)+Real.exp (-(z:ℝ)/2) := by
  exact (layer_recurrence n d k B z (Real.exp 1) exp_parameter).trans
    (add_le_add le_rfl (exponential_small n d B z hz))
lemma unit_ratio (n d B : ℕ) (hB : 0 < B) :
    (1+((1+1/mean n d B)-1)*((B:ℝ)/(n+1:ℝ))^(d+2))^(n+1)/(1+1/mean n d B) ≤
      3*mean n d B := by
  have hm := mean_pos n d B hB
  have hr : 1 ≤ 1+1/mean n d B := le_add_of_nonneg_right (by positivity)
  have heq : ((1+1/mean n d B)-1)*mean n d B=1 := by field_simp <;> ring
  have hx := moment_exp n d B (1+1/mean n d B) hr
  rw [heq] at hx
  apply (div_le_div_of_nonneg_right hx (by positivity)).trans
  apply (div_le_iff₀ (show 0 < 1+1/mean n d B by positivity)).mpr
  have heq2 : mean n d B*(1+1/mean n d B)=mean n d B+1 := by field_simp <;> ring
  rw [show 3*mean n d B*(1+1/mean n d B)=3*(mean n d B+1) by rw [mul_assoc,heq2]]
  linarith [Real.exp_one_lt_three]
lemma last_layer (n d k B : ℕ) (hB : 0 < B) :
    probability n d (fun w => 1 ≤ heavy (finalLoads n d w) (k+1)) ≤
      probability n d (fun w => B < heavy (finalLoads n d w) k)+3*mean n d B := by
  have hm := mean_pos n d B hB
  have hr : 1 ≤ 1+1/mean n d B := le_add_of_nonneg_right (by positivity)
  have hh := layer_recurrence n d k B 1 (1+1/mean n d B) hr
  simp only [pow_one] at hh
  exact hh.trans (add_le_add le_rfl (unit_ratio n d B hB))

def failure (n d k B : ℕ) : ℝ := probability n d (fun w => B < heavy (finalLoads n d w) k)
lemma failure_step (n d k B C : ℕ) (hC : 4*mean n d B ≤ (C:ℝ)+1) :
    failure n d (k+1) C ≤ failure n d k B+Real.exp (-((C:ℝ)+1)/2) := by
  have hh := layer_exponential n d k B (C+1) (by exact_mod_cast hC)
  simpa only [failure,Nat.cast_add,Nat.cast_one,Nat.succ_le_iff] using hh
lemma failure_iterate (n d k : ℕ) (B : ℕ → ℕ) (r : ℕ)
    (hstep : ∀ j < r,4*mean n d (B j) ≤ (B (j+1):ℝ)+1) :
    failure n d (k+r) (B r) ≤ failure n d k (B 0)+
      ∑ j ∈ Finset.range r,Real.exp (-((B (j+1):ℝ)+1)/2) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hprev := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
    have hnext := failure_step n d (k+r) (B r) (B (r+1)) (hstep r (Nat.lt_succ_self r))
    rw [Finset.sum_range_succ]
    have hk : k+(r+1)=(k+r)+1 := by omega
    rw [hk]
    linarith
end
end Queelius.BalancedTail

namespace Queelius.BalancedTail
open ABKUFinite Queelius.Balanced Queelius.BalancedLayer
noncomputable section
lemma heavy_mass (n d : ℕ) (w : Trace n d) (k : ℕ) :
    k*heavy (finalLoads n d w) k ≤ n+1 := by
  simpa only [heavy,Nat.card_eq_fintype_card] using final_heavy_count n d w k
lemma initial_cap (n d k B : ℕ) (hcap : n+1 < k*(B+1)) (w : Trace n d) :
    heavy (finalLoads n d w) k ≤ B := by
  have hh := heavy_mass n d w k
  by_contra h
  have hm := Nat.mul_le_mul_left k (show B+1 ≤ heavy (finalLoads n d w) k by omega)
  omega
lemma initial_failure (n d k B : ℕ) (hcap : n+1 < k*(B+1)) : failure n d k B=0 := by
  have he : (fun w : Trace n d => B < heavy (finalLoads n d w) k)=(fun _ => False) := by
    funext w;apply propext;exact iff_false_intro (not_lt_of_ge (initial_cap n d k B hcap w))
  rw [failure,he]
  simp [probability]
lemma probability_compl (n d : ℕ) (E : Trace n d → Prop) :
    probability n d (fun w => ¬E w)=1-probability n d E := by
  classical
  have hc : (Fintype.card (Trace n d):ℝ) ≠ 0 := by positivity
  have hle := Fintype.card_subtype_le E
  simp only [probability,Fintype.card_subtype_compl,Nat.cast_sub hle,sub_div,div_self hc]
lemma heavy_positive {n : ℕ} (L : Fin (n+1) → ℕ) (k : ℕ) :
    1 ≤ heavy L k ↔ ∃ b,k ≤ L b := by
  classical
  simp only [heavy,Nat.card_eq_fintype_card,Nat.succ_le_iff,Fintype.card_pos_iff,nonempty_subtype]
lemma max_good_iff (n d L : ℕ) (w : Trace n d) :
    maxLoad n d w ≤ L ↔ ¬(1 ≤ heavy (finalLoads n d w) (L+1)) := by
  rw [heavy_positive]
  simp only [maxLoad,Finset.sup_le_iff,Finset.mem_univ,true_implies,not_exists,not_le,Nat.lt_succ_iff]
lemma max_probability (n d L : ℕ) :
    probability n d (fun w => maxLoad n d w ≤ L)=
      1-probability n d (fun w => 1 ≤ heavy (finalLoads n d w) (L+1)) := by
  have he : (fun w : Trace n d => maxLoad n d w ≤ L)=
      (fun w => ¬(1 ≤ heavy (finalLoads n d w) (L+1))) := by
    funext w;exact propext (max_good_iff n d L w)
  rw [he,probability_compl]
lemma finite_upper_certificate (n d k r : ℕ) (B : ℕ → ℕ)
    (hbase : n+1 < k*(B 0+1))
    (hstep : ∀ j < r,4*mean n d (B j) ≤ (B (j+1):ℝ)+1)
    (hlast : 0 < B r) :
    1-((∑ j ∈ Finset.range r,Real.exp (-((B (j+1):ℝ)+1)/2))+3*mean n d (B r)) ≤
      probability n d (fun w => maxLoad n d w ≤ k+r) := by
  have hi := failure_iterate n d k B r hstep
  rw [initial_failure n d k (B 0) hbase,zero_add] at hi
  have hl := last_layer n d (k+r) (B r) hlast
  change probability n d (fun w => 1 ≤ heavy (finalLoads n d w) ((k+r)+1)) ≤
    failure n d (k+r) (B r)+3*mean n d (B r) at hl
  rw [max_probability]
  linarith
lemma uniform_error_sum (B : ℕ → ℕ) (r T : ℕ) (hT : ∀ j < r,T ≤ B (j+1)) :
    (∑ j ∈ Finset.range r,Real.exp (-((B (j+1):ℝ)+1)/2)) ≤
      (r:ℝ)*Real.exp (-((T:ℝ)+1)/2) := by
  calc
    _ ≤ ∑ _j ∈ Finset.range r,Real.exp (-((T:ℝ)+1)/2) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Real.exp_le_exp.mpr
      have hh : (T:ℝ) ≤ B (j+1) := by exact_mod_cast hT j (Finset.mem_range.mp hj)
      linarith
    _ = _ := by simp
lemma finite_uniform_certificate (n d k r T : ℕ) (B : ℕ → ℕ)
    (hbase : n+1 < k*(B 0+1))
    (hstep : ∀ j < r,4*mean n d (B j) ≤ (B (j+1):ℝ)+1)
    (hT : ∀ j < r,T ≤ B (j+1)) (hlast : 0 < B r) :
    1-((r:ℝ)*Real.exp (-((T:ℝ)+1)/2)+3*mean n d (B r)) ≤
      probability n d (fun w => maxLoad n d w ≤ k+r) := by
  have hh := finite_upper_certificate n d k r B hbase hstep hlast
  have hs := uniform_error_sum B r T hT
  linarith
end
end Queelius.BalancedTail

namespace Queelius.BalancedTail
open ABKUFinite
noncomputable section

def beta (n d j : ℕ) : ℝ := (n+1:ℝ)/(4*(2:ℝ)^((d+2)^j))
def clipped (n d T j : ℕ) : ℕ := max T ⌊beta n d j⌋₊
lemma beta_nonneg (n d j : ℕ) : 0 ≤ beta n d j := by unfold beta;positivity
lemma numerical_decay (N q : ℝ) (hN : 0 < N) (hq : 0 < q) (D : ℕ) (hD : 2 ≤ D) :
    4*N*((N/(4*q))/N)^D ≤ N/(4*q^D) := by
  have hcancel : (N/(4*q))/N=1/(4*q) := by field_simp <;> ring
  rw [hcancel,one_div_pow,mul_pow,mul_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hp : (16:ℝ) ≤ 4^D := by
    have hh := pow_le_pow_right₀ (show (1:ℝ) ≤ 4 by norm_num) hD
    norm_num at hh ⊢
    exact hh
  have hh := mul_le_mul_of_nonneg_right hp (show 0 ≤ N*q^D by positivity)
  nlinarith
lemma beta_step (n d j : ℕ) :
    4*(n+1:ℝ)*(beta n d j/(n+1:ℝ))^(d+2) ≤ beta n d (j+1) := by
  have he : (2:ℝ)^((d+2)^(j+1))=((2:ℝ)^((d+2)^j))^(d+2) := by
    rw [pow_succ,pow_mul]
  change 4*(n+1:ℝ)*(((n+1:ℝ)/(4*(2:ℝ)^((d+2)^j)))/(n+1:ℝ))^(d+2) ≤
    (n+1:ℝ)/(4*(2:ℝ)^((d+2)^(j+1)))
  rw [he]
  exact numerical_decay (n+1:ℝ) _ (by positivity) (by positivity) (d+2) (by omega)
lemma clipped_step (n d T j : ℕ) (hT : 4*mean n d T ≤ (T:ℝ)+1) :
    4*mean n d (clipped n d T j) ≤ (clipped n d T (j+1):ℝ)+1 := by
  by_cases hj : ⌊beta n d j⌋₊ ≤ T
  · have he : clipped n d T j=T := max_eq_left hj
    rw [he]
    exact hT.trans (by exact_mod_cast Nat.add_le_add_right (Nat.le_max_left T ⌊beta n d (j+1)⌋₊) 1)
  · have he : clipped n d T j=⌊beta n d j⌋₊ := max_eq_right (by omega)
    have hf := Nat.floor_le (beta_nonneg n d j)
    have hp : ((⌊beta n d j⌋₊:ℝ)/(n+1:ℝ))^(d+2) ≤ (beta n d j/(n+1:ℝ))^(d+2) := by
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div_of_nonneg_right hf (by positivity)
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 4*(n+1:ℝ) by positivity)
    have hn := beta_step n d j
    have hnext := Nat.lt_floor_add_one (beta n d (j+1))
    have hmax : (⌊beta n d (j+1)⌋₊:ℝ) ≤ clipped n d T (j+1) := by
      exact_mod_cast Nat.le_max_right T ⌊beta n d (j+1)⌋₊
    rw [he]
    unfold mean
    nlinarith
lemma clipped_base (n d T : ℕ) : n+1 < 16*(clipped n d T 0+1) := by
  have hf := Nat.lt_floor_add_one (beta n d 0)
  have hm : (⌊beta n d 0⌋₊:ℝ) ≤ clipped n d T 0 := by
    exact_mod_cast Nat.le_max_right T ⌊beta n d 0⌋₊
  have he : beta n d 0=(n+1:ℝ)/8 := by norm_num [beta]
  rw [he] at hf hm
  have hh : (n+1:ℝ) < 16*((clipped n d T 0:ℝ)+1) := by linarith
  exact_mod_cast hh
lemma clipped_finish (n d T r : ℕ) (hr : beta n d r ≤ T) : clipped n d T r=T := by
  apply max_eq_left
  exact Nat.floor_le_of_le hr
lemma explicit_finite_upper (n d T r : ℕ) (hTpos : 0 < T)
    (hT : 4*mean n d T ≤ (T:ℝ)+1) (hr : beta n d r ≤ T) :
    1-((r:ℝ)*Real.exp (-((T:ℝ)+1)/2)+3*mean n d T) ≤
      probability n d (fun w => maxLoad n d w ≤ 16+r) := by
  have hh := finite_uniform_certificate n d 16 r T (clipped n d T)
    (clipped_base n d T) (fun j hj => clipped_step n d T j hT)
    (fun j hj => Nat.le_max_left _ _) (by rw [clipped_finish n d T r hr];exact hTpos)
  simpa only [clipped_finish n d T r hr] using hh
end
end Queelius.BalancedTail

namespace Queelius.BalancedTail
open ABKUFinite Queelius.BalancedLayer
noncomputable section

def rounds (n d : ℕ) : ℕ := ⌈center n d⌉₊+2
def cutoff (n : ℕ) : ℕ := ⌈6*Real.log (n+1:ℝ)⌉₊
lemma log_choices_pos (d : ℕ) : 0 < Real.log (d+2:ℝ) := Real.log_pos (by have hh : (0:ℝ) ≤ d := Nat.cast_nonneg d;linarith)
lemma center_nonneg (n d : ℕ) (hlog : 1 ≤ Real.log (n+1:ℝ)) : 0 ≤ center n d := by
  exact div_nonneg (Real.log_nonneg hlog) (log_choices_pos d).le
lemma round_bound (n d : ℕ) (hlog : 1 ≤ Real.log (n+1:ℝ)) :
    (rounds n d:ℝ) ≤ center n d+3 := by
  have hh := Nat.ceil_lt_add_one (center_nonneg n d hlog)
  simp only [rounds,Nat.cast_add,Nat.cast_ofNat]
  linarith
lemma center_power (n d : ℕ) (hlog : 1 ≤ Real.log (n+1:ℝ)) :
    Real.log (n+1:ℝ) ≤ (d+2:ℝ)^⌈center n d⌉₊ := by
  have hc := Nat.le_ceil (center n d)
  change Real.log (Real.log (n+1:ℝ))/Real.log (d+2:ℝ) ≤ _ at hc
  have hmul := (div_le_iff₀ (log_choices_pos d)).mp hc
  have hh := Real.exp_le_exp.mpr hmul
  rw [Real.exp_log (by linarith : 0 < Real.log (n+1:ℝ)),Real.exp_nat_mul,
    Real.exp_log (by positivity : 0 < (d+2:ℝ))] at hh
  exact hh
lemma round_power (n d : ℕ) (hlog : 1 ≤ Real.log (n+1:ℝ)) :
    4*Real.log (n+1:ℝ) ≤ (d+2:ℝ)^(rounds n d) := by
  have hh := center_power n d hlog
  have hD : (4:ℝ) ≤ (d+2:ℝ)^2 := by nlinarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have hpow : 0 ≤ (d+2:ℝ)^⌈center n d⌉₊ := by positivity
  have hmul := mul_le_mul_of_nonneg_left hD hpow
  simp only [rounds,pow_add]
  nlinarith
lemma round_endpoint (n d : ℕ) (hlog : 1 ≤ Real.log (n+1:ℝ)) : beta n d (rounds n d) ≤ 1 := by
  have hp := round_power n d hlog
  have hq : (n+1:ℝ) ≤ (2:ℝ)^((d+2)^(rounds n d)) := by
    have htwo : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hnon : 0 ≤ (d+2:ℝ)^(rounds n d) := by positivity
    have hmul := mul_le_mul_of_nonneg_left htwo hnon
    have he : Real.log (n+1:ℝ) ≤ ((d+2)^(rounds n d):ℝ)*Real.log 2 := by
      push_cast
      nlinarith
    have hh := Real.exp_le_exp.mpr he
    have hcast : (d+2:ℝ)^(rounds n d)=(((d+2)^(rounds n d):ℕ):ℝ) := by norm_cast
    rw [hcast] at hh
    rw [Real.exp_log (by positivity : 0 < (n+1:ℝ)),Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0:ℝ) < 2)] at hh
    exact hh
  unfold beta
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [show 0 ≤ (2:ℝ)^((d+2)^(rounds n d)) by positivity]
lemma cutoff_positive (n : ℕ) (hlog : 1 ≤ Real.log (n+1:ℝ)) : 0 < cutoff n := by
  have hh := Nat.le_ceil (6*Real.log (n+1:ℝ))
  change 6*Real.log (n+1:ℝ) ≤ (cutoff n:ℝ) at hh
  exact_mod_cast (show (0:ℝ) < cutoff n by linarith)
lemma mean_square (n d B : ℕ) (hB : (B:ℝ) ≤ n+1) :
    mean n d B ≤ (B:ℝ)^2/(n+1:ℝ) := by
  have hp := pow_le_pow_of_le_one (show 0 ≤ (B:ℝ)/(n+1:ℝ) by positivity)
    ((div_le_one (by positivity : 0 < (n+1:ℝ))).mpr hB) (show 2 ≤ d+2 by omega)
  have hh := mul_le_mul_of_nonneg_left hp (show (0:ℝ) ≤ n+1 by positivity)
  unfold mean
  apply hh.trans_eq
  field_simp
lemma cutoff_stable (n d T : ℕ) (hT : 4*(T:ℝ) ≤ n+1) :
    4*mean n d T ≤ (T:ℝ)+1 := by
  have hm := mean_square n d T (by linarith [(Nat.cast_nonneg T : (0:ℝ) ≤ T)])
  have hcross := mul_le_mul_of_nonneg_left hT (show (0:ℝ) ≤ T by positivity)
  have hdiv : 4*(T:ℝ)^2/(n+1:ℝ) ≤ T := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hm4 := mul_le_mul_of_nonneg_left hm (show (0:ℝ) ≤ 4 by norm_num)
  rw [← mul_div_assoc] at hm4
  linarith
lemma centered_finite_upper (n d : ℕ) (hlog : 1 ≤ Real.log (n+1:ℝ))
    (hstable : 4*(cutoff n:ℝ) ≤ n+1) :
    1-((rounds n d:ℝ)*Real.exp (-((cutoff n:ℝ)+1)/2)+3*(cutoff n:ℝ)^2/(n+1:ℝ)) ≤
      probability n d (fun w => (maxLoad n d w:ℝ) ≤ center n d+19) := by
  have hpos := cutoff_positive n hlog
  have hh := explicit_finite_upper n d (cutoff n) (rounds n d) hpos (cutoff_stable n d _ hstable)
    ((round_endpoint n d hlog).trans (by exact_mod_cast hpos))
  have hm := mean_square n d (cutoff n) (by linarith [(Nat.cast_nonneg (cutoff n) : (0:ℝ) ≤ cutoff n)])
  have hp := probability_mono n d (fun w => maxLoad n d w ≤ 16+rounds n d)
    (fun w => (maxLoad n d w:ℝ) ≤ center n d+19) (by
      intro w hw
      have hc : (maxLoad n d w:ℝ) ≤ 16+(rounds n d:ℝ) := by exact_mod_cast hw
      linarith [round_bound n d hlog])
  have hm3 := mul_le_mul_of_nonneg_left hm (show (0:ℝ) ≤ 3 by norm_num)
  rw [← mul_div_assoc] at hm3
  linarith
end
end Queelius.BalancedTail

namespace Queelius.BalancedTail
open ABKUFinite Queelius.BalancedLayer Filter
open scoped Topology
noncomputable section

def analyticError (x : ℝ) : ℝ := ((2*Real.log x+3)+3*(6*Real.log x+1)^2)/x
lemma analytic_error_limit : Tendsto analyticError atTop (𝓝 0) := by
  have h1 := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 := (isLittleO_log_rpow_rpow_atTop 2 (s:=1) (by norm_num)).tendsto_div_nhds_zero
  simp only [Real.rpow_two,Real.rpow_one] at h2
  have h0 : Tendsto (fun x : ℝ => 1/x) atTop (𝓝 0) := by simpa only [one_div] using tendsto_inv_atTop_zero
  have hh := (h2.const_mul 108).add ((h1.const_mul 38).add (h0.const_mul 6))
  have he : analyticError=(fun x : ℝ => 108*(Real.log x^2/x)+(38*(Real.log x/x)+6*(1/x))) := by
    funext x;unfold analyticError;simp only [div_eq_mul_inv];ring
  rw [he]
  simpa only [mul_zero,zero_add,id_eq] using hh
lemma cutoff_ratio_limit : Tendsto (fun x : ℝ => (6*Real.log x+1)/x) atTop (𝓝 0) := by
  have h1 := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h0 : Tendsto (fun x : ℝ => 1/x) atTop (𝓝 0) := by simpa only [one_div] using tendsto_inv_atTop_zero
  have hh := (h1.const_mul 6).add h0
  have he : (fun x : ℝ => (6*Real.log x+1)/x)=(fun x : ℝ => 6*(Real.log x/x)+1/x) := by
    funext x;ring
  rw [he]
  simpa only [mul_zero,zero_add,id_eq] using hh
lemma center_crude (n d : ℕ) (hlog : 1 ≤ Real.log (n+1:ℝ)) :
    center n d ≤ 2*Real.log (n+1:ℝ) := by
  have hD : (1:ℝ)/2 ≤ Real.log (d+2:ℝ) := by
    have hh := Real.log_le_log (show (0:ℝ) < 2 by norm_num) (show (2:ℝ) ≤ d+2 by have h : (0:ℝ) ≤ d := Nat.cast_nonneg d;linarith)
    linarith [Real.log_two_gt_d9]
  have hl := Real.log_le_sub_one_of_pos (show 0 < Real.log (n+1:ℝ) by linarith)
  unfold center
  apply (div_le_iff₀ (log_choices_pos d)).mpr
  have hh := mul_le_mul_of_nonneg_left hD (show 0 ≤ 2*Real.log (n+1:ℝ) by linarith)
  linarith
lemma finite_error_bound (n d : ℕ) (hlog : 1 ≤ Real.log (n+1:ℝ)) :
    (rounds n d:ℝ)*Real.exp (-((cutoff n:ℝ)+1)/2)+3*(cutoff n:ℝ)^2/(n+1:ℝ) ≤
      analyticError (n+1:ℝ) := by
  have hN : 0 < (n+1:ℝ) := by positivity
  have hT := Nat.le_ceil (6*Real.log (n+1:ℝ))
  change 6*Real.log (n+1:ℝ) ≤ (cutoff n:ℝ) at hT
  have hTb := Nat.ceil_lt_add_one (show 0 ≤ 6*Real.log (n+1:ℝ) by linarith)
  change (cutoff n:ℝ) < 6*Real.log (n+1:ℝ)+1 at hTb
  have hr : (rounds n d:ℝ) ≤ 2*Real.log (n+1:ℝ)+3 := by
    linarith [round_bound n d hlog,center_crude n d hlog]
  have he : Real.exp (-((cutoff n:ℝ)+1)/2) ≤ 1/(n+1:ℝ) := by
    have hh := Real.exp_le_exp.mpr (show -((cutoff n:ℝ)+1)/2 ≤ -Real.log (n+1:ℝ) by linarith)
    simpa only [Real.exp_neg,Real.exp_log hN,one_div] using hh
  have hp := mul_le_mul hr he (Real.exp_nonneg _) (show 0 ≤ 2*Real.log (n+1:ℝ)+3 by linarith)
  have hsq : (cutoff n:ℝ)^2 ≤ (6*Real.log (n+1:ℝ)+1)^2 := by
    apply pow_le_pow_left₀ (by positivity) hTb.le
  have hs := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (show (0:ℝ) ≤ 3 by norm_num)) hN.le
  have hh := add_le_add hp hs
  simpa only [mul_one_div,← add_div,analyticError] using hh
lemma upper (d : ℕ) : Upper d := by
  refine ⟨19,by norm_num,?_⟩
  intro ε hε
  have hevent : ∀ᶠ x : ℝ in atTop,analyticError x < ε :=
    analytic_error_limit.eventually (eventually_lt_nhds hε)
  have hsevent : ∀ᶠ x : ℝ in atTop,(6*Real.log x+1)/x < (1:ℝ)/4 :=
    cutoff_ratio_limit.eventually (eventually_lt_nhds (by norm_num))
  obtain ⟨R,he⟩ := eventually_atTop.mp hevent
  obtain ⟨S,hs⟩ := eventually_atTop.mp hsevent
  let M := max (max R S) (Real.exp 1)
  refine ⟨⌈M⌉₊,?_⟩
  intro n hn
  have hceil : M ≤ (n:ℝ) := (Nat.le_ceil M).trans (by exact_mod_cast hn)
  have hM : M ≤ (n+1:ℝ) := by linarith
  have hR : R ≤ (n+1:ℝ) := (le_max_left R S).trans ((le_max_left (max R S) (Real.exp 1)).trans hM)
  have hS : S ≤ (n+1:ℝ) := (le_max_right R S).trans ((le_max_left (max R S) (Real.exp 1)).trans hM)
  have hExp : Real.exp 1 ≤ (n+1:ℝ) := (le_max_right (max R S) (Real.exp 1)).trans hM
  have hN : 0 < (n+1:ℝ) := by positivity
  have hlog : 1 ≤ Real.log (n+1:ℝ) := (Real.le_log_iff_exp_le hN).mpr hExp
  have hratio := hs (n+1:ℝ) hS
  have hcross := (div_lt_iff₀ hN).mp hratio
  have hT := Nat.ceil_lt_add_one (show 0 ≤ 6*Real.log (n+1:ℝ) by linarith)
  change (cutoff n:ℝ) < 6*Real.log (n+1:ℝ)+1 at hT
  have hstable : 4*(cutoff n:ℝ) ≤ n+1 := by linarith
  have hp := centered_finite_upper n d hlog hstable
  have hb := finite_error_bound n d hlog
  have hsmall := he (n+1:ℝ) hR
  linarith
end
end Queelius.BalancedTail

theorem solution : (
  ∀ (d : Nat), ABKUFinite.Upper d
) := @Queelius.BalancedTail.upper
