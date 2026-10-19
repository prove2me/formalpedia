-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
-- name    : OAI_GroupTheory_Kervaire_PermutationCycles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:01:28.169115+00:00
-- url     : https://prove2.me/theorems/ba3ef486-726a-45e6-b965-46d357786ddd
-- title:
--   Cycles of a permutation of darts
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   For a permutation $\sigma$ of a finite set $D$ of darts:
--
--   1. **Cycles.** The quotient of $D$ by the relation of lying in the same cycle, and the number of cycles $c(\sigma)$, fixed points included.
--   2. **Cycle lists.** The list of a cycle starting at $x$, which is $[x]$ for a fixed point, and the bijection between pairs (cycle, position) and $D$.
--
--   Composing with a transposition $(x\ y)$ merges two cycles when $x,y$ lie in different cycles, and splits one when they lie in the same cycle:
--   $$
--   c\bigl((x\ y)\sigma\bigr)=c(\sigma)\mp1 .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/PermutationCycles.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/PermutationCycles.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Kervaire mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

abbrev Cycles (σ : Equiv.Perm D) := Quotient (SameCycle.setoid σ)
def numCycles (σ : Equiv.Perm D) : ℕ := Fintype.card (Cycles σ)
def cycleList (σ : Equiv.Perm D) (x : D) : List D :=
  if σ x = x then [x] else σ.toList x

lemma cycleList_nodup (σ : Equiv.Perm D) (x : D) : (cycleList σ x).Nodup := by
  by_cases hx : σ x = x
  · simp [cycleList,hx]
  · simpa only [cycleList,ite_eq_right hx] using σ.nodup_toList x
lemma mem_cycleList (σ : Equiv.Perm D) (x y : D) : y ∈ cycleList σ x ↔ σ.SameCycle x y := by
  by_cases hx : σ x = x
  · simp only [cycleList,ite_eq_left hx,List.mem_singleton]
    exact ⟨fun h ↦ h ▸ SameCycle.rfl,fun h ↦ (h.eq_of_left hx).symm⟩
  · simp [cycleList,hx,Equiv.Perm.mem_toList_iff,Equiv.Perm.mem_support]
lemma class_mem_cycleList (σ : Equiv.Perm D) (z : Cycles σ) (x : D) :
    x ∈ cycleList σ z.out ↔ Quotient.mk _ x = z := by
  rw [mem_cycleList]
  exact ⟨fun h ↦ (Quotient.sound h.symm).trans z.out_eq,
    fun h ↦ (Quotient.exact (h.trans z.out_eq.symm)).symm⟩

def cycleEquiv (σ : Equiv.Perm D) : (Σ z : Cycles σ, Fin (cycleList σ z.out).length) ≃ D :=
  Equiv.ofBijective (fun p ↦ (cycleList σ p.1.out)[p.2.val]) (by
    constructor
    · rintro ⟨z,i⟩ ⟨w,j⟩ h
      have hi : Quotient.mk _ ((cycleList σ z.out)[i.val]) = z :=
        (class_mem_cycleList σ z _).mp (List.getElem_mem i.isLt)
      have hj : Quotient.mk _ ((cycleList σ w.out)[j.val]) = w :=
        (class_mem_cycleList σ w _).mp (List.getElem_mem j.isLt)
      have hz : z = w := hi.symm.trans ((congrArg (Quotient.mk _) h).trans hj)
      subst w
      have hij : i = j := (List.nodup_iff_injective_getElem.mp (cycleList_nodup σ z.out)) h
      subst j
      rfl
    · intro x
      let z : Cycles σ := Quotient.mk _ x
      have hx : x ∈ cycleList σ z.out := (class_mem_cycleList σ z x).mpr rfl
      obtain ⟨i,hi,hix⟩ := List.getElem_of_mem hx
      exact ⟨⟨z,⟨i,hi⟩⟩,hix⟩)

lemma sameCycle_map_eq {B : Type*} (σ : Equiv.Perm D) (f : D → B)
    (hf : ∀ d, f (σ d) = f d) {x y : D} (h : σ.SameCycle x y) : f x = f y := by
  obtain ⟨n,_,_,rfl⟩ := h.exists_pow_eq σ
  suffices ∀ n : ℕ, f ((σ^n) x) = f x from (this n).symm
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pow_succ',mul_apply,hf] using ih

omit [Fintype D] in
lemma formPerm_cut (x y : D) (l m : List D) (h : (x :: (l ++ y :: m)).Nodup) :
    swap x y * (x :: (l ++ y :: m)).formPerm = (x :: l).formPerm * (y :: m).formPerm := by
  induction l generalizing x with
  | nil => simp [List.formPerm_cons_cons]
  | cons a l ih =>
    have hyx : y ≠ x := fun he ↦ h.notMem (by simp [he])
    have hya : y ≠ a := fun he ↦ h.of_cons.notMem (by simp [he])
    have hc : swap x y * swap x a = swap x a * swap a y := by
      rw [swap_mul_eq_mul_swap]
      simp only [swap_inv,swap_apply_left,swap_apply_of_ne_of_ne hyx hya]
    change swap x y * (swap x a * (a :: (l ++ y :: m)).formPerm) =
      (swap x a * (a :: l).formPerm) * (y :: m).formPerm
    rw [← mul_assoc,hc,mul_assoc,ih a h.of_cons,mul_assoc]

omit [Fintype D] [DecidableEq D] in
lemma mem_formPerm_of_fixed (l : List D) (σ : Equiv.Perm D)
    (h : ∀ x ∈ l, σ x = x) (x : D) : σ x ∈ l ↔ x ∈ l := by
  constructor
  · intro hx
    have he := h (σ x) hx
    have hh : σ x = x := σ.injective he
    rwa [hh] at hx
  · intro hx
    rwa [h x hx]

lemma sameCycle_swap_separates (σ : Equiv.Perm D) {x y : D}
    (hne : x ≠ y) (hxy : σ.SameCycle x y) :
    ¬ (swap x y * σ).SameCycle x y := by
  have hx : σ x ≠ x := fun hx ↦ hne (hxy.eq_of_left hx)
  have hs : x ∈ σ.support := Equiv.Perm.mem_support.mpr hx
  have hl : σ.toList x ≠ [] := fun he ↦ (Equiv.Perm.toList_eq_nil_iff.mp he) hs
  obtain ⟨a,t,ht⟩ := List.exists_cons_of_ne_nil hl
  have ha : a = x := by
    have hh := σ.toList_getElem_zero x hs
    simpa only [ht,List.getElem_cons_zero] using hh
  subst a
  have hy : y ∈ t := by
    have hh : y ∈ σ.toList x := Equiv.Perm.mem_toList_iff.mpr ⟨hxy,hs⟩
    simpa only [ht,List.mem_cons,or_iff_right (Ne.symm hne)] using hh
  obtain ⟨l,m,hm⟩ := List.mem_iff_append.mp hy
  subst t
  have hd : (x :: (l ++ y :: m)).Nodup := ht ▸ σ.nodup_toList x
  have hcut := formPerm_cut x y l m hd
  have hL : (x::l).Disjoint (y::m) := by
    intro a ha hb
    exact (List.nodup_append.mp (show ((x::l)++(y::m)).Nodup from hd)).2.2 a ha a hb rfl
  let f : D → Prop := fun d ↦ d ∈ x::l
  have hmem (d : D) : (x::l).formPerm ((y::m).formPerm d) ∈ x::l ↔ d ∈ x::l := by
    rw [List.formPerm_mem_iff_mem]
    exact mem_formPerm_of_fixed (x::l) (y::m).formPerm
      (fun z hz ↦ List.formPerm_apply_of_notMem (fun hzz ↦ hL hz hzz)) d
  have hi (d : D) : f ((swap x y * σ) d) = f d := by
    apply propext
    change (swap x y * σ) d ∈ x::l ↔ d ∈ x::l
    by_cases hc : d ∈ σ.toList x
    · have he : σ d = (x :: (l ++ y :: m)).formPerm d := by
        rw [← ht,σ.formPerm_toList]
        exact (SameCycle.cycleOf_apply (Equiv.Perm.mem_toList_iff.mp hc).1).symm
      change swap x y (σ d) ∈ x::l ↔ _
      rw [he,← Equiv.Perm.mul_apply,hcut]
      exact hmem d
    · have hx' : σ d ≠ x := by
        intro he
        apply hc
        rw [Equiv.Perm.mem_toList_iff]
        exact ⟨(sameCycle_apply_right.mp (he ▸ SameCycle.rfl)),hs⟩
      have hy' : σ d ≠ y := by
        intro he
        apply hc
        rw [Equiv.Perm.mem_toList_iff]
        exact ⟨sameCycle_apply_right.mp (he ▸ hxy),hs⟩
      rw [mul_apply,swap_apply_of_ne_of_ne hx' hy']
      have hdn : d ∉ x::l := fun hd' ↦ hc (ht ▸ (List.mem_append_left (y::m) hd'))
      have hσn : σ d ∉ x::l := by
        intro hh
        apply hc
        rw [Equiv.Perm.mem_toList_iff]
        have hm' : σ d ∈ σ.toList x := ht ▸ (List.mem_append_left (y::m) hh)
        exact ⟨sameCycle_apply_right.mp (Equiv.Perm.mem_toList_iff.mp hm').1,hs⟩
      simp only [hdn,hσn]
  intro hn
  have he := sameCycle_map_eq (swap x y * σ) f hi hn
  have hfx : f x := by simp [f]
  have hfy : ¬ f y := fun hy ↦ hL hy (by simp)
  exact hfy (he ▸ hfx)
end
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma sameCycle_swap_merges (σ : Equiv.Perm D) {x y : D}
    (hxy : ¬ σ.SameCycle x y) : (swap x y * σ).SameCycle x y := by
  have hne : x ≠ y := fun he ↦ hxy (he ▸ SameCycle.rfl)
  have hex : ∃ n : ℕ, 0 < n ∧ (σ^n) x = x :=
    ⟨orderOf σ,orderOf_pos σ,by rw [pow_orderOf_eq_one]; rfl⟩
  let n := Nat.find hex
  have hn : 0 < n ∧ (σ^n) x = x := Nat.find_spec hex
  have hmin (i : ℕ) (hi : i < n) (hi0 : 0 < i) : (σ^i) x ≠ x := by
    intro he
    exact Nat.find_min hex hi ⟨hi0,he⟩
  have hyp (i : ℕ) : (σ^i) x ≠ y := fun he ↦ hxy ⟨i,by simpa using he⟩
  have hp (i : ℕ) (hi : i < n) : ((swap x y * σ)^i) x = (σ^i) x := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [pow_succ',mul_apply,ih (by omega)]
      change swap x y (σ ((σ^i) x)) = _
      have he : σ ((σ^i) x) = (σ^(i+1)) x := by rw [pow_succ',mul_apply]
      rw [he,swap_apply_of_ne_of_ne (hmin (i+1) hi (by omega)) (hyp (i+1))]
  have hlast : ((swap x y * σ)^n) x = y := by
    obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hn.1.ne'
    rw [hm,pow_succ',mul_apply,hp m (by omega)]
    change swap x y (σ ((σ^m) x)) = y
    have he : σ ((σ^m) x) = x := by simpa only [hm,pow_succ',mul_apply] using hn.2
    rw [he,swap_apply_left]
  exact ⟨n,by simpa using hlast⟩

omit [Fintype D] in
lemma map_swap_eq {B : Type*} (f : D → B) {x y : D} (hxy : f x = f y) (d : D) :
    f (swap x y d) = f d := by
  by_cases hx : d = x
  · subst d; simpa using hxy.symm
  by_cases hy : d = y
  · subst d; simpa using hxy
  rw [swap_apply_of_ne_of_ne hx hy]

lemma sameCycle_transfer (σ : Equiv.Perm D) {x y : D}
    (hxy : (swap x y * σ).SameCycle x y) {d e : D} (hde : σ.SameCycle d e) :
    (swap x y * σ).SameCycle d e := by
  let τ := swap x y * σ
  let f : D → Cycles τ := Quotient.mk _
  have hfτ (a : D) : f (τ a) = f a := Quotient.sound (SameCycle.rfl.apply_left)
  have hfxy : f x = f y := Quotient.sound hxy
  apply Quotient.exact (s := SameCycle.setoid τ)
  exact sameCycle_map_eq σ f (fun a ↦ by
    have he : σ a = swap x y (τ a) := by simp [τ]
    rw [he,map_swap_eq f hfxy,hfτ]) hde

omit [DecidableEq D] in
lemma numCycles_eq_card {B : Type*} [Fintype B] (σ : Equiv.Perm D) (f : D → B)
    (hfs : Function.Surjective f) (hf : ∀ x y, σ.SameCycle x y ↔ f x = f y) :
    numCycles σ = Fintype.card B := by
  let E : Cycles σ ≃ B := Equiv.ofBijective
    (Quotient.lift f (fun x y h ↦ (hf x y).mp h)) (by
      constructor
      · intro x y
        induction x using Quotient.inductionOn with | h x =>
          induction y using Quotient.inductionOn with | h y =>
            exact fun he ↦ Quotient.sound ((hf x y).mpr he)
      · intro b
        obtain ⟨d,rfl⟩ := hfs b
        exact ⟨Quotient.mk _ d,rfl⟩)
  exact Fintype.card_congr E

lemma numCycles_swap_merge (σ : Equiv.Perm D) {x y : D}
    (hxy : ¬ σ.SameCycle x y) : numCycles (swap x y * σ) + 1 = numCycles σ := by
  let τ := swap x y * σ
  let C := Cycles σ
  let q : D → C := Quotient.mk _
  have hq : q x ≠ q y := fun he ↦ hxy (Quotient.exact he)
  let B := {z : C // z ≠ q y}
  let f : D → B := fun d ↦ if hd : q d = q y then ⟨q x,hq⟩ else ⟨q d,hd⟩
  have hfval (d : D) : (f d).val = if q d = q y then q x else q d := by
    dsimp [f]
    split <;> simp_all
  have hfq (d e : D) (he : q d = q e) : f d = f e := by
    apply Subtype.ext
    simp only [hfval,he]
  have hfσ (d : D) : f (σ d) = f d := hfq _ _ (Quotient.sound SameCycle.rfl.apply_left)
  have hfxy : f x = f y := by
    apply Subtype.ext
    simp [hfval,hq]
  have hfs : Function.Surjective f := by
    intro ⟨z,hz⟩
    refine ⟨z.out,?_⟩
    apply Subtype.ext
    simp only [hfval]
    have he : q z.out = z := z.out_eq
    rw [he,ite_eq_right hz]
  have hτ : τ.SameCycle x y := sameCycle_swap_merges σ hxy
  have hf (d e : D) : τ.SameCycle d e ↔ f d = f e := by
    constructor
    · exact sameCycle_map_eq τ f (fun a ↦ by
        change f (swap x y (σ a)) = f a
        rw [map_swap_eq f hfxy,hfσ])
    · intro he
      have hv := congrArg Subtype.val he
      simp only [hfval] at hv
      by_cases hd : q d = q y <;> by_cases he : q e = q y
      · exact sameCycle_transfer σ hτ (Quotient.exact (hd.trans he.symm))
      · simp only [ite_eq_left hd,ite_eq_right he] at hv
        exact (sameCycle_transfer σ hτ (Quotient.exact hd)).trans
          (hτ.symm.trans (sameCycle_transfer σ hτ (Quotient.exact hv)))
      · simp only [ite_eq_right hd,ite_eq_left he] at hv
        exact (sameCycle_transfer σ hτ (Quotient.exact hv)).trans
          (hτ.trans (sameCycle_transfer σ hτ (Quotient.exact he.symm)))
      · simp only [ite_eq_right hd,ite_eq_right he] at hv
        exact sameCycle_transfer σ hτ (Quotient.exact hv)
  rw [numCycles_eq_card τ f hfs hf]
  change Fintype.card {z : C // z ≠ q y} + 1 = Fintype.card C
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_unique]
  have hc : 0 < Fintype.card C := Fintype.card_pos_iff.mpr ⟨q x⟩
  omega

lemma numCycles_swap_split (σ : Equiv.Perm D) {x y : D} (hne : x ≠ y)
    (hxy : σ.SameCycle x y) : numCycles (swap x y * σ) = numCycles σ + 1 := by
  have h := numCycles_swap_merge (swap x y * σ) (sameCycle_swap_separates σ hne hxy)
  simpa only [← mul_assoc,swap_mul_self,one_mul] using h.symm
end KervaireRibbon

end

end OAI


