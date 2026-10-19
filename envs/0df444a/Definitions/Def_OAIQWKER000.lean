-- Prove2me | Definitions.Def_OAIQWKER000
-- name    : OAIQWKER000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T21:32:51.521504+00:00
-- url     : https://prove2.me/theorems/3a0e8e24-fd46-4da3-816a-d0c7f72a7de8
-- title:
--   OpenAI Kervaire split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof of `OAI.Kervaire.coefficient_injective`: for every group $A$ and every unimodular word $w$ in $A * \langle t\rangle$, the coefficient map $A \to (A * \langle t\rangle)/\langle\langle w\rangle\rangle$ is injective. That is the unimodular case of the Kervaire–Laudenbach conjecture, which gives the Kervaire conjecture.
--
--   The bundle holds OpenAI's Lean definitions, structures and instances from `lean/OAI/GroupTheory/Kervaire` (OpenAI, *The Kervaire theorem for groups*, OpenAI Math Release, September 24, 2026, result family 256, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with OpenAI's `@[simp]` lemmas about them. Among them:
--   - the Hilbert space $\ell^2(D \times A)$ with its operators (`Space`, `Operator`);
--   - the spectral phase of a unitary and its trace (`phase`, `vectorPhase`, `sumPhase`, `KervaireMatrix.phase`);
--   - labelled and weighted shifts (`labelledShift`, `weightedShift`, `scalarTensor`);
--   - the slots and cyclic orders of word disks (`Slot`, `successor`, `labels`, `S`);
--   - the mixing matrices (`mixingMatrix`) and the fixed-space dimension (`fixedDim`);
--   - ribbon permutations and planarity (`planar`, `components`).
--
--   The bundle also contains the lemmas those definitions use in their bodies. Planarity of the ribbon permutations rests on the Euler inequality for a pair of permutations (`euler_inequality`). Here that lemma is a three-line bridge from the published standalone statement `OAI.Kervaire.perm_euler_inequality`, which the bundle imports. So that statement, and its proof, must be live before this bundle is published.
--
--   The definitions of the published goal (`WordGroup`, `exponentSum`, `Unimodular`, `relatorClosure`, `RelatorQuotient`, `coefficientMap`) are not part of this bundle: the solutions import them from the published bundle `Def_Kervaire`. The cycle and component counts `numCycles`, `classes`, `edgePerm` and `attachEdges` come from the bundle `OAIQWKERK000` of the Euler-inequality statement, which this bundle imports.
--
--   The theorems the definitions do not need are proved in the four solutions of this split. Three prove the published intermediate statements `OAI.KervaireBoundary.phase_boundary_cycles`, `OAI.KervaireMixing.phase_upper_of_fixed` and `OAI.KervaireBoundary.boundary_phase_upper`, and the fourth proves `OAI.Kervaire.coefficient_injective` from them. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The Kervaire theorem for groups, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 256; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kervaire-Theorem-for-Groups-September-24-2026/The-Kervaire-Theorem-for-Groups-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/Kervaire at commit adc7f12

import Mathlib
import Definitions.Def_OAIQWKERK000
import Theorems.Thm_OAI_Kervaire_perm_euler_inequality

section
-- module Solutions.OAIQW_KervaireMain.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434
end

section
-- module Solutions.OAIQW_KervaireMain.PermutationCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

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
end

section
-- module Solutions.OAIQW_KervaireMain.Components
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma cycle_le_of_step (σ : Equiv.Perm D) (r : Setoid D) (h : ∀ d, r (σ d) d) :
    SameCycle.setoid σ ≤ r := by
  intro x y hxy
  apply Quotient.exact (s := r)
  exact sameCycle_map_eq σ (Quotient.mk r) (fun d ↦ Quotient.sound (h d)) hxy

lemma cycle_swap_le (r : Setoid D) (x y : D) (hxy : r x y) :
    SameCycle.setoid (swap x y) ≤ r := by
  apply cycle_le_of_step
  intro d
  by_cases hx : d = x
  · subst d; simpa using r.symm' hxy
  by_cases hy : d = y
  · subst d; simpa using hxy
  rw [swap_apply_of_ne_of_ne hx hy]

lemma joinPair_eq (r : Setoid D) {x y : D} (h : r x y) : joinPair r x y = r :=
  sup_eq_left.mpr (cycle_swap_le r x y h)
omit [Fintype D] in
lemma le_joinPair (r : Setoid D) (x y : D) : r ≤ joinPair r x y := le_sup_left
omit [Fintype D] in
lemma joinPair_rel (r : Setoid D) (x y : D) : joinPair r x y x y := by
  apply (le_sup_right : SameCycle.setoid (swap x y) ≤ joinPair r x y)
  have h : (swap x y).SameCycle x (swap x y x) := SameCycle.rfl.apply_right
  change (swap x y).SameCycle x y
  simpa only [swap_apply_left] using h

lemma classes_joinPair (r : Setoid D) {x y : D} (hxy : ¬ r x y) :
    classes (joinPair r x y) + 1 = classes r := by
  let q : D → Quotient r := Quotient.mk r
  have hq : q x ≠ q y := fun he ↦ hxy (Quotient.exact he)
  let B := {z : Quotient r // z ≠ q y}
  let f : D → B := fun d ↦ if hd : q d = q y then ⟨q x,hq⟩ else ⟨q d,hd⟩
  have hfval (d : D) : (f d).val = if q d = q y then q x else q d := by
    dsimp [f]; split <;> simp_all
  have hfr : r ≤ Setoid.ker f := by
    intro d e h
    apply Subtype.ext
    simp only [hfval,show q d = q e from Quotient.sound h]
  have hfxy : f x = f y := by apply Subtype.ext; simp [hfval,hq]
  have hle : joinPair r x y ≤ Setoid.ker f :=
    sup_le hfr (cycle_swap_le _ x y hfxy)
  have hge : Setoid.ker f ≤ joinPair r x y := by
    intro d e he
    have hv := congrArg Subtype.val he
    simp only [hfval] at hv
    have hr (d e : D) (h : q d = q e) : joinPair r x y d e :=
      le_joinPair r x y (Quotient.exact h)
    have hh := joinPair_rel r x y
    by_cases hd : q d = q y <;> by_cases he : q e = q y
    · exact hr _ _ (hd.trans he.symm)
    · simp only [ite_eq_left hd,ite_eq_right he] at hv
      exact (joinPair r x y).trans' (hr _ _ hd)
        ((joinPair r x y).trans' ((joinPair r x y).symm' hh) (hr _ _ hv))
    · simp only [ite_eq_right hd,ite_eq_left he] at hv
      exact (joinPair r x y).trans' (hr _ _ hv)
        ((joinPair r x y).trans' hh (hr _ _ he.symm))
    · simp only [ite_eq_right hd,ite_eq_right he] at hv
      exact hr _ _ hv
  have hfs : Function.Surjective f := by
    intro ⟨z,hz⟩
    refine ⟨z.out,?_⟩
    apply Subtype.ext
    simp only [hfval]
    have he : q z.out = z := z.out_eq
    rw [he,ite_eq_right hz]
  have hc : classes (joinPair r x y) = Fintype.card B := by
    rw [le_antisymm hle hge]
    exact Fintype.card_congr (Setoid.quotientKerEquivOfSurjective f hfs)
  rw [hc]
  change Fintype.card {z : Quotient r // z ≠ q y} + 1 = Fintype.card (Quotient r)
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_unique]
  have hc : 0 < Fintype.card (Quotient r) := Fintype.card_pos_iff.mpr ⟨q x⟩
  omega

lemma cycles_swap_le (σ : Equiv.Perm D) (r : Setoid D) (h : SameCycle.setoid σ ≤ r)
    (x y : D) : SameCycle.setoid (swap x y * σ) ≤ joinPair r x y := by
  apply cycle_le_of_step
  intro d
  exact (joinPair r x y).trans'
    ((le_sup_right : SameCycle.setoid (swap x y) ≤ joinPair r x y)
      (SameCycle.rfl.apply_left : (swap x y).SameCycle (swap x y (σ d)) (σ d)))
    (le_joinPair r x y (h SameCycle.rfl.apply_left))

end
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
lemma numCycles_one : numCycles (1 : Equiv.Perm D) = Fintype.card D := by
  exact numCycles_eq_card 1 id Function.surjective_id (fun _ _ ↦ sameCycle_one)

omit [DecidableEq D] in
lemma numCycles_conj (σ e : Equiv.Perm D) : numCycles (e*σ*e⁻¹) = numCycles σ := by
  apply numCycles_eq_card (e*σ*e⁻¹) (fun d ↦ (Quotient.mk _ (e⁻¹ d) : Cycles σ))
  · intro z
    exact ⟨e z.out,by simp⟩
  · intro x y
    rw [sameCycle_conj]
    exact @Quotient.eq D (SameCycle.setoid σ) _ _ |>.symm

omit [DecidableEq D] in
lemma numCycles_mul_comm (σ θ : Equiv.Perm D) : numCycles (σ*θ) = numCycles (θ*σ) := by
  have h := numCycles_conj (θ*σ) σ
  simpa only [mul_assoc,mul_inv_cancel,mul_one] using h

lemma cycles_swap_sup (σ : Equiv.Perm D) (x y : D) :
    SameCycle.setoid (swap x y * σ) ⊔ SameCycle.setoid (swap x y) =
      SameCycle.setoid σ ⊔ SameCycle.setoid (swap x y) := by
  apply le_antisymm
  · exact sup_le (cycles_swap_le σ _ le_rfl x y) le_sup_right
  · apply sup_le _ le_sup_right
    have h := cycles_swap_le (swap x y * σ) (SameCycle.setoid (swap x y * σ)) le_rfl x y
    simpa only [← mul_assoc,swap_mul_self,one_mul,joinPair] using h

end KervaireRibbon

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.EulerStd
set_option linter.all false

namespace OAI

namespace KervaireRibbon

open Equiv Equiv.Perm
open scoped Classical

theorem euler_inequality {D : Type*} [Fintype D] [DecidableEq D] (σ θ : Equiv.Perm D) :
    numCycles σ + numCycles θ + numCycles (σ*θ) ≤
      Fintype.card D + 2*classes (SameCycle.setoid σ ⊔ SameCycle.setoid θ) := by
  have h := OAI.Kervaire.perm_euler_inequality σ θ
  simp only [numCycles, classes, Cycles, Fintype.card_eq_nat_card]
  exact h

end KervaireRibbon

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.Suppression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

def erase (σ : Equiv.Perm D) (x : D) : Equiv.Perm D := swap x (σ x) * σ

omit [Fintype D] in
lemma erase_fixed (σ : Equiv.Perm D) (x : D) : erase σ x x = x := by simp [erase]

omit [Fintype D] in
lemma erase_apply (σ : Equiv.Perm D) (x d : D) (hd : d ≠ x) :
    erase σ x d = if σ d = x then σ x else σ d := by
  change swap x (σ x) (σ d) = _
  split_ifs with he
  · rw [he,swap_apply_left]
  · exact swap_apply_of_ne_of_ne he (fun hh ↦ hd (σ.injective hh))

def components (σ θ : Equiv.Perm D) : Setoid D := SameCycle.setoid σ ⊔ SameCycle.setoid θ

def planar (σ θ : Equiv.Perm D) : Prop :=
  numCycles σ + numCycles θ + numCycles (σ*θ) = Fintype.card D + 2*classes (components σ θ)

lemma components_swap_sup (σ θ : Equiv.Perm D) (x y : D) :
    joinPair (components (swap x y * σ) θ) x y = joinPair (components σ θ) x y := by
  unfold joinPair components
  have h := cycles_swap_sup σ x y
  simpa only [sup_right_comm] using congrArg (fun r : Setoid D ↦ r ⊔ SameCycle.setoid θ) h

/-- Splitting a vertex of a planar ribbon permutation preserves planarity.
The proof uses only the finite Euler inequality and the exact cycle split/merge count. -/
lemma planar_vertex_split (σ θ : Equiv.Perm D) {x y : D} (hne : x ≠ y)
    (hxy : σ.SameCycle x y) (hp : planar σ θ) : planar (swap x y * σ) θ := by
  let r := components (swap x y * σ) θ
  have hr : joinPair r x y = components σ θ := by
    dsimp [r]
    rw [components_swap_sup]
    exact joinPair_eq (components σ θ) ((le_sup_left : SameCycle.setoid σ ≤ components σ θ) hxy)
  have hv := numCycles_swap_split σ hne hxy
  by_cases hc : r x y
  · have hre : r = components σ θ := by simpa only [joinPair_eq _ hc] using hr
    have hi := euler_inequality (swap x y * σ) θ
    change _ ≤ _ + 2*classes r at hi
    rw [hre,hv,mul_assoc] at hi
    have hf : ¬ (σ*θ).SameCycle x y := by
      intro hh
      have hn := numCycles_swap_split (σ*θ) hne hh
      unfold planar at hp
      omega
    have hf' := numCycles_swap_merge (σ*θ) hf
    unfold planar at hp ⊢
    change numCycles (swap x y * σ) + numCycles θ + numCycles ((swap x y * σ)*θ) = _ + 2*classes r
    rw [hv,hre,mul_assoc]
    omega
  · have hφle : SameCycle.setoid ((swap x y * σ)*θ) ≤ r := by
      apply cycle_le_of_step
      intro d
      exact r.trans' ((le_sup_left : SameCycle.setoid (swap x y * σ) ≤ r) SameCycle.rfl.apply_left)
        ((le_sup_right : SameCycle.setoid θ ≤ r) SameCycle.rfl.apply_left)
    have hf' := numCycles_swap_merge ((swap x y * σ)*θ) (fun h ↦ hc (hφle h))
    have he : swap x y * ((swap x y * σ)*θ) = σ*θ := by simp [← mul_assoc]
    rw [he] at hf'
    have hcr := classes_joinPair r hc
    rw [hr] at hcr
    unfold planar at hp ⊢
    change _ = _ + 2*classes r
    omega
end
section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma cycles_mul_le (σ θ : Equiv.Perm D) (r : Setoid D)
    (hs : SameCycle.setoid σ ≤ r) (ht : SameCycle.setoid θ ≤ r) :
    SameCycle.setoid (σ*θ) ≤ r := by
  apply cycle_le_of_step
  intro d
  exact r.trans' (hs SameCycle.rfl.apply_left) (ht SameCycle.rfl.apply_left)

/-- Suppress a two-valent vertex, retaining its two darts as isolated markers. -/
def suppress (θ : Equiv.Perm D) (x y : D) : Equiv.Perm D :=
  swap x y * (swap y (θ x) * θ * swap y (θ x))

end
open Equiv Equiv.Perm
open scoped Classical
end KervaireRibbon

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.ComponentFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

abbrev Fiber (r : Setoid D) (c : Quotient r) := {d : D // Quotient.mk r d = c}

def fiberPerm (σ : Equiv.Perm D) (r : Setoid D) (h : SameCycle.setoid σ ≤ r) (c : Quotient r) :
    Equiv.Perm (Fiber r c) :=
  σ.subtypePerm (fun d ↦ by
    have he : Quotient.mk r (σ d) = Quotient.mk r d := Quotient.sound (h SameCycle.rfl.apply_left)
    exact he ▸ Iff.rfl)

omit [DecidableEq D] in
lemma card_fiber_sum (r : Setoid D) :
    (∑ c : Quotient r, Fintype.card (Fiber r c)) = Fintype.card D := by
  simpa only [Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk r))

lemma classes_top {B : Type*} [Fintype B] [Nonempty B] : classes (⊤ : Setoid B) = 1 := by
  let _ : Subsingleton (Quotient (⊤ : Setoid B)) := Quotient.subsingleton_iff.mpr rfl
  exact Fintype.card_eq_one_iff.mpr ⟨Quotient.mk _ (Classical.arbitrary B),fun _ ↦ Subsingleton.elim _ _⟩

end

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
lemma sameCycle_involution (θ : Perm D) (hθ : ∀ d, θ (θ d) = d) (x y : D) :
    θ.SameCycle x y ↔ y = x ∨ y = θ x := by
  constructor
  · intro h
    obtain ⟨n,rfl⟩ := h.exists_nat_pow_eq
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
      rw [pow_succ',mul_apply]
      rcases ih SameCycle.rfl.pow_right with h | h
      · exact Or.inr (congrArg θ h)
      · exact Or.inl ((congrArg θ h).trans (hθ x))
  · rintro (rfl|rfl)
    · exact SameCycle.rfl
    · exact SameCycle.rfl.apply_right

omit [DecidableEq D] in
lemma card_fiber_involution (θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (hne : ∀ d, θ d ≠ d) (c : Cycles θ) : Fintype.card (Fiber (SameCycle.setoid θ) c) = 2 := by
  let d := c.out
  have hd : Quotient.mk (SameCycle.setoid θ) d = c := c.out_eq
  have ht : Quotient.mk (SameCycle.setoid θ) (θ d) = c :=
    (Quotient.sound SameCycle.rfl.apply_left).trans hd
  let f : Bool → Fiber (SameCycle.setoid θ) c := fun b ↦ if b then ⟨θ d,ht⟩ else ⟨d,hd⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have hab' := congrArg Subtype.val hab
      cases a <;> cases b <;> simp only [f,Bool.false_eq_true,ite_false,ite_true] at hab' ⊢
      · exact (hne d hab'.symm).elim
      · exact (hne d hab').elim
    · intro x
      have hx : θ.SameCycle d x.val := Quotient.exact (hd.trans x.property.symm)
      rcases (sameCycle_involution θ hθ _ _).mp hx with he | he
      · exact ⟨false,Subtype.ext he.symm⟩
      · exact ⟨true,Subtype.ext he.symm⟩
  exact (Fintype.card_congr (Equiv.ofBijective f hf)).symm.trans Fintype.card_bool

omit [DecidableEq D] in
lemma numCycles_involution (θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (hne : ∀ d, θ d ≠ d) : 2 * numCycles θ = Fintype.card D := by
  have hh := card_fiber_sum (SameCycle.setoid θ)
  simp only [card_fiber_involution θ hθ hne,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  change 2 * Fintype.card (Cycles θ) = _
  simpa only [Cycles,Nat.mul_comm,Nat.cast_id] using hh

end

open Equiv Equiv.Perm
open scoped Classical
end KervaireRibbon

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.StrongLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace KervaireStrong
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {ι : Type*} {l : Filter ι}
abbrev Operator (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H] := H →L[ℂ] H

def StrongTendsto (T : ι → Operator H) (l : Filter ι) (S : Operator H) : Prop :=
  ∀ ξ, Tendsto (fun i => T i ξ) l (𝓝 (S ξ))

/-- Joint continuity of evaluation for strong convergence on an operator-norm
bounded family. -/
theorem StrongTendsto.apply_variable {T : ι → Operator H} {S : Operator H}
    (h : StrongTendsto T l S) {C : ℝ} (_hC : 0 ≤ C) (hb : ∀ i, ‖T i‖ ≤ C)
    {x : ι → H} {ξ : H} (hx : Tendsto x l (𝓝 ξ)) :
    Tendsto (fun i => T i (x i)) l (𝓝 (S ξ)) := by
  have hzero : Tendsto (fun i => T i (x i - ξ)) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun i => (T i).le_of_opNorm_le (hb i) _)
    have hx' : Tendsto (fun i => ‖x i - ξ‖) l (𝓝 0) := by
      simpa using (hx.sub (tendsto_const_nhds (x := ξ))).norm
    simpa using hx'.const_mul C
  have hs := hzero.add (h ξ)
  simpa only [map_sub, sub_add_cancel, zero_add] using hs

theorem StrongTendsto.mul {T T' : ι → Operator H} {S S' : Operator H}
    (h : StrongTendsto T l S) (h' : StrongTendsto T' l S')
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i, ‖T i‖ ≤ C) :
    StrongTendsto (fun i => T i * T' i) l (S * S') := by
  intro ξ
  exact h.apply_variable hC hb (h' ξ)

theorem StrongTendsto.pow {T : ι → Operator H} {S : Operator H}
    (h : StrongTendsto T l S) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i, ‖T i‖ ≤ C)
    (n : ℕ) : StrongTendsto (fun i => T i ^ n) l (S ^ n) := by
  induction n with
  | zero => intro ξ; simp only [pow_zero]; exact tendsto_const_nhds
  | succ n ih => simpa only [pow_succ'] using h.mul ih hC hb

/-- Exponentiation is strongly continuous on uniformly bounded families. -/
theorem StrongTendsto.exp [CompleteSpace H] {T : ι → Operator H} {S : Operator H}
    (h : StrongTendsto T l S) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i, ‖T i‖ ≤ C) :
    StrongTendsto (fun i => NormedSpace.exp (T i)) l (NormedSpace.exp S) := by
  intro ξ
  let a : ℕ → ℝ := fun n => (n.factorial : ℝ)⁻¹
  have hs (R : Operator H) : HasSum (fun n => a n • ((R ^ n) ξ))
      (NormedSpace.exp R ξ) := by
    simpa [a] using
      ((ContinuousLinearMap.apply ℂ H ξ).restrictScalars ℝ).hasSum
        (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) R)
  have ht := tendsto_tsum_of_dominated_convergence
    ((NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) C).mul_right ‖ξ‖)
    (fun n => (h.pow hC hb n ξ).const_smul (a n)) ?_
  · simpa only [(hs _).tsum_eq] using ht
  · filter_upwards [] with i n
    calc
      ‖a n • ((T i ^ n) ξ)‖ = ‖a n‖ * ‖(T i ^ n) ξ‖ := norm_smul _ _
      _ ≤ ‖a n‖ * (C ^ n * ‖ξ‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', mul_apply_eq_comp]
          exact ((T i).le_of_opNorm_le (hb i) _).trans
            ((mul_le_mul_of_nonneg_left ih hC).trans_eq (by rw [pow_succ']; ring))
      _ = ‖(n.factorial : ℝ)⁻¹ • C ^ n‖ * ‖ξ‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hC n)]
        exact (mul_assoc _ _ _).symm

open scoped ComplexOrder

end KervaireStrong

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.SpectralMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology

namespace KervaireSpectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
abbrev Operator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] := H →L[ℂ] H

/-- Embed a real-valued function into complex-valued functions. -/
def complexify {X : Type*} [TopologicalSpace X] (f : C(X, ℝ)) : C(X, ℂ) :=
  ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

@[simp] theorem complexify_apply {X : Type*} [TopologicalSpace X]
    (f : C(X, ℝ)) (x : X) : complexify f x = (f x : ℂ) := rfl

@[simp] theorem complexify_add {X : Type*} [TopologicalSpace X]
    (f g : C(X, ℝ)) : complexify (f + g) = complexify f + complexify g := by ext; simp [complexify]

@[simp] theorem complexify_smul {X : Type*} [TopologicalSpace X]
    (r : ℝ) (f : C(X, ℝ)) : complexify (r • f) = (r : ℂ) • complexify f := by
  ext; simp [complexify]

/-- A vector functional restricted to the continuous calculus of a normal operator. -/
def vectorFunctional (U : Operator H) [hU : IsStarNormal U] (ξ : H) :
    C_c(spectrum ℂ U, ℝ) →ₚ[ℝ] ℝ := .mk₀ {
  toFun f := (inner ℂ ξ (cfcHom hU (complexify f.toContinuousMap) ξ)).re
  map_add' f g := by
    have hfg : (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap := rfl
    rw [hfg, complexify_add, map_add]
    simp
  map_smul' r f := by
    have hrf : (r • f).toContinuousMap = r • f.toContinuousMap := rfl
    rw [hrf, complexify_smul, map_smul]
    simp
  } (by
    intro f hf
    have hfc : 0 ≤ complexify f.toContinuousMap := by
      intro x
      exact (Complex.zero_le_real).mpr (hf x)
    have hc : 0 ≤ cfcHom hU (complexify f.toContinuousMap) :=
      (cfcHom_nonneg_iff hU).mpr hfc
    exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hc).re_inner_nonneg_right ξ)

/-- The finite scalar spectral measure of a vector, on the actual spectrum. -/
def vectorMeasure (U : Operator H) [IsStarNormal U] (ξ : H) : Measure (spectrum ℂ U) :=
  RealRMK.rieszMeasure (vectorFunctional U ξ)

instance vectorMeasure_finite (U : Operator H) [IsStarNormal U] (ξ : H) :
    IsFiniteMeasure (vectorMeasure U ξ) := by
  dsimp [vectorMeasure]
  infer_instance

/-- Squared modulus of a continuous complex function, kept real-valued. -/
def normSqMap {X : Type*} [TopologicalSpace X] (f : C(X, ℂ)) : C(X, ℝ) :=
  ⟨fun z => Complex.normSq (f z), Complex.continuous_normSq.comp f.continuous⟩

def phase (z : ℂ) : ℝ := Int.fract (z.arg / (2 * Real.pi))

@[simp] theorem phase_one : phase 1 = 0 := by simp [phase]

def vectorPhase (U : Operator H) [IsStarNormal U] (ξ : H) : ℝ :=
  ∫ z, phase z ∂vectorMeasure U ξ

/-- The continuous squared distance to one on the spectrum. -/
def distanceSq (U : Operator H) : C(spectrum ℂ U, ℝ) :=
  ⟨fun z => Complex.normSq ((z : ℂ) - 1),
    Complex.continuous_normSq.comp (continuous_subtype_val.sub continuous_const)⟩

theorem phase_exp (x : ℝ) :
    phase (Complex.exp (x * Complex.I)) = Int.fract (x / (2 * Real.pi)) := by
  rw [phase, Complex.arg_exp_mul_I]
  apply Int.fract_eq_fract.mpr
  refine ⟨-toIocDiv Real.two_pi_pos (-Real.pi) x, ?_⟩
  rw [← sub_div, toIocMod_sub_self]
  simp only [zsmul_eq_mul, Int.cast_neg]
  field_simp

/-- A continuous triangular cutoff on the chosen angle interval. -/
def phaseTriangle (n : ℕ) (x : ℝ) : ℝ := min x ((n : ℝ) * (1 - x))

theorem continuous_phaseTriangle (n : ℕ) : Continuous (phaseTriangle n) := by
  unfold phaseTriangle
  fun_prop

@[simp] theorem phaseTriangle_zero (n : ℕ) : phaseTriangle n 0 = 0 := by
  simp [phaseTriangle]

@[simp] theorem phaseTriangle_one (n : ℕ) : phaseTriangle n 1 = 0 := by
  simp [phaseTriangle]

/-- Although phase is discontinuous, this clipped phase is continuous on the circle. -/
theorem continuous_clippedPhase (n : ℕ) :
    Continuous (fun z : Circle => phaseTriangle n (phase z)) := by
  apply (Circle.isCoveringMap_exp.isQuotientMap Circle.exp_surjective).continuous_iff.mpr
  have hc : Continuous (phaseTriangle n ∘ Int.fract) :=
    (continuous_phaseTriangle n).continuousOn.comp_fract'' (by simp)
  simpa only [Function.comp_def, Circle.coe_exp, phase_exp, id_eq] using
    hc.comp (continuous_id.div_const (2 * Real.pi))

/-- Continuous lower approximations to phase on a unitary spectrum. -/
def phaseApprox (U : Operator H) (hU : U ∈ unitary (Operator H)) (n : ℕ) :
    C(spectrum ℂ U, ℝ) :=
  ⟨fun z => phaseTriangle n (phase z), by
    have hm : ∀ z : spectrum ℂ U, ‖(z : ℂ)‖ = 1 := fun z =>
      CStarRing.norm_of_mem_unitary (spectrum_subset_unitary_of_mem_unitary hU z.property)
    exact (continuous_clippedPhase n).comp (continuous_subtype_val.subtype_mk (fun z => mem_sphere_zero_iff_norm.mpr (hm z)))⟩

/-- Pointwise exponential of a continuous complex-valued function. -/
def expMap {X : Type*} [TopologicalSpace X] (f : C(X, ℂ)) : C(X, ℂ) :=
  ⟨fun z => Complex.exp (f z), Complex.continuous_exp.comp f.continuous⟩

end KervaireSpectral

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.SpectralLogarithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology

namespace KervaireSpectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The continuous vector functional on all bounded operators. -/
def vectorCLM (ξ : H) : Operator H →L[ℂ] ℂ :=
  (innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ H ξ)

omit [CompleteSpace H] in
@[simp] theorem vectorCLM_apply (ξ : H) (T : Operator H) :
    vectorCLM ξ T = inner ℂ ξ (T ξ) := rfl

end KervaireSpectral

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.ScalarPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireScalarPhase

def phase (z : ℂ) : ℝ := Int.fract (z.arg / (2 * Real.pi))

@[simp] theorem phase_one : phase 1 = 0 := by simp [phase]

/-- Tangential approach to the phase cut, from the prescribed side. -/
def cutApproach (ε : ℝ) : ℂ := (1 - ε ^ 2 : ℝ) + ε * Complex.I

/-- The regularization used in the trace inequality. -/
def smoothPhase (a z : ℂ) : ℝ := 1 / 2 + (1 - a * z).arg / Real.pi

theorem re_one_sub_mul_pos {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    0 < (1 - a * z).re := by
  have h : (a*z).re < 1 := (Complex.re_le_norm _).trans_lt
    ((norm_mul_le a z).trans_lt <| by nlinarith [norm_nonneg a, norm_nonneg z])
  simpa using sub_pos.mpr h

/-- A concrete sequence in the open disk approaching the required side of the cut. -/
def cutTime (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

end KervaireScalarPhase

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.TraceCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireTraceCalculus
open scoped Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedRing E]
  [NormedAlgebra 𝕜 E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section RealPath
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- A regularized logarithm evaluated by a trace. -/
def traceLog (τ : A →L[ℂ] ℂ) (a : ℂ) (U : A) : ℂ :=
  ∑' n : ℕ, (a ^ (n + 1) / (n + 1)) * τ (U ^ (n + 1))

end RealPath
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A]

/-- The derivative generator has the normalization used for fractional phase. -/
def phaseVelocity (B : A) : A := ((2 * Real.pi : ℂ) * Complex.I) • B

/-- A smooth trace approximation to the fractional spectral phase. -/
def smoothTrace (τ : A →L[ℂ] ℂ) (a : ℂ) (U : A) : ℝ :=
  (τ 1).re / 2 - (traceLog τ a U).im / Real.pi

end KervaireTraceCalculus

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.SpectralApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireSpectral
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Mercator logarithm is continuous on the unitary spectrum. -/
def spectralLog (U : Operator H) (hU : U ∈ unitary (Operator H)) (a : ℂ)
    (ha : ‖a‖ < 1) : C(spectrum ℂ U, ℂ) :=
  ⟨fun z => -Complex.log (1 - a * z), by
    apply Continuous.neg
    apply Continuous.clog
    · fun_prop
    · intro z
      apply Complex.mem_slitPlane_iff.mpr
      exact Or.inl (re_one_sub_mul_pos ha
        (CStarRing.norm_of_mem_unitary
          (spectrum_subset_unitary_of_mem_unitary hU z.property)).le)⟩

/-- The regularized scalar phase is continuous on the unitary spectrum. -/
def spectralSmooth (U : Operator H) (hU : U ∈ unitary (Operator H))
    (a : ℂ) (ha : ‖a‖ < 1) : C(spectrum ℂ U, ℝ) :=
  ⟨fun z => smoothPhase a z, by
    have hc : Continuous (fun z : spectrum ℂ U =>
        1 / 2 - (spectralLog U hU a ha z).im / Real.pi) := by
      exact continuous_const.sub
        ((Complex.continuous_im.comp (spectralLog U hU a ha).continuous).div_const _)
    simpa [spectralLog, smoothPhase, Complex.log_im, sub_eq_add_neg, neg_div]
      using hc⟩

@[simp] theorem complexify_one {X : Type*} [TopologicalSpace X] :
    complexify (1 : C(X, ℝ)) = 1 := by ext; simp [complexify]

end KervaireSpectral

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.PhaseSubadditivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder

namespace KervaireCentralizer
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
abbrev Operator := H →L[ℂ] H

/-- The strongly closed algebra in which the phase comparison is performed. -/
def algebra (S : Set (Operator (H := H))) : StarSubalgebra ℂ (Operator (H := H)) :=
  StarSubalgebra.centralizer ℂ S

instance instIsClosedOperatorCoeStarSubalgebraComplexAlgebra (S : Set (Operator (H := H))) : IsClosed (algebra S : Set (Operator (H := H))) :=
  Set.isClosed_centralizer _

/-- The inclusion is continuous for the inherited operator norm. -/
def inclusion (S : Set (Operator (H := H))) : algebra S →L[ℂ] Operator (H := H) :=
  (algebra S).toSubalgebra.toSubmodule.subtypeL

local instance instContinuousFunctionalCalculusRealOperatorIsSelfAdjoint_rcbcc5f_1 : ContinuousFunctionalCalculus ℝ (Operator (H := H)) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus
@[simp] theorem inclusion_apply (S : Set (Operator (H := H))) (X : algebra S) :
    inclusion S X = (X : Operator (H := H)) := rfl

/-- Unitarity is unchanged when an operator is viewed in its centralizer. -/
theorem unitary_iff (S : Set (Operator (H := H))) (X : algebra S) :
    X ∈ unitary (algebra S) ↔ (X : Operator (H := H)) ∈ unitary (Operator (H := H)) := by
  simp only [Unitary.mem_iff]
  constructor
  · rintro ⟨h₁,h₂⟩
    exact ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨Subtype.ext h₁, Subtype.ext h₂⟩

end KervaireCentralizer

namespace KervaireSpectral
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

/-- The unnormalized finite sum of vector functionals used for matrix traces. -/
def vectorSum (ξ : ι → H) : Operator H →L[ℂ] ℂ := ∑ j, vectorCLM (ξ j)

omit [CompleteSpace H] in
@[simp] theorem vectorSum_apply (ξ : ι → H) (T : Operator H) :
    vectorSum ξ T = ∑ j, vectorCLM (ξ j) T := by simp [vectorSum]

/-- The phase measured by a finite family of vectors. -/
def sumPhase (U : Operator H) [IsStarNormal U] (ξ : ι → H) : ℝ :=
  ∑ j, vectorPhase U (ξ j)

end KervaireSpectral

namespace KervaireCentralizer
open KervaireTraceCalculus KervaireSpectral KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

/-- The vector sum restricted to the correct finite-trace algebra. -/
def trace (S : Set (Operator (H := H))) (ξ : ι → H) : algebra S →L[ℂ] ℂ :=
  (vectorSum ξ).comp (inclusion S)

@[simp] theorem trace_apply (S : Set (Operator (H := H))) (ξ : ι → H) (X : algebra S) :
    trace S ξ X = vectorSum ξ (X : Operator (H := H)) := rfl

end KervaireCentralizer

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.PhaseNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder

namespace KervaireSpectral

def scalarRotation (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[simp] theorem scalarRotation_zero : scalarRotation 0 = 1 := by simp [scalarRotation]

@[simp] theorem norm_scalarRotation (x : ℝ) : ‖scalarRotation x‖ = 1 := by
  simp [scalarRotation, Complex.norm_exp]

@[simp] theorem scalarRotation_add (x y : ℝ) :
    scalarRotation (x+y) = scalarRotation x * scalarRotation y := by
  simp only [scalarRotation, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

@[simp] theorem star_scalarRotation (x : ℝ) : star (scalarRotation x) = scalarRotation (-x) := by
  unfold scalarRotation
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg,
    mul_neg, neg_mul]

theorem scalarRotation_unitary (x : ℝ) : scalarRotation x ∈ unitary ℂ := by
  rw [Unitary.mem_iff]
  simp only [star_scalarRotation, ← scalarRotation_add, neg_add_cancel, add_neg_cancel,
    scalarRotation_zero, and_self]

end KervaireSpectral

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.PhaseGrids
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder

namespace KervaireSpectral

section

@[simp] theorem scalarRotation_nat_mul (x : ℝ) (d : ℕ) :
    scalarRotation ((d : ℝ)*x) = scalarRotation x ^ d := by
  unfold scalarRotation
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

end

open KervaireTraceCalculus KervaireScalarPhase

end KervaireSpectral

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.RegularOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate

namespace KervaireRegular

variable {α β γ : Type*}

/-- Permuting the coordinates of a square-summable family preserves membership,
without requiring a countable set of coordinates. -/
theorem mem_l2_reindex (e : α ≃ β) (f : ℓ²(α, ℂ)) :
    Memℓp (fun j => f (e.symm j)) 2 := by
  apply memℓp_gen
  exact (e.symm.summable_iff).2 ((lp.memℓp f).summable (by norm_num))

/-- Coordinate permutation before adding the isometric structure. -/
def reindexLinear (e : α ≃ β) : ℓ²(α, ℂ) ≃ₗ[ℂ] ℓ²(β, ℂ) where
  toFun f := ⟨fun j => f (e.symm j), mem_l2_reindex e f⟩
  invFun f := ⟨fun i => f (e i), mem_l2_reindex e.symm f⟩
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp
  map_add' f g := rfl
  map_smul' c f := rfl

@[simp] theorem reindexLinear_apply (e : α ≃ β) (f : ℓ²(α, ℂ)) (j : β) :
    reindexLinear e f j = f (e.symm j) := rfl

/-- The unitary permutation representation on `ℓ²`, for arbitrary index types. -/
def reindex (e : α ≃ β) : ℓ²(α, ℂ) ≃ₗᵢ[ℂ] ℓ²(β, ℂ) :=
  (reindexLinear e).isometryOfInner (by
    intro f g
    simp only [lp.inner_eq_tsum, reindexLinear_apply]
    exact e.symm.tsum_eq (fun i => inner ℂ (f i) (g i)))

@[simp] theorem reindex_apply (e : α ≃ β) (f : ℓ²(α, ℂ)) (j : β) :
    reindex e f j = f (e.symm j) := rfl

@[simp] theorem reindex_symm (e : α ≃ β) : (reindex e).symm = reindex e.symm := by
  ext f j
  rfl

@[simp] theorem reindex_trans (e : α ≃ β) (d : β ≃ γ) :
    (reindex e).trans (reindex d) = reindex (e.trans d) := by
  ext f j
  rfl

/-- The standard delta vector used for the finite trace. -/
def delta (i : α) : ℓ²(α, ℂ) := by classical exact lp.single 2 i 1

@[simp] theorem reindex_delta (e : α ≃ β) (i : α) :
    reindex e (delta i) = delta (e i) := by
  classical
  ext j
  simp [reindex_apply, delta, Pi.single_apply, Equiv.symm_apply_eq]

@[simp] theorem inner_delta_left (i : α) (f : ℓ²(α, ℂ)) :
    inner ℂ (delta i) f = f i := by
  classical
  simpa [delta] using lp.inner_single_left (𝕜 := ℂ) i (1 : ℂ) f

@[simp] theorem inner_delta_right (i : α) (f : ℓ²(α, ℂ)) :
    inner ℂ f (delta i) = star (f i) := by
  classical
  simpa [delta] using lp.inner_single_right (𝕜 := ℂ) i (1 : ℂ) f

variable {A : Type*} [Group A]

/-- `L(a) δ_x = δ_(ax)` including infinite and uncountable groups. -/
def left (a : A) : ℓ²(A, ℂ) ≃ₗᵢ[ℂ] ℓ²(A, ℂ) := reindex (Equiv.mulLeft a)

def right (a : A) : ℓ²(A, ℂ) ≃ₗᵢ[ℂ] ℓ²(A, ℂ) := reindex (Equiv.mulRight a⁻¹)

@[simp] theorem left_apply (a : A) (f : ℓ²(A, ℂ)) (x : A) :
    left a f x = f (a⁻¹ * x) := rfl

@[simp] theorem right_apply (a : A) (f : ℓ²(A, ℂ)) (x : A) :
    right a f x = f (x * a) := by simp [right]

@[simp] theorem left_delta (a x : A) : left a (delta x) = delta (a * x) :=
  reindex_delta (Equiv.mulLeft a) x

@[simp] theorem right_delta (a x : A) : right a (delta x) = delta (x * a⁻¹) :=
  reindex_delta (Equiv.mulRight a⁻¹) x

@[simp] theorem left_mul (a b : A) (f : ℓ²(A, ℂ)) :
    left (a * b) f = left a (left b f) := by ext x; simp [mul_assoc]

@[simp] theorem right_mul (a b : A) (f : ℓ²(A, ℂ)) :
    right (a * b) f = right a (right b f) := by ext x; simp [mul_assoc]

abbrev Operator (A : Type*) := ℓ²(A, ℂ) →L[ℂ] ℓ²(A, ℂ)

instance operator_real_smulCommClass : SMulCommClass ℝ (Operator A) (Operator A) :=
  Algebra.to_smulCommClass (R := ℝ) (A := Operator A)

instance operator_real_isScalarTower : IsScalarTower ℝ (Operator A) (Operator A) :=
  IsScalarTower.right (R := ℝ) (A := Operator A)

/-- The commutant of the right regular representation. -/
def InCommutant (T : Operator A) : Prop :=
  ∀ a : A, Commute T (right a : Operator A)

@[simp] theorem right_star (a : A) :
    star (right a : Operator A) = (right a⁻¹ : Operator A) := by
  rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.adjoint_eq_symm]
  ext f x
  simp [right, reindex_symm, reindex_apply]

@[simp] theorem right_one (f : ℓ²(A, ℂ)) : right (1 : A) f = f := by
  ext x
  simp

/-- The (unnormalized for one copy) vector trace. -/
def trace : Operator A →L[ℂ] ℂ :=
  (innerSL ℂ (delta 1)).comp (ContinuousLinearMap.apply ℂ (ℓ²(A, ℂ)) (delta 1))

@[simp] theorem trace_apply (T : Operator A) :
    trace T = inner ℂ (delta 1) (T (delta 1)) := rfl

@[simp] theorem trace_eq_coefficient (T : Operator A) : trace T = T (delta 1) 1 := by
  simp

@[simp] theorem trace_one : trace (1 : Operator A) = 1 := by
  classical
  simp [delta]

local instance instContinuousFunctionalCalculusRealOperatorIsSelfAdjoint : ContinuousFunctionalCalculus ℝ (Operator A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus (A := Operator A)

end KervaireRegular

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.MatrixTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate

namespace KervaireMatrix

section
open KervaireRegular
variable {D A : Type*} [Group A]
abbrev Space (D A : Type*) := ℓ²(D × A, ℂ)
abbrev Operator (D A : Type*) := Space D A →L[ℂ] Space D A

/-- Diagonal right translations on the finite multiple of the regular Hilbert space. -/
def right (a : A) : Space D A ≃ₗᵢ[ℂ] Space D A :=
  reindex (Equiv.prodCongr (Equiv.refl D) (Equiv.mulRight a⁻¹))

@[simp] theorem right_apply (a : A) (f : Space D A) (j : D) (x : A) :
    right a f (j,x) = f (j,x*a) := by simp [right]

@[simp] theorem right_delta (a x : A) (j : D) :
    right a (delta (j,x)) = delta (j,x*a⁻¹) := by simp [right]

@[simp] theorem right_star (a : A) :
    star (right (D := D) a : Operator D A) = (right (D := D) a⁻¹ : Operator D A) := by
  rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.adjoint_eq_symm]
  ext f ⟨j,x⟩
  simp [right, reindex_symm, reindex_apply]

/-- The finite matrix group von Neumann algebra, before bundling. -/
def InCommutant (T : Operator D A) : Prop := ∀ a : A, Commute T (right (D := D) a : Operator D A)

variable [Fintype D]

def trace : Operator D A →L[ℂ] ℂ :=
  ∑ i : D, (innerSL ℂ (delta (i,(1 : A)))).comp
    (ContinuousLinearMap.apply ℂ (Space D A) (delta (i,1)))

@[simp] theorem trace_apply (T : Operator D A) :
    trace T = ∑ i : D, inner ℂ (delta (i,1)) (T (delta (i,1))) := by simp [trace]

@[simp] theorem trace_eq_coefficient (T : Operator D A) :
    trace T = ∑ i : D, T (delta (i,1)) (i,1) := by simp

@[simp] theorem trace_one : trace (1 : Operator D A) = Fintype.card D := by
  classical
  simp [delta]

end

section
open KervaireRegular KervaireSpectral
variable {D A : Type*} [Group A]

/-- The closed algebra `M_D(M_A)` represented on the arbitrary-group Hilbert space. -/
def algebra : StarSubalgebra ℂ (Operator D A) :=
  KervaireCentralizer.algebra (Set.range (fun a : A => (right (D := D) a : Operator D A)))

variable [Fintype D]

/-- The regular Hilbert space is nonzero whenever the finite index set is inhabited. -/
instance instNontrivialSubtypePreLpProdComplexMemAddSubgroupSpaceOfNonempty [Nonempty D] : Nontrivial (Space D A) := by
  classical
  let i : D := Classical.choice inferInstance
  refine ⟨⟨delta (i,(1 : A)), 0, ?_⟩⟩
  intro h
  have hh := congrArg (fun f : Space D A => f (i,1)) h
  simp [delta] at hh

def phase (U : Operator D A) [IsStarNormal U] : ℝ :=
  sumPhase U (fun i : D => delta (i,(1 : A)))

end

open KervaireRegular KervaireSpectral

end KervaireMatrix

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.MatrixShifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate

namespace KervaireMatrix

section
open KervaireRegular
open scoped Classical
variable {D A : Type*}

/-- Projection to a scalar coordinate, on the actual product-index regular Hilbert space. -/
def coordinateProjection (i : D) : Operator D A := by
  classical
  let L : Space D A →ₗ[ℂ] Space D A := {
    toFun := fun f => ⟨fun p => if p.1 = i then f p else 0,
      (lp.memℓp f).mono' (by intro p; split_ifs <;> simp)⟩
    map_add' := by
      intro f g
      ext p
      change (if p.1 = i then f p + g p else 0) =
        (if p.1 = i then f p else 0) + (if p.1 = i then g p else 0)
      split_ifs <;> simp
    map_smul' := by intro c f; ext p; by_cases h : p.1 = i <;> simp [h] }
  exact L.mkContinuous 1 (fun f => by
    rw [one_mul]
    exact lp.norm_mono (by norm_num) (fun p => by
      change ‖ite (p.1 = i) (f p) 0‖ ≤ _
      split_ifs <;> simp))

@[simp] theorem coordinateProjection_apply (i d : D) (f : Space D A) (a : A) :
    coordinateProjection i f (d,a) = if d = i then f (d,a) else 0 := by
  classical
  rfl

/-- The scalar matrix unit, continuously acting on all (possibly uncountable) group coordinates. -/
def matrixUnit (i j : D) : Operator D A := by
  classical
  exact (coordinateProjection i).comp
    (reindex (Equiv.prodCongr (Equiv.swap i j) (Equiv.refl A))).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem matrixUnit_apply (i j d : D) (f : Space D A) (a : A) :
    matrixUnit i j f (d,a) = if d = i then f (j,a) else 0 := by
  classical
  simp only [matrixUnit, ContinuousLinearMap.comp_apply, coordinateProjection_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    reindex_apply, Equiv.prodCongr_symm, Equiv.symm_swap, Equiv.refl_symm,
    Equiv.prodCongr_apply]
  split_ifs with h
  · subst d; simp
  · rfl

/-- Equality of operators on the standard orthonormal basis. -/
theorem ext_delta {T U : Operator D A}
    (h : ∀ p : D × A, T (delta p) = U (delta p)) : T = U := by
  classical
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro p
  apply ContinuousLinearMap.ext
  intro c
  have hc : lp.single (E := fun _ : D × A => ℂ) 2 p c = c • delta p := by
    ext q
    simp [delta, Pi.single_apply]
  change T (lp.single 2 p c) = U (lp.single 2 p c)
  rw [hc, map_smul, map_smul, h]

/-- Matrix coefficients suffice to establish an adjoint identity. -/
theorem star_eq_of_coefficients {T U : Operator D A}
    (h : ∀ p q : D × A, star (T (delta p) q) = U (delta q) p) : star T = U := by
  apply ext_delta
  intro q
  ext p
  calc
    (star T) (delta q) p = inner ℂ (delta p) ((star T) (delta q)) :=
      (inner_delta_left _ _).symm
    _ = inner ℂ (T (delta p)) (delta q) := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    _ = star (T (delta p) q) := inner_delta_right _ _
    _ = U (delta q) p := h p q

@[simp] theorem matrixUnit_star (i j : D) : star (matrixUnit (A := A) i j) = matrixUnit j i := by
  classical
  apply star_eq_of_coefficients
  rintro ⟨d,a⟩ ⟨e,b⟩
  simp only [matrixUnit_apply]
  by_cases he : e = i <;> by_cases hd : d = j
  · subst e; subst d
    simp [delta, Pi.single_apply, eq_comm]
  · simp [he,hd,delta,Prod.mk.injEq,Ne.symm hd]
  · simp [he,hd,delta,Prod.mk.injEq,Ne.symm he]
  · simp [he,hd]

variable [Fintype D]

/-- Scalar matrices embedded without any finite/countable assumption on the group. -/
def scalarTensor (M : Matrix D D ℂ) : Operator D A :=
  ∑ i, ∑ j, M i j • matrixUnit i j

@[simp] theorem scalarTensor_apply (M : Matrix D D ℂ) (f : Space D A) (d : D) (a : A) :
    scalarTensor M f (d,a) = ∑ j, M d j * f (j,a) := by
  classical
  change (∑ i, ∑ j, M i j • matrixUnit (A := A) i j) f (d,a) = _
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply]
  simp [Finset.sum_ite_irrel]

@[simp] theorem scalarTensor_one : scalarTensor (1 : Matrix D D ℂ) = (1 : Operator D A) := by
  classical
  ext f ⟨d,a⟩
  simp [Matrix.one_apply]

@[simp] theorem scalarTensor_mul (M N : Matrix D D ℂ) :
    scalarTensor (A := A) (M*N) = scalarTensor M * scalarTensor N := by
  ext f ⟨d,a⟩
  simp only [scalarTensor_apply, mul_apply_eq_comp, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_assoc _ _ _

@[simp] theorem scalarTensor_star (M : Matrix D D ℂ) :
    star (scalarTensor (A := A) M) = scalarTensor (star M) := by
  classical
  apply star_eq_of_coefficients
  rintro ⟨sourceIndex,sourceElement⟩ ⟨targetIndex,targetElement⟩
  by_cases heq : sourceElement = targetElement
  · subst targetElement
    simp [delta, Pi.single_apply, Prod.mk.injEq]
  · simp [delta, Prod.mk.injEq, heq, Ne.symm heq]

variable [Group A]

/-- The scalar trace on tensoring with the regular identity is unnormalized matrix trace. -/
@[simp] theorem trace_scalarTensor (M : Matrix D D ℂ) :
    trace (scalarTensor (A := A) M) = Matrix.trace M := by
  classical
  simp only [trace_apply, inner_delta_left, scalarTensor_apply, Matrix.trace]
  simp [delta, Pi.single_apply, Prod.mk.injEq]

omit [Group A] in
/-- Unitary scalar matrices remain unitary in the full regular operator algebra. -/
theorem scalarTensor_mem_unitary {M : Matrix D D ℂ} (hM : M ∈ Matrix.unitaryGroup D ℂ) :
    scalarTensor (A := A) M ∈ unitary (Operator D A) := by
  rw [Unitary.mem_iff] at hM ⊢
  constructor
  · rw [scalarTensor_star, ← scalarTensor_mul, hM.1, scalarTensor_one]
  · rw [scalarTensor_star, ← scalarTensor_mul, hM.2, scalarTensor_one]

end

open KervaireRegular
open scoped Classical
variable {D A : Type*} [Group A]

/-- The coordinate permutation underlying a group-labelled shift.  Labels act
on the left so that the operator commutes with every right translation. -/
def labelledPermutation (σ : Equiv.Perm D) (a : D → A) : Equiv.Perm (D × A) where
  toFun p := (σ p.1, a p.1 * p.2)
  invFun p := (σ.symm p.1, (a (σ.symm p.1))⁻¹ * p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- A corner-labelled permutation on the actual arbitrary-group Hilbert space. -/
def labelledShift (σ : Equiv.Perm D) (a : D → A) : Operator D A :=
  (reindex (labelledPermutation σ a)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem labelledShift_apply (σ : Equiv.Perm D) (a : D → A)
    (f : Space D A) (d : D) (x : A) :
    labelledShift σ a f (d,x) = f (σ.symm d, (a (σ.symm d))⁻¹ * x) := rfl

@[simp] theorem labelledShift_delta (σ : Equiv.Perm D) (a : D → A) (d : D) (x : A) :
    labelledShift σ a (delta (d,x)) = delta (σ d,a d*x) :=
  reindex_delta _ _

/-- This representation is unitary without dimensional or cardinality assumptions. -/
theorem labelledShift_unitary (σ : Equiv.Perm D) (a : D → A) :
    labelledShift σ a ∈ unitary (Operator D A) := by
  rw [Unitary.mem_iff]
  have hs : star (labelledShift σ a) =
      (reindex (labelledPermutation σ a)).symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    exact LinearIsometryEquiv.adjoint_eq_symm _
  rw [hs]
  constructor <;> ext f p <;> simp [labelledShift, mul_apply_eq_comp]

@[simp] theorem labelledShift_one :
    labelledShift (Equiv.refl D) (fun _ => (1 : A)) = 1 := by
  ext f ⟨d,x⟩
  simp

variable [Fintype D]

/-- A scalar diagonal on the finite coordinate set. -/
def scalarDiagonal (u : D → ℂ) : Operator D A :=
  scalarTensor (Matrix.diagonal u)

omit [Group A] in
@[simp] theorem scalarDiagonal_apply (u : D → ℂ) (f : Space D A) (d : D) (x : A) :
    scalarDiagonal u f (d,x) = u d * f (d,x) := by
  classical
  simp [scalarDiagonal, Matrix.diagonal]

omit [Group A] in
@[simp] theorem scalarDiagonal_delta (u : D → ℂ) (d : D) (x : A) :
    scalarDiagonal u (delta (d,x)) = u d • delta (d,x) := by
  classical
  ext ⟨e,y⟩
  by_cases h : (e,y) = (d,x)
  · cases h
    simp [delta]
  · simp [delta, Ne.symm h]

omit [Group A] in
@[simp] theorem scalarDiagonal_one : scalarDiagonal (A := A) (fun _ : D => 1) = 1 := by
  ext f ⟨d,x⟩
  simp

omit [Group A] in
@[simp] theorem scalarDiagonal_mul (u v : D → ℂ) :
    scalarDiagonal (A := A) u * scalarDiagonal v = scalarDiagonal (u*v) := by
  ext f ⟨d,x⟩
  simp [mul_apply_eq_comp, mul_assoc]

omit [Group A] in
@[simp] theorem scalarDiagonal_star (u : D → ℂ) :
    star (scalarDiagonal (A := A) u) = scalarDiagonal (star u) := by
  dsimp [scalarDiagonal]
  rw [scalarTensor_star]
  congr 1
  ext i j
  by_cases h : i = j
  · subst j; simp
  · simp [Matrix.star_apply, Matrix.diagonal, h, Ne.symm h]

omit [Group A] in
theorem scalarDiagonal_unitary (u : D → ℂ) (hu : ∀ d, u d ∈ unitary ℂ) :
    scalarDiagonal (A := A) u ∈ unitary (Operator D A) := by
  rw [Unitary.mem_iff, scalarDiagonal_star, scalarDiagonal_mul, scalarDiagonal_mul]
  have h1 : star u * u = 1 := funext fun d => (Unitary.mem_iff.mp (hu d)).1
  have h2 : u * star u = 1 := funext fun d => (Unitary.mem_iff.mp (hu d)).2
  rw [h1,h2]
  exact ⟨scalarDiagonal_one,scalarDiagonal_one⟩

/-- This includes both shifts: `S` has coefficient labels,
while `Theta` has only scalar phase labels. -/
def weightedShift (σ : Equiv.Perm D) (u : D → ℂ) (a : D → A) : Operator D A :=
  labelledShift σ a * scalarDiagonal u

@[simp] theorem weightedShift_apply (σ : Equiv.Perm D) (u : D → ℂ) (a : D → A)
    (f : Space D A) (d : D) (x : A) :
    weightedShift σ u a f (d,x) =
      u (σ.symm d) * f (σ.symm d, (a (σ.symm d))⁻¹*x) := by
  simp [weightedShift, mul_apply_eq_comp]

@[simp] theorem weightedShift_delta (σ : Equiv.Perm D) (u : D → ℂ) (a : D → A)
    (d : D) (x : A) :
    weightedShift σ u a (delta (d,x)) = u d • delta (σ d,a d*x) := by
  simp [weightedShift,mul_apply_eq_comp]

theorem weightedShift_unitary (σ : Equiv.Perm D) (u : D → ℂ) (a : D → A)
    (hu : ∀ d, u d ∈ unitary ℂ) : weightedShift σ u a ∈ unitary (Operator D A) :=
  mul_mem (labelledShift_unitary σ a) (scalarDiagonal_unitary u hu)

end KervaireMatrix
namespace KervaireSpectral
@[simp] theorem scalarRotation_nat (j : ℕ) : scalarRotation j = 1 := by
  unfold scalarRotation
  rw [show ((2 * Real.pi * (j : ℝ) : ℝ) : ℂ) * Complex.I =
    (j : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact Complex.exp_nat_mul_two_pi_mul_I j

end KervaireSpectral

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.WeightedCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate

namespace KervaireRegular
open KervaireSpectral
open scoped Classical
variable {A : Type*} [Group A]

def leftOperator (a : A) : Operator A := (left a).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem leftOperator_delta (a x : A) :
    leftOperator a (delta x) = delta (a*x) := left_delta a x

@[simp] theorem leftOperator_one : leftOperator (1 : A) = 1 := by
  ext f x
  simp [leftOperator]

theorem leftOperator_mul (a b : A) : leftOperator (a*b) = leftOperator a * leftOperator b := by
  ext f x
  simp [leftOperator, mul_apply_eq_comp]

@[simp] theorem leftOperator_pow (a : A) (n : ℕ) : leftOperator (a^n) = leftOperator a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, leftOperator_mul, ih, pow_succ]

theorem leftOperator_unitary (a : A) : leftOperator a ∈ unitary (Operator A) := by
  rw [Unitary.mem_iff]
  have hs : star (leftOperator a) = leftOperator a⁻¹ := by
    change ContinuousLinearMap.adjoint (left a).toContinuousLinearEquiv.toContinuousLinearMap = _
    rw [LinearIsometryEquiv.adjoint_eq_symm]
    ext f x
    simp [leftOperator, left, reindex_symm, reindex_apply]
  rw [hs, ← leftOperator_mul, ← leftOperator_mul]
  simp

/-- Exact scalar-rotated fractional phase of a group element. -/
def groupPhase (z : ℂ) (hz : z ∈ unitary ℂ) (a : A) : ℝ :=
  let _ := isStarNormal_of_mem_unitary (Unitary.smul_mem ⟨z,hz⟩ (leftOperator_unitary a))
  vectorPhase (z • leftOperator a) (delta 1)

end KervaireRegular

namespace KervaireCycle
open Fin.NatCast
variable {D B : Type*} [Monoid B]

/-- Circuit weights in their actual operator multiplication order. -/
def orbitWeight (σ : Equiv.Perm D) (b : D → B) : ℕ → D → B
  | 0, _ => 1
  | n+1, i => b ((σ^n) i) * orbitWeight σ b n i

@[simp] theorem orbitWeight_zero (σ : Equiv.Perm D) (b : D → B) (i : D) :
    orbitWeight σ b 0 i = 1 := rfl
@[simp] theorem orbitWeight_succ (σ : Equiv.Perm D) (b : D → B) (n : ℕ) (i : D) :
    orbitWeight σ b (n+1) i = b ((σ^n) i) * orbitWeight σ b n i := rfl

end KervaireCycle

namespace KervaireCycle
variable {D B : Type*} [Monoid B]

/-- All full and partial circuit products remain in any submonoid containing the labels. -/
theorem orbitWeight_mem (H : Submonoid B) (σ : Equiv.Perm D) (b : D → B)
    (hb : ∀ i, b i ∈ H) (n : ℕ) (i : D) : orbitWeight σ b n i ∈ H := by
  induction n with
  | zero => exact H.one_mem
  | succ n ih => exact H.mul_mem (hb _) ih

end KervaireCycle

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.PhaseFaithfulness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate

namespace KervaireRegular
open KervaireSpectral
open scoped ComplexOrder
variable {A : Type*} [Group A]

@[simp] theorem star_leftOperator (a : A) : star (leftOperator a) = leftOperator a⁻¹ := by
  change ContinuousLinearMap.adjoint (left a).toContinuousLinearEquiv.toContinuousLinearMap = _
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  ext f x
  simp [leftOperator, left, reindex_symm, reindex_apply]

end KervaireRegular

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.PhaseDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder

namespace KervaireSpectral

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- A basis adapted to a subspace and its orthogonal complement. -/
def orthogonalPairBasis (E : Submodule ℂ H) :
    Module.Basis (Fin (Module.finrank ℂ E) ⊕ Fin (Module.finrank ℂ Eᗮ)) ℂ H :=
  ((stdOrthonormalBasis ℂ E).toBasis.prod (stdOrthonormalBasis ℂ Eᗮ).toBasis).map
    (E.prodEquivOfIsCompl Eᗮ E.isCompl_orthogonal)

@[simp] theorem orthogonalPairBasis_inl (E : Submodule ℂ H) (i : Fin (Module.finrank ℂ E)) :
    orthogonalPairBasis E (.inl i) = (stdOrthonormalBasis ℂ E i : H) := by
  simp [orthogonalPairBasis, Module.Basis.map_apply, Module.Basis.prod_apply,
    Submodule.coe_prodEquivOfIsCompl']

@[simp] theorem orthogonalPairBasis_inr (E : Submodule ℂ H) (i : Fin (Module.finrank ℂ Eᗮ)) :
    orthogonalPairBasis E (.inr i) = (stdOrthonormalBasis ℂ Eᗮ i : H) := by
  simp [orthogonalPairBasis, Module.Basis.map_apply, Module.Basis.prod_apply,
    Submodule.coe_prodEquivOfIsCompl']

theorem orthogonalPairBasis_orthonormal (E : Submodule ℂ H) :
    Orthonormal ℂ (orthogonalPairBasis E) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · simpa only [orthogonalPairBasis_inl, Submodule.coe_inner,
      Sum.inl.injEq] using (orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ E).orthonormal) i j
  · simp only [orthogonalPairBasis_inl, orthogonalPairBasis_inr, reduceCtorEq, ↓reduceIte]
    exact (stdOrthonormalBasis ℂ Eᗮ j).property _ (stdOrthonormalBasis ℂ E i).property
  · simp only [orthogonalPairBasis_inl, orthogonalPairBasis_inr, reduceCtorEq, ↓reduceIte]
    exact inner_eq_zero_symm.mp
      ((stdOrthonormalBasis ℂ Eᗮ i).property _ (stdOrthonormalBasis ℂ E j).property)
  · simpa only [orthogonalPairBasis_inr, Submodule.coe_inner,
      Sum.inr.injEq] using (orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ Eᗮ).orthonormal) i j

/-- The normalized basis is orthonormal. -/
def orthogonalPairONB (E : Submodule ℂ H) :
    OrthonormalBasis (Fin (Module.finrank ℂ E) ⊕ Fin (Module.finrank ℂ Eᗮ)) ℂ H :=
  (orthogonalPairBasis E).toOrthonormalBasis (orthogonalPairBasis_orthonormal E)

@[simp] theorem orthogonalPairONB_inl (E : Submodule ℂ H) (i : Fin (Module.finrank ℂ E)) :
    orthogonalPairONB E (.inl i) = (stdOrthonormalBasis ℂ E i : H) := by
  simp [orthogonalPairONB, Module.Basis.coe_toOrthonormalBasis]

@[simp] theorem orthogonalPairONB_inr (E : Submodule ℂ H) (i : Fin (Module.finrank ℂ Eᗮ)) :
    orthogonalPairONB E (.inr i) = (stdOrthonormalBasis ℂ Eᗮ i : H) := by
  simp [orthogonalPairONB, Module.Basis.coe_toOrthonormalBasis]

end

end KervaireSpectral

namespace KervaireMatrix
open KervaireRegular KervaireSpectral KervaireTraceCalculus
open scoped Classical
variable {D A : Type*} [Fintype D] [Group A]

omit [Group A] in
@[simp] theorem scalarTensor_pow (M : Matrix D D ℂ) (n : ℕ) :
    scalarTensor (A := A) (M^n) = scalarTensor M ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, scalarTensor_mul, ih, pow_succ]

end KervaireMatrix

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.MixingOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder

namespace KervaireMixing

section
open Matrix KervaireMatrix KervaireRegular
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

/-- A slot is a disk number, a disk kind, and a position in the cyclic word. -/
abbrev Slot (I K : Type*) := (K ⊕ K) × I

/-- The opposite cyclic orders on positive and negative word disks. -/
def successor (ρ : Equiv.Perm I) : Equiv.Perm (Slot I K) where
  toFun p := match p with
    | (Sum.inl k, i) => (Sum.inl k, ρ i)
    | (Sum.inr k, i) => (Sum.inr k, ρ.symm i)
  invFun p := match p with
    | (Sum.inl k, i) => (Sum.inl k, ρ.symm i)
    | (Sum.inr k, i) => (Sum.inr k, ρ i)
  left_inv p := by rcases p with ⟨k|k,i⟩ <;> simp
  right_inv p := by rcases p with ⟨k|k,i⟩ <;> simp

/-- Coefficient inverses for the signed incidence operator. -/
def labels (ρ : Equiv.Perm I) (a : I → A) : Slot I K → A
  | (Sum.inl _, i) => (a i)⁻¹
  | (Sum.inr _, i) => a (ρ.symm i)

/-- The scalar mixing involution; no group coefficients occur in it. -/
def mixingMatrix (X : Matrix K K ℂ) : Matrix (Slot I K) (Slot I K) ℂ :=
  blockDiagonal fun _ : I => fromBlocks 0 Xᴴ X 0

omit [Fintype I] [Fintype K] in
@[simp] theorem mixingMatrix_star (X : Matrix K K ℂ) :
    star (mixingMatrix (I := I) X) = mixingMatrix X := by
  ext ⟨k,i⟩ ⟨l,j⟩
  rcases k with k | k <;> rcases l with l | l <;>
    by_cases h : i = j <;> simp [mixingMatrix, Matrix.star_apply, blockDiagonal_apply, fromBlocks, eq_comm, h]

@[simp] theorem mixingMatrix_sq (X : Matrix.unitaryGroup K ℂ) :
    mixingMatrix (I := I) (X : Matrix K K ℂ) * mixingMatrix (X : Matrix K K ℂ) = 1 := by
  simp only [mixingMatrix, ← blockDiagonal_mul, fromBlocks_multiply,
    zero_mul, mul_zero, add_zero, zero_add]
  rw [show (X : Matrix K K ℂ)ᴴ * (X : Matrix K K ℂ) = 1 from X.2.1,
    show (X : Matrix K K ℂ) * (X : Matrix K K ℂ)ᴴ = 1 from X.2.2]
  convert (blockDiagonal_one (m := K ⊕ K) (o := I) (α := ℂ)) using 1
  ext ⟨p,i⟩ ⟨q,j⟩
  simp [blockDiagonal_apply, fromBlocks_one, Matrix.one_apply]

/-- The coefficient shift S and scalar mixer J in the actual regular Hilbert space. -/
def S (ρ : Equiv.Perm I) (a : I → A) : Operator (Slot I K) A :=
  labelledShift (successor ρ) (labels ρ a)
def J (X : Matrix K K ℂ) : Operator (Slot I K) A := scalarTensor (mixingMatrix X)

omit [Fintype I] [Fintype K] in
theorem S_unitary (ρ : Equiv.Perm I) (a : I → A) :
    S (K := K) ρ a ∈ unitary (Operator (Slot I K) A) := labelledShift_unitary _ _
omit [Group A] in
theorem J_sq (X : Matrix.unitaryGroup K ℂ) :
    J (I := I) (A := A) (X : Matrix K K ℂ) * J (X : Matrix K K ℂ) = 1 := by
  rw [J, ← scalarTensor_mul, mixingMatrix_sq]
  ext f ⟨d,a⟩
  simp [Matrix.one_apply]

omit [Group A] in
theorem J_star (X : Matrix K K ℂ) :
    star (J (I := I) (A := A) X) = J X := by
  rw [J, scalarTensor_star, mixingMatrix_star]

omit [Group A] in
theorem J_unitary (X : Matrix.unitaryGroup K ℂ) :
    J (I := I) (A := A) (X : Matrix K K ℂ) ∈ unitary (Operator (Slot I K) A) := by
  rw [Unitary.mem_iff, J_star, J_sq]
  exact ⟨rfl,rfl⟩

omit [Group A] in
@[simp] theorem scalarTensor_delta (M : Matrix (Slot I K) (Slot I K) ℂ)
    (p q : Slot I K) (x y : A) :
    scalarTensor M (delta (p,x)) (q,y) = if x = y then M q p else 0 := by
  simp [scalarTensor_apply, delta, Pi.single_apply, Prod.mk.injEq, ite_and,
    mul_ite, eq_comm]

end
open Matrix KervaireMatrix KervaireRegular KervaireSpectral
open scoped Classical

end KervaireMixing

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.HaarCurrents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology

open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff

namespace KervaireHaarFlow

open NormedSpace
open scoped ContDiff

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
  [StarRing B] [ContinuousStar B] [StarModule ℝ B]

local instance instNormedAlgebraRat_solutions : NormedAlgebra ℚ B := .restrictScalars ℚ ℝ B

/-- The genuine exponential flow in the unitary group. -/
def expFlow (a : skewAdjoint.submodule ℝ B) (t : ℝ) : unitary B :=
  ⟨exp (t • (a : B)), exp_mem_unitary_of_mem_skewAdjoint (by
    change star (t • (a : B)) = -(t • (a : B))
    rw [star_smul, star_trivial, a.property, smul_neg])⟩

end KervaireHaarFlow

namespace KervaireUnitaryHaarCurrent
open MeasureTheory VectorField
open scoped ContDiff
variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]

/-- The autonomous lift of a right-translation field to the time cylinder. -/
def liftField (a : B) : (ℝ × B) →L[ℝ] (ℝ × B) :=
  (ContinuousLinearMap.inr ℝ ℝ B).comp
    (((ContinuousLinearMap.mul ℝ B).flip a).comp (ContinuousLinearMap.snd ℝ ℝ B))

@[simp] lemma liftField_apply (a : B) (p : ℝ × B) : liftField a p = (0,p.2*a) := rfl

end KervaireUnitaryHaarCurrent

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.CurrentPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff

open MeasureTheory NormedSpace
open scoped ContDiff

namespace KervaireUnitaryTangent

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
  [StarRing B] [ContinuousStar B] [StarModule ℝ B]

/-- The real tangent subspace at a unitary, represented in the ambient algebra. -/
def tangent (u : unitary B) : Submodule ℝ B :=
  (skewAdjoint.submodule ℝ B).map (LinearMap.mulLeft ℝ (u : B))

end KervaireUnitaryTangent

open Module Set ContinuousAlternatingMap

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.IncidenceSpaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator

namespace KervaireIncidenceCurrent

section
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
abbrev Mat (I : Type*) := Matrix I I ℂ
abbrev Alg (K R : Type*) := Mat K × Mat (K ⊕ R) × Mat R
abbrev Horizontal (K R : Type*) [Fintype K] [Fintype R] :=
  skewAdjoint.submodule ℝ (Mat K) × skewAdjoint.submodule ℝ (Mat R) × Matrix R K ℂ

/-- Diagonal corner inclusions, as continuous real linear maps. -/
def in11 : Mat K →L[ℝ] Mat (K ⊕ R) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ fromBlocks A 0 0 0
      map_add' := by intros; ext i j; cases i <;> cases j <;> simp [fromBlocks]
      map_smul' := by intros; ext i j; cases i <;> cases j <;> simp [fromBlocks] }
def in22 : Mat R →L[ℝ] Mat (K ⊕ R) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun B ↦ fromBlocks 0 0 0 B
      map_add' := by intros; ext i j; cases i <;> cases j <;> simp [fromBlocks]
      map_smul' := by intros; ext i j; cases i <;> cases j <;> simp [fromBlocks] }

def diag (A : Mat K) (B : Mat R) : Mat (K ⊕ R) := fromBlocks A 0 0 B

def off (Z : Matrix R K ℂ) : Mat (K ⊕ R) := fromBlocks 0 (-Zᴴ) Z 0

omit [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R] in
lemma off_skew (Z : Matrix R K ℂ) : star (off Z) = -off Z := by
  ext i j
  cases i <;> cases j <;> simp [off, Matrix.star_apply, Matrix.conjTranspose_apply]

omit [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R] in
lemma diag_star (A : Mat K) (B : Mat R) : star (diag A B) = diag (star A) (star B) := by
  ext i j
  cases i <;> cases j <;> simp [diag, Matrix.star_apply]

omit [DecidableEq K] [DecidableEq R] in
lemma diag_mul (A C : Mat K) (B D : Mat R) : diag A B * diag C D = diag (A*C) (B*D) := by
  simp [diag, fromBlocks_multiply]

/-- The incidence map is polynomial in the redundant compact-group coordinates. -/
def incidence (f : ℝ × Mat K → Mat (K ⊕ R)) (p : ℝ × Alg K R) : Mat (K ⊕ R) :=
  f (p.1,p.2.1) * p.2.2.1 * diag 1 (star p.2.2.2) * star p.2.2.1

omit [DecidableEq K] [DecidableEq R] in
lemma diag_eq_corner (A : Mat K) (B : Mat R) : diag A B = in11 A + in22 B := by
  ext i j
  cases i <;> cases j <;> simp [diag, in11, in22, fromBlocks]

end
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

omit [Fintype K] [Fintype R] in
lemma diag_one : diag (1 : Mat K) (1 : Mat R) = 1 := by
  ext i j
  cases i <;> cases j <;> simp [diag, fromBlocks, one_apply]

lemma diag_unitary {A : Mat K} {B : Mat R} (hA : A ∈ unitary (Mat K))
    (hB : B ∈ unitary (Mat R)) : diag A B ∈ unitary (Mat (K ⊕ R)) := by
  rw [Unitary.mem_iff] at hA hB ⊢
  simp only [diag_star, diag_mul, hA.1, hA.2, hB.1, hB.2, diag_one, and_self]

lemma unitary_alg_parts (p : unitary (Alg K R)) :
    (p.val.1 ∈ unitary (Mat K)) ∧ (p.val.2.1 ∈ unitary (Mat (K ⊕ R))) ∧
      (p.val.2.2 ∈ unitary (Mat R)) := by
  have h := Unitary.mem_iff.mp p.property
  exact ⟨⟨congrArg Prod.fst h.1, congrArg Prod.fst h.2⟩,
    ⟨congrArg (Prod.fst ∘ Prod.snd) h.1, congrArg (Prod.fst ∘ Prod.snd) h.2⟩,
    ⟨congrArg (Prod.snd ∘ Prod.snd) h.1, congrArg (Prod.snd ∘ Prod.snd) h.2⟩⟩

def compensated (T : unitary (Mat R)) (V : skewAdjoint.submodule ℝ (Mat R)) :
    skewAdjoint.submodule ℝ (Mat R) :=
  ⟨star (T : Mat R) * V * T - V, by
    change star (star (T : Mat R) * (V : Mat R) * T - V) = -_
    rw [star_sub, star_mul, star_mul, star_star, V.property]
    noncomm_ring⟩

end KervaireIncidenceCurrent

open scoped ComplexOrder
namespace KervaireSkewTrace
variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "M" => Matrix I I ℂ
local notation "S" => skewAdjoint.submodule ℝ M

/-- The positive invariant trace pairing on skew-Hermitian matrices. -/
def pairing : LinearMap.BilinForm ℝ S where
  toFun a :=
    { toFun := fun b ↦ -(Matrix.trace ((a : M) * (b : M))).re
      map_add' b c := by
        change -(trace ((a : M) * ((b : M) + (c : M)))).re =
          -(trace ((a : M)*(b : M))).re + -(trace ((a : M)*(c : M))).re
        rw [mul_add, trace_add, Complex.add_re]
        ring
      map_smul' := by intros; simp }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    change -(trace (((a : M)+(b : M))*(c : M))).re =
      -(trace ((a : M)*(c : M))).re + -(trace ((b : M)*(c : M))).re
    rw [add_mul, trace_add, Complex.add_re]
    ring
  map_smul' r a := by ext c; simp

def bracket (a b : S) : S :=
  ⟨(a : M)*(b : M)-(b : M)*(a : M), by
    change star ((a : M)*(b : M)-(b : M)*(a : M)) = -_
    rw [star_sub, star_mul, star_mul, a.property, b.property]
    simp only [neg_mul_neg]
    abel⟩

end KervaireSkewTrace
namespace KervaireIncidenceCurrent
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

/-- The redundant compact group has a canonically chosen horizontal frame. -/
def direction : Horizontal K R →ₗ[ℝ] skewAdjoint.submodule ℝ (Alg K R) where
  toFun h := ⟨((h.1 : Mat K),off h.2.2,(h.2.1 : Mat R)), by
    change (star (h.1 : Mat K),star (off h.2.2),star (h.2.1 : Mat R)) = -_
    rw [h.1.property, h.2.1.property, off_skew]
    rfl⟩
  map_add' h g := by
    apply Subtype.ext
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    change off (h.2.2+g.2.2) = off h.2.2+off g.2.2
    simp only [off, conjTranspose_add, neg_add_rev, fromBlocks_add]
    congr 1 <;> first | simp only [zero_add] | exact add_comm _ _
  map_smul' c h := by
    apply Subtype.ext
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    ext i j
    cases i <;> cases j <;> simp [off, fromBlocks, conjTranspose_smul]

/-- Lower block of the bracket of two off-diagonal skew matrices. -/
def rectBracket (Z Y : Matrix R K ℂ) : skewAdjoint.submodule ℝ (Mat R) :=
  ⟨-Z*Yᴴ+Y*Zᴴ, by
    change (-Z*Yᴴ+Y*Zᴴ)ᴴ = -(-Z*Yᴴ+Y*Zᴴ)
    simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_neg,
      conjTranspose_conjTranspose]
    simp only [Matrix.mul_neg, Matrix.neg_mul]
    abel⟩

omit [Fintype R] [DecidableEq K] [DecidableEq R] in
@[simp] lemma rectBracket_zero_left (Y : Matrix R K ℂ) : rectBracket 0 Y = 0 := by
  apply Subtype.ext
  simp [rectBracket]
omit [Fintype R] [DecidableEq K] [DecidableEq R] in
@[simp] lemma rectBracket_zero_right (Z : Matrix R K ℂ) : rectBracket Z 0 = 0 := by
  apply Subtype.ext
  simp [rectBracket]
@[simp] lemma compensated_zero (T : unitary (Mat R)) : compensated T 0 = 0 := by
  apply Subtype.ext
  simp [compensated]
@[simp] lemma skewBracket_zero_left (b : skewAdjoint.submodule ℝ (Mat K)) :
    KervaireSkewTrace.bracket 0 b = 0 := by
  apply Subtype.ext
  simp [KervaireSkewTrace.bracket]
@[simp] lemma skewBracket_zero_right (a : skewAdjoint.submodule ℝ (Mat K)) :
    KervaireSkewTrace.bracket a 0 = 0 := by
  apply Subtype.ext
  simp [KervaireSkewTrace.bracket]

/-- The defect of horizontal integrability is vertical and is absorbed by T. -/
def effectiveBracket (T : unitary (Mat R)) (h g : Horizontal K R) : Horizontal K R :=
  (KervaireSkewTrace.bracket h.1 g.1,
   KervaireSkewTrace.bracket h.2.1 g.2.1 + compensated T (rectBracket h.2.2 g.2.2),0)

variable {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))

def horizontalBasis : Basis (IK ⊕ IR ⊕ IZ) ℝ (Horizontal K R) := bK.prod (bR.prod bZ)

end KervaireIncidenceCurrent

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.IncidenceTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder

namespace KervaireIncidenceCurrent

section
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

def horizontalInput (p : Alg K R) : Horizontal K R →ₗ[ℝ] (ℝ × Alg K R) where
  toFun h := (0,p*(direction h : Alg K R))
  map_add' h g := by
    change (0,p*(direction (h+g) : Alg K R)) = _
    rw [map_add]
    change ((0 : ℝ),p*((direction h : Alg K R)+(direction g : Alg K R))) =
      (0,p*(direction h : Alg K R))+(0,p*(direction g : Alg K R))
    rw [mul_add]
    exact Prod.ext (zero_add 0).symm rfl
  map_smul' c h := by
    change (0,p*(direction (c • h) : Alg K R)) = _
    rw [map_smul]
    change ((0 : ℝ),p*(c • (direction h : Alg K R))) = c • (0,p*(direction h : Alg K R))
    rw [mul_smul_comm]
    simp only [Prod.smul_mk,smul_zero]

def horizontalDifferential (f : ℝ × Mat K → Mat (K ⊕ R)) (t : ℝ) (p : Alg K R) :
    Horizontal K R →ₗ[ℝ] Mat (K ⊕ R) :=
  (fderiv ℝ (incidence f) (t,p)).toLinearMap.comp (horizontalInput p)

end

end KervaireIncidenceCurrent

namespace KervaireFixedSpace
open Matrix
variable {K R : Type*}
abbrev Skew (K : Type*) := skewAdjoint (Matrix K K ℂ)

/-- Entrywise skew-Hermitian symmetry. -/
theorem skew_entry (T : Skew K) (i j : K) : star (T.val j i) = -T.val i j := by
  exact congrFun (congrFun T.property i) j

/-- The first diagonal block of a skew-Hermitian matrix. -/
def skewBlock11 (T : Skew (K ⊕ R)) : Skew K :=
  ⟨T.val.toBlocks₁₁, by
    ext i j
    exact skew_entry T (Sum.inl i) (Sum.inl j)⟩

/-- The second diagonal block of a skew-Hermitian matrix. -/
def skewBlock22 (T : Skew (K ⊕ R)) : Skew R :=
  ⟨T.val.toBlocks₂₂, by
    ext i j
    exact skew_entry T (Sum.inr i) (Sum.inr j)⟩

/-- The block formula for the incidence derivative. -/
def derivativeMatrix (ε : ℝ) (A : Skew K) (B : Skew R) (Z : Matrix R K ℂ) :
    Matrix (K ⊕ R) (K ⊕ R) ℂ :=
  fromBlocks (ε • A.val) ((2 : ℝ) • Zᴴ) ((-2 : ℝ) • Z) (-B.val)

theorem derivativeMatrix_skew (ε : ℝ) (A : Skew K) (B : Skew R) (Z : Matrix R K ℂ) :
    derivativeMatrix ε A B Z ∈ skewAdjoint (Matrix (K ⊕ R) (K ⊕ R) ℂ) := by
  change star (derivativeMatrix ε A B Z) = -derivativeMatrix ε A B Z
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [derivativeMatrix, Matrix.star_apply, Matrix.fromBlocks, skew_entry]
  · simp [derivativeMatrix, Matrix.star_apply, Matrix.fromBlocks]
  · simp [derivativeMatrix, Matrix.star_apply, Matrix.fromBlocks]
  · simp [derivativeMatrix, Matrix.star_apply, Matrix.fromBlocks, skew_entry]

def degreeDerivative (ε : ℝ) : (Skew K × Skew R × Matrix R K ℂ) →ₗ[ℝ] Skew (K ⊕ R) where
  toFun v := ⟨derivativeMatrix ε v.1 v.2.1 v.2.2,
    derivativeMatrix_skew ε v.1 v.2.1 v.2.2⟩
  map_add' v w := by
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [derivativeMatrix, Matrix.fromBlocks, smul_add]; abel
  map_smul' c v := by
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [derivativeMatrix, Matrix.fromBlocks, smul_comm ε c, smul_comm (2 : ℝ) c,
        smul_comm (-2 : ℝ) c]

/-- Explicit inverse coordinates of the differential; no finite-dimensional
or genericity assumption is needed for this algebraic step. -/
def inverseDerivative (ε : ℝ) (T : Skew (K ⊕ R)) : Skew K × Skew R × Matrix R K ℂ :=
  (ε⁻¹ • skewBlock11 T, -skewBlock22 T, (-((2 : ℝ)⁻¹)) • T.val.toBlocks₂₁)

theorem degreeDerivative_inverse (ε : ℝ) (hε : ε ≠ 0) (T : Skew (K ⊕ R)) :
    degreeDerivative ε (inverseDerivative ε T) = T := by
  apply Subtype.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [degreeDerivative, inverseDerivative, derivativeMatrix, skewBlock11,
      Matrix.fromBlocks, Matrix.toBlocks₁₁, smul_smul, hε]
  · simp [degreeDerivative, inverseDerivative, derivativeMatrix, Matrix.fromBlocks,
      Matrix.toBlocks₂₁, smul_smul, skew_entry]
  · simp [degreeDerivative, inverseDerivative, derivativeMatrix, Matrix.fromBlocks,
      Matrix.toBlocks₂₁, smul_smul]
  · simp [degreeDerivative, inverseDerivative, derivativeMatrix, skewBlock22,
      Matrix.fromBlocks, Matrix.toBlocks₂₂]

theorem inverse_degreeDerivative (ε : ℝ) (hε : ε ≠ 0) (v : Skew K × Skew R × Matrix R K ℂ) :
    inverseDerivative ε (degreeDerivative ε v) = v := by
  apply Prod.ext
  · apply Subtype.ext
    ext i j
    simp [inverseDerivative, degreeDerivative, derivativeMatrix, skewBlock11,
      Matrix.toBlocks₁₁, Matrix.fromBlocks, hε]
  · apply Prod.ext
    · apply Subtype.ext
      ext i j
      simp [inverseDerivative, degreeDerivative, derivativeMatrix, skewBlock22,
        Matrix.toBlocks₂₂, Matrix.fromBlocks]
    · ext i j
      simp [inverseDerivative, degreeDerivative, derivativeMatrix, Matrix.toBlocks₂₁,
        Matrix.fromBlocks]

/-- The differential at the regular fiber is a real-linear isomorphism. -/
def degreeDerivativeEquiv (ε : ℝ) (hε : ε ≠ 0) :
    (Skew K × Skew R × Matrix R K ℂ) ≃ₗ[ℝ] Skew (K ⊕ R) :=
  { degreeDerivative ε with
    invFun := inverseDerivative ε
    left_inv := inverse_degreeDerivative ε hε
    right_inv := degreeDerivative_inverse ε hε }

end KervaireFixedSpace

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.UnitaryHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff

namespace KervaireUnitaryHomotopy
variable (B C : Type*) [CStarAlgebra B] [CStarAlgebra C]

/-- A smooth ambient representative of a smooth unitary-valued map. -/
structure UMap where
  toFun : B → C
  smooth : ContDiff ℝ ∞ toFun
  unitary : ∀ x : unitary B, toFun (x : B) ∈ unitary C

instance instCoeFunUMapForall : CoeFun (UMap B C) (fun _ ↦ B → C) := ⟨UMap.toFun⟩

variable {B C}

/-- Elementary smooth homotopy; equalities only concern the unitary domain. -/
def Elementary (F G : UMap B C) : Prop :=
  ∃ H : ℝ × B → C, ContDiff ℝ ∞ H ∧
    (∀ t (x : unitary B), H (t,(x : B)) ∈ unitary C) ∧
    (∀ x : unitary B, H (0,(x : B)) = F x) ∧
    (∀ x : unitary B, H (1,(x : B)) = G x)

/-- Finite chains suffice, so no smooth concatenation theorem is assumed. -/
def Homotopic (F G : UMap B C) : Prop := Relation.EqvGen Elementary F G

section Differential
variable {E D : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]
  [StarRing E] [ContinuousStar E] [StarModule ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
local instance instNormedAlgebraRat_solutions : NormedAlgebra ℚ E := .restrictScalars ℚ ℝ E

end Differential

end KervaireUnitaryHomotopy

namespace KervaireIncidenceCurrent

section
open MeasureTheory KervaireUnitaryHomotopy
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))
  [MeasurableSpace (unitary (Alg K R))] [BorelSpace (unitary (Alg K R))]
  {μ : Measure (unitary (Alg K R))} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

/-- An ambient representative independent of the time coordinate. -/
def timeless (F : UMap (Mat K) (Mat (K ⊕ R))) : ℝ × Mat K → Mat (K ⊕ R) :=
  fun p ↦ F p.2

/-- The compact horizontal current evaluated on a smooth unitary map. -/
def current {n : ℕ} (b : Fin n → Horizontal K R)
    (form : Mat (K ⊕ R) → Mat (K ⊕ R) [⋀^Fin n]→L[ℝ] ℝ)
    (F : UMap (Mat K) (Mat (K ⊕ R))) : ℝ :=
  ∫ p : unitary (Alg K R), form (incidence (timeless F) (0,(p : Alg K R)))
    (fun i ↦ fderiv ℝ (incidence (timeless F)) (0,(p : Alg K R))
      (0,(p : Alg K R)*(direction (b i) : Alg K R))) ∂μ

end

variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

def model : ℝ × Mat K → Mat (K ⊕ R) := fun p ↦ diag p.2 (-1)

/-- Conjugation is a real linear automorphism of the skew-Hermitian space. -/
def skewConj (U : unitary (Mat K)) :
    skewAdjoint.submodule ℝ (Mat K) ≃ₗ[ℝ] skewAdjoint.submodule ℝ (Mat K) where
  toFun A := ⟨star (U : Mat K)*(A : Mat K)*U, by
    change star (star (U : Mat K)*(A : Mat K)*U) = -_
    rw [star_mul,star_mul,star_star,A.property]
    simp [mul_assoc]⟩
  invFun A := ⟨(U : Mat K)*(A : Mat K)*star (U : Mat K), by
    change star ((U : Mat K)*(A : Mat K)*star (U : Mat K)) = -_
    rw [star_mul,star_mul,star_star,A.property]
    simp [mul_assoc]⟩
  left_inv A := by
    apply Subtype.ext
    change (U : Mat K)*(star (U : Mat K)*(A : Mat K)*U)*star (U : Mat K) = A
    simp only [mul_assoc, U.property.2, mul_one]
    rw [← mul_assoc,U.property.2,one_mul]
  right_inv A := by
    apply Subtype.ext
    change star (U : Mat K)*((U : Mat K)*(A : Mat K)*star (U : Mat K))*U = A
    simp only [mul_assoc,U.property.1,mul_one]
    rw [← mul_assoc,U.property.1,one_mul]
  map_add' A B := by apply Subtype.ext; simp [mul_add,add_mul]
  map_smul' c A := by apply Subtype.ext; simp

def gaugeFrame (U : unitary (Mat K)) (V : unitary (Mat R)) : unitary (Mat (K ⊕ R)) :=
  ⟨diag (U : Mat K) (V : Mat R),diag_unitary U.property V.property⟩

def gaugePoint (U : unitary (Mat K)) (V : unitary (Mat R)) : unitary (Alg K R) :=
  ⟨(1,(gaugeFrame U V : Mat (K ⊕ R)),-1), by
    constructor <;> apply Prod.ext
    · simp
    · exact Prod.ext (gaugeFrame U V).property.1 (by simp)
    · simp
    · exact Prod.ext (gaugeFrame U V).property.2 (by simp)⟩

def modelHorizontalEquiv (U : unitary (Mat K)) (V : unitary (Mat R)) :
    Horizontal K R ≃ₗ[ℝ] skewAdjoint.submodule ℝ (Mat (K ⊕ R)) :=
  ((skewConj U).prodCongr (LinearEquiv.refl ℝ _)) |>.trans
    ((KervaireFixedSpace.degreeDerivativeEquiv (K := K) (R := R) 1 one_ne_zero).trans
      (skewConj (star (gaugeFrame U V))))

end KervaireIncidenceCurrent

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.IncidenceDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff

namespace KervaireIncidenceCurrent
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

/-- The ambient projection onto the skew-Hermitian tangent at the identity. -/
def skewPart {I : Type*} [Fintype I] [DecidableEq I] :
    Mat I →ₗ[ℝ] skewAdjoint.submodule ℝ (Mat I) where
  toFun A := ⟨(1/2 : ℝ) • (A-star A), by
    change star ((1/2 : ℝ) • (A-star A)) = -((1/2 : ℝ) • (A-star A))
    simp only [star_smul,star_sub,star_star,star_trivial]
    rw [← neg_sub A (star A),smul_neg]⟩
  map_add' A B := by
    apply Subtype.ext
    change (1/2 : ℝ) • ((A+B)-star (A+B)) =
      (1/2 : ℝ) • (A-star A)+(1/2 : ℝ) • (B-star B)
    rw [star_add]
    module
  map_smul' c A := by
    apply Subtype.ext
    change (1/2 : ℝ) • (c • A-star (c • A)) = c • ((1/2 : ℝ) • (A-star A))
    simp only [star_smul,star_trivial]
    module

@[simp] lemma skewPart_coe {I : Type*} [Fintype I] [DecidableEq I]
    (A : skewAdjoint.submodule ℝ (Mat I)) : skewPart (A : Mat I) = A := by
  apply Subtype.ext
  change (1/2 : ℝ) • ((A : Mat I)-star (A : Mat I)) = A
  rw [A.property]
  module

/-- A constant ambient form restricting to the determinant volume on the unitary tangent. -/
def tangentVolume {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (b : Basis J ℝ (skewAdjoint.submodule ℝ (Mat I))) : Mat I [⋀^J]→L[ℝ] ℝ where
  toAlternatingMap := b.det.compLinearMap skewPart
  cont := by
    change Continuous (fun v : J → Mat I ↦ b.det (fun j ↦ skewPart (v j)))
    simp only [Basis.det_apply]
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun v : J → Mat I ↦ (b.coord i) (skewPart (v j)))
    exact (b.coord i).continuous_of_finiteDimensional.comp
      (skewPart.continuous_of_finiteDimensional.comp (continuous_apply j))

end KervaireIncidenceCurrent

open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator

namespace KervaireUnitaryExponential
variable {A : Type*} [CStarAlgebra A]
local instance instNormedAlgebraRat_solutions : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A

end KervaireUnitaryExponential

namespace KervaireIncidenceCurrent
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {J : Type*} [Fintype J] [DecidableEq J]

def jacobian (b : Basis J ℝ (Horizontal K R))
    (c : Basis J ℝ (skewAdjoint.submodule ℝ (Mat (K ⊕ R))))
    (f : ℝ × Mat K → Mat (K ⊕ R)) (t : ℝ) (p : Alg K R) : ℝ :=
  tangentVolume c (fun j ↦ fderiv ℝ (incidence f) (t,p) (0,p*(direction (b j) : Alg K R)))

/-- The determinant volume is normalized by the base point's horizontal frame. -/
def modelVolumeBasis (b : Basis J ℝ (Horizontal K R)) :
    Basis J ℝ (skewAdjoint.submodule ℝ (Mat (K ⊕ R))) :=
  b.map (modelHorizontalEquiv 1 1)

end KervaireIncidenceCurrent

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.CurrentExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace KervaireIncidenceCurrent
open MeasureTheory KervaireUnitaryHomotopy
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

def modelMap : UMap (Mat K) (Mat (K ⊕ R)) where
  toFun X := diag X (-1)
  smooth := by
    simp only [diag_eq_corner]
    exact (in11 (K := K) (R := R)).contDiff.add contDiff_const
  unitary X := diag_unitary X.property (by constructor <;> simp)

end KervaireIncidenceCurrent

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.SignedIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace KervaireIncidenceCurrent

section
open KervaireUnitaryHomotopy
variable {K L : Type*} [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]

lemma contDiff_diag {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Mat K} {g : E → Mat L} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x ↦ diag (f x) (g x)) := by
  simp only [diag_eq_corner]
  exact ((in11 (K := K) (R := L)).contDiff.comp hf).add
    ((in22 (K := K) (R := L)).contDiff.comp hg)

def swapBlocks : unitary (Mat (L ⊕ L)) :=
  ⟨Matrix.fromBlocks 0 1 1 0,by
    constructor <;>
      simp [star_eq_conjTranspose,Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_multiply,← Matrix.fromBlocks_one]⟩

def pairedMap (Y : UMap (Mat K) (Mat L)) : UMap (Mat K) (Mat (K ⊕ (L ⊕ L))) where
  toFun X := diag X (diag (Y X) (star (Y X)))
  smooth := contDiff_diag contDiff_id (contDiff_diag Y.smooth ((starL ℝ).contDiff.comp Y.smooth))
  unitary X := diag_unitary X.property (diag_unitary (Y.unitary X) (by
    simpa only [Unitary.star_mem_iff] using Y.unitary X))

def coreMap : UMap (Mat K) (Mat (K ⊕ (L ⊕ L))) where
  toFun X := diag X 1
  smooth := contDiff_diag contDiff_id contDiff_const
  unitary X := diag_unitary X.property (by simp)

def rightMulMap {I : Type*} [Fintype I] [DecidableEq I]
    (F : UMap (Mat K) (Mat I)) (P : unitary (Mat I)) : UMap (Mat K) (Mat I) where
  toFun X := F X * P
  smooth := F.smooth.mul contDiff_const
  unitary X := (unitary _).mul_mem (F.unitary X) P.property

end

section
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

def includeFirst : (K → ℂ) →ₗ[ℂ] ((K ⊕ R) → ℂ) where
  toFun v := Sum.elim v (fun _ ↦ 0)
  map_add' v w := by ext i; cases i <;> simp
  map_smul' c v := by ext i; cases i <;> simp

end

open KervaireUnitaryHomotopy
end KervaireIncidenceCurrent

namespace KervaireSignPairing

section
open Matrix
variable {I K : Type*} [Fintype I]

abbrev positive (s : I → ℤ) := {i // s i = 1}
abbrev negative (s : I → ℤ) := {i // s i ≠ 1}

noncomputable def positiveEquiv (s : I → ℤ)
    (hc : Fintype.card (positive s) = Fintype.card (negative s) + 1) :
    Unit ⊕ negative s ≃ positive s := Fintype.equivOfCardEq (by
  simpa only [Fintype.card_sum,Fintype.card_unit] using (Nat.add_comm _ _).trans hc.symm)

noncomputable def signsEquiv (s : I → ℤ)
    (hc : Fintype.card (positive s) = Fintype.card (negative s) + 1) :
    (Unit ⊕ negative s) ⊕ negative s ≃ I :=
  (Equiv.sumCongr (positiveEquiv s hc) (Equiv.refl _)).trans (Equiv.sumCompl (fun i ↦ s i = 1))

noncomputable def coordinates (s : I → ℤ)
    (hc : Fintype.card (positive s) = Fintype.card (negative s) + 1) :
    K ⊕ ((K × negative s) ⊕ (K × negative s)) ≃ K × I :=
  (Equiv.sumAssoc K (K × negative s) (K × negative s)).symm.trans
    ((Equiv.sumCongr ((Equiv.sumCongr (Equiv.prodUnique K Unit).symm (Equiv.refl _)).trans
      (Equiv.prodSumDistrib K Unit (negative s)).symm) (Equiv.refl _)).trans
        ((Equiv.prodSumDistrib K (Unit ⊕ negative s) (negative s)).symm.trans
          (Equiv.prodCongr (Equiv.refl K) (signsEquiv s hc))))

end

open Matrix KervaireIncidenceCurrent KervaireUnitaryHomotopy
open scoped Matrix.Norms.L2Operator
variable {I K D : Type*} [Fintype I] [Fintype K] [Fintype D]
  [DecidableEq I] [DecidableEq K] [DecidableEq D]

def repeatMatrix (X : Mat K) : Mat (K × D) := blockDiagonal (fun _ ↦ X)

def repeatMap : UMap (Mat K) (Mat (K × D)) where
  toFun := repeatMatrix
  smooth := by
    let L : Mat K →ₗ[ℝ] Mat (K × D) :=
      { toFun := repeatMatrix
        map_add' := by intro X Y; exact blockDiagonal_add _ _
        map_smul' := by intro c X; exact blockDiagonal_smul c _ }
    exact L.toContinuousLinearMap.contDiff
  unitary X := by
    have h1 : (X : Mat K).conjTranspose * X = 1 := X.property.1
    have h2 : (X : Mat K) * (X : Mat K).conjTranspose = 1 := X.property.2
    constructor <;>
      simp only [repeatMatrix,star_eq_conjTranspose,blockDiagonal_conjTranspose,
        ← blockDiagonal_mul,h1,h2]
    all_goals exact blockDiagonal_one

def signedMatrix (s : I → ℤ) (X : Mat K) : Mat (K × I) :=
  blockDiagonal (fun i ↦ if s i = 1 then X else star X)

end KervaireSignPairing

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.FixedSpaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix

namespace KervaireFixed

section
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
def fixedDim (M : Matrix I I ℂ) := Module.finrank ℂ (LinearMap.ker (M.mulVecLin - LinearMap.id))
end

section
open Matrix
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
def reindexUnitary (e : I ≃ J) (P : unitary (Matrix I I ℂ)) : unitary (Matrix J J ℂ) :=
  ⟨Matrix.reindex e e (P : Matrix I I ℂ),by
    let f := Matrix.reindexAlgEquiv ℂ ℂ e
    have hs (M : Matrix I I ℂ) : star (f M) = f (star M) := by
      exact Matrix.conjTranspose_reindex e e M
    change star (f P) * f P = 1 ∧ f P * star (f P) = 1
    constructor
    · rw [hs,← map_mul,P.property.1,map_one]
    · rw [hs,← map_mul,P.property.2,map_one]⟩
end

open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]
abbrev fixedSpace (M : Matrix I I ℂ) := LinearMap.ker (M.mulVecLin - LinearMap.id)
omit [DecidableEq I] in
@[simp] lemma mem_fixedSpace (M : Matrix I I ℂ) (v : I → ℂ) :
    v ∈ fixedSpace M ↔ M.mulVec v = v := by
  simp [fixedSpace, LinearMap.mem_ker, sub_eq_zero]

lemma fixed_star {M : Matrix I I ℂ} (hM : M ∈ unitary (Matrix I I ℂ))
    {v : I → ℂ} (hv : M.mulVec v = v) : (star M).mulVec v = v := by
  calc
    (star M).mulVec v = (star M).mulVec (M.mulVec v) := congrArg _ hv.symm
    _ = v := by rw [mulVec_mulVec, hM.1, one_mulVec]

/-- Both traversal blocks have the same fixed space dimension, without a
spectral-theorem assumption or a nonzero complement assumption. -/
def doubleFixedMap (D P : unitary (Matrix I I ℂ)) :
    (fixedSpace ((D : Matrix I I ℂ) * (P : Matrix I I ℂ)) × fixedSpace ((D : Matrix I I ℂ) * (P : Matrix I I ℂ))) →ₗ[ℂ]
      fixedSpace ((fromBlocks 0 (D : Matrix I I ℂ) (star D : Matrix I I ℂ) 0) *
        (fromBlocks 0 (star P : Matrix I I ℂ) (P : Matrix I I ℂ) 0)) where
  toFun v := ⟨Sum.elim (v.1 : I → ℂ) ((star D : Matrix I I ℂ).mulVec v.2),by
    rw [mem_fixedSpace]
    have h1 := (mem_fixedSpace _ _).mp v.1.property
    have h2 := fixed_star (mul_mem D.property P.property) ((mem_fixedSpace _ _).mp v.2.property)
    simp only [star_mul] at h2
    rw [fromBlocks_multiply]
    simp only [zero_mul,mul_zero,zero_add,add_zero]
    rw [fromBlocks_mulVec]
    simp only [zero_mulVec,add_zero,zero_add]
    funext i
    cases i with
    | inl i => simpa using congrFun h1 i
    | inr i =>
      change ((star D : Matrix I I ℂ) * (star P : Matrix I I ℂ)).mulVec
        ((star D : Matrix I I ℂ).mulVec v.2) i = ((star D : Matrix I I ℂ).mulVec v.2) i
      have hh := congrArg ((star D : Matrix I I ℂ).mulVec) h2
      simpa only [mulVec_mulVec, mul_assoc] using congrFun hh i⟩
  map_add' v w := by
    apply Subtype.ext
    funext i
    cases i <;> simp [mulVec_add]
  map_smul' c v := by
    apply Subtype.ext
    funext i
    cases i <;> simp [mulVec_smul]

end KervaireFixed

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.Traversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix

namespace KervaireTraversal

section
open Matrix KervaireFixed KervaireSignPairing
open scoped Classical
variable {I K : Type*} [Fintype I] [Fintype K]
abbrev Slots (I K : Type*) := (K ⊕ K) × I

def coordinates (s : I → ℤ) : ((K × I) ⊕ (K × I)) ≃ Slots I K where
  toFun p := match p with
    | .inl (k,i) => (if s i = 1 then Sum.inl k else Sum.inr k, i)
    | .inr (k,i) => (if s i = 1 then Sum.inr k else Sum.inl k, i)
  invFun p := match p with
    | (.inl k,i) => if s i = 1 then Sum.inl (k,i) else Sum.inr (k,i)
    | (.inr k,i) => if s i = 1 then Sum.inr (k,i) else Sum.inl (k,i)
  left_inv p := by rcases p with ⟨k,i⟩ | ⟨k,i⟩ <;> by_cases h : s i = 1 <;> simp [h]
  right_inv p := by rcases p with ⟨k|k,i⟩ <;> by_cases h : s i = 1 <;> simp [h]

def mixer (X : Matrix K K ℂ) : Matrix (Slots I K) (Slots I K) ℂ :=
  blockDiagonal fun _ : I => fromBlocks 0 (star X) X 0

def exchange (P : Matrix (K × I) (K × I) ℂ) :
    Matrix ((K × I) ⊕ (K × I)) ((K × I) ⊕ (K × I)) ℂ := fromBlocks 0 (star P) P 0

end

open Matrix KervaireFixed
open scoped Classical
variable {I K : Type*} [Fintype I] [Fintype K] [Nonempty K]
local instance instDecidableEqSlots : DecidableEq (Slots I K) := Classical.decEq _

end KervaireTraversal

namespace KervaireMatrix
open Matrix KervaireRegular
open scoped Classical
variable {D : Type*} [Fintype D]

/-- The exact scalar weighted permutation attached to the oriented bands. -/
def monomial (θ : Equiv.Perm D) (u : D → ℂ) : Matrix D D ℂ :=
  fun i j ↦ if i = θ j then u j else 0

@[simp] lemma monomial_mul (θ τ : Equiv.Perm D) (u v : D → ℂ) :
    monomial θ u * monomial τ v = monomial (θ*τ) (fun j ↦ u (τ j)*v j) := by
  ext i j
  simp only [Matrix.mul_apply,monomial]
  rw [Finset.sum_eq_single (τ j)]
  · simp only
    change (if i = θ (τ j) then u (τ j) else 0) * v j =
      if i = θ (τ j) then u (τ j)*v j else 0
    split_ifs <;> simp
  · intro k _ hk
    simp [hk]
  · simp

omit [Fintype D] in
@[simp] lemma monomial_one [DecidableEq D] : monomial (Equiv.refl D) (fun _ ↦ 1) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [monomial,Matrix.one_apply,h]

end KervaireMatrix

namespace KervaireMixing
open Matrix KervaireMatrix KervaireRegular KervaireFixed
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A] [Nonempty I] [Nonempty K]
local instance instDecidableEqSlot : DecidableEq (Slot I K) := Classical.decEq _

end KervaireMixing

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.BoundaryFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix

namespace KervaireFlow

section
open scoped Classical
variable {D Z : Type*} [Fintype D] [Fintype Z]

def antisymmetric (θ : Equiv.Perm D) : Submodule ℝ (D → ℝ) where
  carrier := {γ | ∀ d, γ (θ d) = -γ d}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy d
    change x (θ d) + y (θ d) = -(x d + y d)
    rw [hx d, hy d, neg_add]
  smul_mem' := by
    intro r x hx d
    change r • x (θ d) = -(r • x d)
    rw [hx d, smul_neg]

/-- Literal sum of corner phases on each boundary circle. -/
def divergence (b : D → Z) : (D → ℝ) →ₗ[ℝ] (Z → ℝ) where
  toFun γ z := ∑ d, if b d = z then γ d else 0
  map_add' γ δ := by
    ext z
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> simp
  map_smul' r γ := by
    ext z
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> simp

/-- Supported on the two ends of one band, including the harmless loop case. -/
def edgeFlow (θ : Equiv.Perm D) (d : D) : D → ℝ :=
  Pi.single d 1 - Pi.single (θ d) 1

/-- Adjacency in the graph dual to the band sides, with orientations retained. -/
def Adj (b : D → Z) (θ : Equiv.Perm D) (x y : Z) : Prop :=
  ∃ d, b d = x ∧ b (θ d) = y

end

end KervaireFlow
namespace KervaireBoundary

section
open Matrix KervaireMatrix KervaireRegular KervaireSpectral KervaireMixing KervaireTraversal
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]
local instance instDecidableEqSlot : DecidableEq (Slot I K) := Classical.decEq _

def traversalSign (s : I → ℤ) : Slot I K → ℤ
  | (.inl _,i) => s i
  | (.inr _,i) => -s i

end
open KervaireCycle KervaireSpectral KervaireMatrix KervaireRegular KervaireMixing KervaireTraversal
open scoped Classical
end KervaireBoundary

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.RelatorRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D A : Type*} [Fintype D] [DecidableEq D] [Group A]

/-- The coefficient on the corner immediately following a dart. -/
def corner (σ θ : Perm D) (u : D → A) (d : D) : A := u (θ d) * (u (σ d))⁻¹

end

section
open Equiv Equiv.Perm
open scoped Classical
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

omit [Fintype B] [DecidableEq B] in
lemma components_map (e : D → B) (σ θ : Perm D) (σ' θ' : Perm B)
    (hs : ∀ d, e (σ d) = σ' (e d)) (ht : ∀ d, e (θ d) = θ' (e d))
    {x y : D} (h : components σ θ x y) : components σ' θ' (e x) (e y) := by
  have hl : components σ θ ≤ (components σ' θ').comap e := by
    apply sup_le
    · apply cycle_le_of_step
      intro d
      change components σ' θ' (e (σ d)) (e d)
      rw [hs]
      exact (le_sup_left : SameCycle.setoid σ' ≤ components σ' θ') SameCycle.rfl.apply_left
    · apply cycle_le_of_step
      intro d
      change components σ' θ' (e (θ d)) (e d)
      rw [ht]
      exact (le_sup_right : SameCycle.setoid θ' ≤ components σ' θ') SameCycle.rfl.apply_left
  exact hl h

end

open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

def vertexNext (ρ : Perm I) (ε : V → ℤ) (p : V × I) : V × I :=
  (p.1, if ε p.1 = 1 then ρ p.2 else ρ.symm p.2)
def vertexCorner (ρ : Perm I) (a : I → A) (ε : V → ℤ) (p : V × I) : A :=
  if ε p.1 = 1 then a p.2 else (a (ρ.symm p.2))⁻¹

/-- Disjoint relator disks in a larger ribbon diagram. The other darts may
belong to an outside word or be isolated markers from previous cancellations. -/
structure DiskAtlas (ρ : Perm I) (a : I → A) (s : I → ℤ)
    (σ : Perm D) (t : D → ℤ) where
  disk : V × I ↪ D
  ε : V → ℤ
  polarity : ∀ v, ε v = 1 ∨ ε v = -1
  next : ∀ v i, σ (disk (v,i)) = disk (vertexNext ρ ε (v,i))
  sign : ∀ v i, t (disk (v,i)) = ε v*s i

end KervaireRibbon

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.VertexJoin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
lemma planar_vertex_join (σ θ : Perm D) {x y : D} (hxy : ¬ components σ θ x y)
    (hp : planar σ θ) : planar (swap x y * σ) θ := by
  have hσ : ¬ σ.SameCycle x y := fun h ↦ hxy ((le_sup_left : SameCycle.setoid σ ≤ components σ θ) h)
  have hφ : ¬ (σ*θ).SameCycle x y := fun h ↦ hxy (cycles_mul_le σ θ (components σ θ) le_sup_left le_sup_right h)
  have hv := numCycles_swap_merge σ hσ
  have hf := numCycles_swap_merge (σ*θ) hφ
  have hc : components (swap x y*σ) θ x y :=
    (le_sup_left : SameCycle.setoid (swap x y*σ) ≤ components (swap x y*σ) θ) (sameCycle_swap_merges σ hσ)
  have hr := components_swap_sup σ θ x y
  rw [joinPair_eq _ hc] at hr
  have hcr := classes_joinPair (components σ θ) hxy
  unfold planar at hp ⊢
  rw [hr,mul_assoc]
  omega

omit [DecidableEq D] [DecidableEq E] in
lemma card_quotient_ker {B : Type*} [Fintype B] (f : D → B) (hf : Function.Surjective f) :
    classes (Setoid.ker f) = Fintype.card B := by
  let e : Quotient (Setoid.ker f) ≃ B := Equiv.ofBijective
    (Quotient.lift f (fun _ _ h ↦ h)) (by
      constructor
      · intro x y
        induction x using Quotient.inductionOn with | h x =>
          induction y using Quotient.inductionOn with | h y =>
            exact fun h ↦ Quotient.sound h
      · intro b; obtain ⟨d,rfl⟩ := hf b; exact ⟨Quotient.mk _ d,rfl⟩)
  exact Fintype.card_congr e

omit [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E] in
lemma sumPerm_zpow (σ : Perm D) (τ : Perm E) (n : ℤ) :
    (σ.sumCongr τ)^n = (σ^n).sumCongr (τ^n) := by
  exact (map_zpow (sumCongrHom D E) (σ,τ) n).symm

omit [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E] in
lemma sameCycle_sumPerm (σ : Perm D) (τ : Perm E) (x y : D ⊕ E) :
    (σ.sumCongr τ).SameCycle x y ↔
      Sum.map (Quotient.mk (SameCycle.setoid σ)) (Quotient.mk (SameCycle.setoid τ)) x =
      Sum.map (Quotient.mk (SameCycle.setoid σ)) (Quotient.mk (SameCycle.setoid τ)) y := by
  cases x <;> cases y <;>
    simp only [SameCycle,sumPerm_zpow,Equiv.Perm.sumCongr_apply,Sum.map_inl,Sum.map_inr,
      Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,exists_const]
  · exact ⟨fun h ↦ Quotient.sound (s := SameCycle.setoid σ) h,fun h ↦ Quotient.exact h⟩
  · exact ⟨fun h ↦ Quotient.sound (s := SameCycle.setoid τ) h,fun h ↦ Quotient.exact h⟩

omit [DecidableEq D] [DecidableEq E] in
lemma numCycles_sumPerm (σ : Perm D) (τ : Perm E) :
    numCycles (σ.sumCongr τ) = numCycles σ + numCycles τ := by
  let f : D ⊕ E → Cycles σ ⊕ Cycles τ := Sum.map (Quotient.mk _) (Quotient.mk _)
  have hf : Function.Surjective f := by
    rintro (x|y)
    · exact ⟨Sum.inl x.out,congrArg Sum.inl x.out_eq⟩
    · exact ⟨Sum.inr y.out,congrArg Sum.inr y.out_eq⟩
  rw [numCycles_eq_card (σ.sumCongr τ) f hf (sameCycle_sumPerm σ τ),Fintype.card_sum]
  rfl

lemma components_sumPerm (σ θ : Perm D) (τ η : Perm E) :
    components (σ.sumCongr τ) (θ.sumCongr η) =
      Setoid.ker (Sum.map (Quotient.mk (components σ θ)) (Quotient.mk (components τ η))) := by
  let f := Sum.map (Quotient.mk (components σ θ)) (Quotient.mk (components τ η))
  apply le_antisymm
  · apply sup_le
    · apply cycle_le_of_step
      intro d
      cases d with
      | inl d => exact congrArg Sum.inl (Quotient.sound ((le_sup_left : SameCycle.setoid σ ≤ components σ θ) SameCycle.rfl.apply_left))
      | inr d => exact congrArg Sum.inr (Quotient.sound ((le_sup_left : SameCycle.setoid τ ≤ components τ η) SameCycle.rfl.apply_left))
    · apply cycle_le_of_step
      intro d
      cases d with
      | inl d => exact congrArg Sum.inl (Quotient.sound ((le_sup_right : SameCycle.setoid θ ≤ components σ θ) SameCycle.rfl.apply_left))
      | inr d => exact congrArg Sum.inr (Quotient.sound ((le_sup_right : SameCycle.setoid η ≤ components τ η) SameCycle.rfl.apply_left))
  · intro x y h
    change f x = f y at h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        exact components_map Sum.inl σ θ _ _ (fun _ ↦ rfl) (fun _ ↦ rfl) (Quotient.exact (Sum.inl.inj h))
      | inr y => simp only [f,Sum.map_inl,Sum.map_inr,Sum.inl_ne_inr] at h
    | inr x =>
      cases y with
      | inl y => simp only [f,Sum.map_inl,Sum.map_inr,Sum.inr_ne_inl] at h
      | inr y =>
        exact components_map Sum.inr τ η _ _ (fun _ ↦ rfl) (fun _ ↦ rfl) (Quotient.exact (Sum.inr.inj h))

lemma planar_sumPerm (σ θ : Perm D) (τ η : Perm E) (h₁ : planar σ θ) (h₂ : planar τ η) :
    planar (σ.sumCongr τ) (θ.sumCongr η) := by
  have hf : Function.Surjective (Sum.map (Quotient.mk (components σ θ)) (Quotient.mk (components τ η))) := by
    rintro (x|y)
    · exact ⟨Sum.inl x.out,congrArg Sum.inl x.out_eq⟩
    · exact ⟨Sum.inr y.out,congrArg Sum.inr y.out_eq⟩
  unfold planar at h₁ h₂ ⊢
  rw [components_sumPerm,card_quotient_ker _ hf,Fintype.card_sum]
  have he : (σ.sumCongr τ)*(θ.sumCongr η) = (σ*θ).sumCongr (τ*η) := by
    exact (map_mul (sumCongrHom D E) (σ,τ) (θ,η)).symm
  rw [he,numCycles_sumPerm,numCycles_sumPerm,numCycles_sumPerm,Fintype.card_sum]
  change _ = _ + 2*(classes (components σ θ)+classes (components τ η))
  omega

omit [Fintype E] [DecidableEq E] [DecidableEq D] in
lemma planar_one_right (σ : Perm D) : planar σ 1 := by
  have ho : SameCycle.setoid (1 : Perm D) = ⊥ := by ext x y; exact sameCycle_one
  unfold planar components
  rw [ho,sup_bot_eq,mul_one,numCycles_one]
  change numCycles σ + Fintype.card D + numCycles σ = Fintype.card D + 2*numCycles σ
  omega
end KervaireRibbon

end
end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.Circles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [DecidableEq D] [Finite D]

def Circle (σ : Perm D) (o : D) (l : List D) : Prop :=
  (o :: (l ++ [o])).IsChain (fun x y ↦ σ x = y)

end
open Monoid Multiplicative
open scoped Classical
variable {D A : Type*} [Group A]
abbrev FreeProd (A : Type*) [Group A] := Coprod A (Multiplicative ℤ)
def dartLetter (t : D → ℤ) (c : D → A) (d : D) : FreeProd A :=
  Coprod.inr (ofAdd (t d)) * Coprod.inl (c d)
def dartEval (t : D → ℤ) (c : D → A) (l : List D) : FreeProd A := (l.map (dartLetter t c)).prod

lemma dartEval_cons (t : D → ℤ) (c : D → A) (d : D) (l : List D) :
    dartEval t c (d::l) = dartLetter t c d * dartEval t c l := rfl

end KervaireRibbon

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.Splicing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D E B : Type*} [DecidableEq D] [DecidableEq E]

def splice (σ : Perm D) (τ : Perm E) (o : D) (p : E) : Perm (D ⊕ E) :=
  erase (swap (Sum.inl o) (Sum.inr p) * (σ.sumCongr τ)) (Sum.inr p)

lemma splice_inl (σ : Perm D) (τ : Perm E) (o : D) (p : E) (d : D) :
    splice σ τ o p (Sum.inl d) =
      if σ d = o then (if τ p = p then Sum.inl o else Sum.inr (τ p)) else Sum.inl (σ d) := by
  rw [splice,erase_apply _ _ _ (by simp)]
  simp only [mul_apply,Equiv.Perm.sumCongr_apply,Sum.map_inl,Sum.map_inr]
  by_cases hd : σ d = o
  · rw [hd,swap_apply_left,ite_eq_left rfl,ite_eq_left rfl]
    by_cases hp : τ p = p
    · rw [hp,swap_apply_right,ite_eq_left rfl]
    · rw [swap_apply_of_ne_of_ne (by simp) (by simpa using hp),ite_eq_right hp]
  · rw [swap_apply_of_ne_of_ne (by simpa using hd) (by simp),ite_eq_right (by simp),ite_eq_right hd]

lemma splice_inr (σ : Perm D) (τ : Perm E) (o : D) (p d : E) (hd : d ≠ p) :
    splice σ τ o p (Sum.inr d) = if τ d = p then Sum.inl o else Sum.inr (τ d) := by
  rw [splice,erase_apply _ _ _ (by simpa using hd)]
  simp only [mul_apply,Equiv.Perm.sumCongr_apply,Sum.map_inr]
  by_cases hp : τ d = p
  · rw [hp,swap_apply_right,ite_eq_right (by simp),ite_eq_left rfl]
  · rw [swap_apply_of_ne_of_ne (by simp) (by simpa using hp),ite_eq_right (by simpa using hp),ite_eq_right hp]

lemma splice_marker (σ : Perm D) (τ : Perm E) (o : D) (p : E) :
    splice σ τ o p (Sum.inr p) = Sum.inr p := erase_fixed _ _

omit [DecidableEq E] in
lemma chain_redirect (σ : Perm D) (F : B → B) (f : D → B) (o : D) (q : B)
    (x : D) (l : List D) (hc : (x::(l++[o])).IsChain (fun a b ↦ σ a = b))
    (hno : o ∉ l) (hf : ∀ d ∈ x::l, F (f d) = if σ d = o then q else f (σ d)) :
    (f x :: (l.map f ++ [q])).IsChain (fun a b ↦ F a = b) := by
  induction l generalizing x with
  | nil =>
    have hh : σ x = o := by simpa using hc
    simp only [List.map_nil,List.nil_append,List.isChain_cons_cons,List.isChain_singleton,and_true,
      hf x (by simp),hh,ite_true]
  | cons d l ih =>
    obtain ⟨hxd,ht⟩ := List.isChain_cons_cons.mp hc
    have hd : d ≠ o := fun h ↦ hno (by simp [h])
    apply List.isChain_cons_cons.mpr
    constructor
    · rw [hf x (by simp),hxd,ite_eq_right hd]
    · exact ih d ht (fun h ↦ hno (by simp [h])) (fun z hz ↦ hf z (by simp only [List.mem_cons] at hz ⊢; tauto))

lemma circle_splice [Finite D] [Finite E] (σ : Perm D) (τ : Perm E) (o : D) (p : E)
    (l : List D) (m : List E) (hc : Circle σ o l) (hd : Circle τ p m)
    (hno : o ∉ l) (hnp : p ∉ m) :
    Circle (splice σ τ o p) (Sum.inl o) (l.map Sum.inl ++ m.map Sum.inr) := by
  have hl := chain_redirect σ (splice σ τ o p) Sum.inl o
    (if τ p = p then Sum.inl o else Sum.inr (τ p)) o l hc hno
    (fun d _ ↦ splice_inl σ τ o p d)
  cases m with
  | nil =>
    have hp : τ p = p := by simpa only [Circle,List.nil_append,List.isChain_cons_cons,List.isChain_singleton,and_true] using hd
    simpa only [Circle,List.map_nil,List.append_nil,hp,ite_true] using hl
  | cons d m =>
    have hpd : τ p = d := (List.isChain_cons_cons.mp hd).1
    have hdm := (List.isChain_cons_cons.mp hd).2
    have hdp : d ≠ p := fun h ↦ hnp (by simp [h])
    have hl' : (Sum.inl o :: (l.map Sum.inl ++ [Sum.inr d])).IsChain (fun a b ↦ splice σ τ o p a = b) := by
      simpa only [hpd,ite_eq_right hdp] using hl
    have hm := chain_redirect τ (splice σ τ o p) Sum.inr p (Sum.inl o) d m hdm
      (fun h ↦ hnp (by simp [h])) (fun z hz ↦ splice_inr σ τ o p z (fun h ↦ hnp (h ▸ hz)))
    change (Sum.inl o :: ((l.map Sum.inl ++ Sum.inr d :: m.map Sum.inr) ++ [Sum.inl o])).IsChain _
    have hx : ((Sum.inl o :: l.map Sum.inl) ++ Sum.inr d :: (m.map Sum.inr ++ [Sum.inl o])).IsChain
        (fun a b ↦ splice σ τ o p a = b) :=
      List.isChain_split.mpr ⟨by simpa only [List.cons_append] using hl',hm⟩
    simpa only [List.cons_append,List.append_assoc] using hx

lemma planar_splice [Fintype D] [Fintype E] (σ θ : Perm D) (τ η : Perm E)
    (o : D) (p : E) (h₁ : planar σ θ) (h₂ : planar τ η) :
    planar (splice σ τ o p) (θ.sumCongr η) := by
  have hc : ¬ components (σ.sumCongr τ) (θ.sumCongr η) (Sum.inl o) (Sum.inr p) := by
    rw [components_sumPerm]
    change ¬ Sum.inl (Quotient.mk (components σ θ) o) = Sum.inr (Quotient.mk (components τ η) p)
    simp
  have hp := planar_vertex_join (σ.sumCongr τ) (θ.sumCongr η) hc (planar_sumPerm σ θ τ η h₁ h₂)
  let μ := swap (Sum.inl o) (Sum.inr p) * (σ.sumCongr τ)
  by_cases he : μ (Sum.inr p) = Sum.inr p
  · have hh : erase μ (Sum.inr p) = μ := by ext d; simp [erase,he]
    change planar (erase μ (Sum.inr p)) _
    rw [hh]
    exact hp
  · exact planar_vertex_split μ (θ.sumCongr η) (Ne.symm he) SameCycle.rfl.apply_right hp
end KervaireRibbon

end
end

section
namespace KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma planar_vertex_join_face (σ θ : Perm D) {x y : D}
    (hv : ¬ σ.SameCycle x y) (hf : (σ*θ).SameCycle x y) (hp : planar σ θ) :
    planar (swap x y*σ) θ := by
  have hne : x ≠ y := fun h ↦ hv (h ▸ SameCycle.rfl)
  have hn := numCycles_swap_merge σ hv
  have hm := numCycles_swap_split (σ*θ) hne hf
  have hc : components (swap x y*σ) θ x y :=
    (le_sup_left : SameCycle.setoid (swap x y*σ) ≤ components (swap x y*σ) θ) (sameCycle_swap_merges σ hv)
  have hd : components σ θ x y := cycles_mul_le σ θ _ le_sup_left le_sup_right hf
  have hr := components_swap_sup σ θ x y
  rw [joinPair_eq _ hc,joinPair_eq _ hd] at hr
  unfold planar at hp ⊢
  rw [hr,mul_assoc]
  omega

omit [DecidableEq D] in
lemma planar_one_left (θ : Perm D) : planar 1 θ := by
  have h := planar_one_right θ
  unfold planar components at h ⊢
  simpa only [one_mul,mul_one,sup_comm,Nat.add_comm (numCycles (1:Perm D))] using h

def whisker (σ : Perm D) (o : D) : Perm (D ⊕ Bool) :=
  swap (Sum.inl o) (Sum.inr true) *
    (swap (Sum.inl (σ o)) (Sum.inr false) * (σ.sumCongr 1))

omit [Fintype D] in
lemma whisker_o (σ : Perm D) (o : D) : whisker σ o (Sum.inl o) = Sum.inr false := by
  simp [whisker,swap_apply_def]
omit [Fintype D] in
lemma whisker_y (σ : Perm D) (o : D) : whisker σ o (Sum.inr true) = Sum.inl o := by
  simp [whisker,swap_apply_def]
omit [Fintype D] in
lemma whisker_x (σ : Perm D) (o : D) : whisker σ o (Sum.inr false) =
    if σ o = o then Sum.inr true else Sum.inl (σ o) := by
  simp only [whisker,mul_apply,Equiv.Perm.sumCongr_apply,Sum.map_inr,one_apply,swap_apply_right]
  by_cases he : σ o = o
  · simp only [he,ite_true,swap_apply_left]
  · rw [swap_apply_of_ne_of_ne (by simpa using he) (by simp),ite_eq_right he]
omit [Fintype D] in
lemma whisker_inl (σ : Perm D) (o d : D) (hd : d ≠ o) : whisker σ o (Sum.inl d) =
    if σ d = o then Sum.inr true else Sum.inl (σ d) := by
  simp only [whisker,mul_apply,Equiv.Perm.sumCongr_apply,Sum.map_inl]
  rw [swap_apply_of_ne_of_ne (fun h ↦ hd (σ.injective (Sum.inl.inj h))) (by simp)]
  by_cases he : σ d = o
  · simp only [he,ite_true,swap_apply_left]
  · rw [swap_apply_of_ne_of_ne (by simpa using he) (by simp),ite_eq_right he]

lemma planar_whisker (σ θ : Perm D) (o : D) (ho : θ o = o) (hp : planar σ θ) :
    planar (whisker σ o) (θ.sumCongr (swap false true)) := by
  let τ := σ.sumCongr (1 : Perm Bool)
  let η := θ.sumCongr (swap false true)
  let α := swap (Sum.inl (σ o)) (Sum.inr false) * τ
  have hc : ¬ components τ η (Sum.inl (σ o)) (Sum.inr false) := by
    rw [components_sumPerm]
    change ¬ Sum.inl _ = Sum.inr _
    simp
  have hα := planar_vertex_join τ η hc (planar_sumPerm σ θ 1 (swap false true) hp (planar_one_left _))
  have hy : α (Sum.inr true) = Sum.inr true := by simp [α,τ,swap_apply_def]
  have hv : ¬ α.SameCycle (Sum.inl o) (Sum.inr true) := fun h ↦ Sum.inl_ne_inr (h.eq_of_right hy)
  have hf : (α*η).SameCycle (Sum.inl o) (Sum.inr true) := by
    have he : ((α*η)^2) (Sum.inl o) = Sum.inr true := by
      simp [pow_two,α,τ,η,ho,swap_apply_def]
    exact ⟨(2:ℤ),by simpa only [zpow_ofNat] using he⟩
  exact planar_vertex_join_face α η hv hf hα

omit [Fintype D] in
lemma circle_whisker (σ : Perm D) (o : D) (l : List D) (hc : Circle σ o l) (hn : o ∉ l) :
    Circle (whisker σ o) (Sum.inl o) (Sum.inr false :: l.map Sum.inl ++ [Sum.inr true]) := by
  cases l with
  | nil =>
    have he : σ o = o := by simpa only [Circle,List.nil_append,List.isChain_cons_cons,List.isChain_singleton,and_true] using hc
    simp only [Circle,List.map_nil,List.cons_append,List.nil_append,List.isChain_cons_cons,
      List.isChain_singleton,and_true,whisker_o,whisker_x,he,ite_true,whisker_y]
  | cons d l =>
    have hod : σ o = d := (List.isChain_cons_cons.mp hc).1
    have hdl := (List.isChain_cons_cons.mp hc).2
    have hdo : d ≠ o := fun he ↦ hn (by simp [he])
    have hh := chain_redirect σ (whisker σ o) Sum.inl o (Sum.inr true) d l hdl
      (fun h ↦ hn (by simp [h])) (fun z hz ↦ whisker_inl σ o z (fun he ↦ hn (he ▸ hz)))
    change (Sum.inl o :: Sum.inr false :: ((Sum.inl d :: l.map Sum.inl) ++ [Sum.inr true] ++ [Sum.inl o])).IsChain _
    apply List.isChain_cons_cons.mpr
    refine ⟨whisker_o _ _,?_⟩
    apply List.isChain_cons_cons.mpr
    refine ⟨?_,?_⟩
    · rw [whisker_x,hod,ite_eq_right hdo]
    · have hb : (Sum.inr true :: [Sum.inl o]).IsChain (fun x y ↦ whisker σ o x = y) := by
        simpa only [List.isChain_cons_cons,List.isChain_singleton,and_true] using whisker_y σ o
      have hg : ((Sum.inl d :: l.map Sum.inl) ++ Sum.inr true :: [Sum.inl o]).IsChain
          (fun x y ↦ whisker σ o x = y) :=
        List.isChain_split.mpr ⟨by simpa only [List.cons_append] using hh,hb⟩
      simpa only [List.append_eq,List.cons_append,List.append_assoc,List.singleton_append,List.nil_append] using hg

end KervaireRibbon

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.Capping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D A : Type*} [Fintype D] [DecidableEq D] [Group A]

def capSign (t : D → ℤ) (x y : D) (d : D) : ℤ := if d = x ∨ d = y then 0 else t d

end

open Equiv Equiv.Perm
open scoped Classical
end KervaireRibbon

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.OuterRibbon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

/-- A finite genus-zero relator ribbon with a marked outside vertex. Isolated
zero-sign darts are retained, so cap surgery never changes the finite universe. -/
structure OuterRibbon (ρ : Perm I) (a : I → A) (s : I → ℤ) (o : D) (l : List D) where
  σ : Perm D
  θ : Perm D
  involutive : ∀ d, θ (θ d) = d
  planar' : planar σ θ
  t : D → ℤ
  opposite : ∀ d, t (θ d) = - t d
  marker : θ o = o
  marker_sign : t o = 0
  circle : Circle σ o l
  nodup : (o::l).Nodup
  unit : ∀ d ∈ l, t d = 1 ∨ t d = -1
  atlas : DiskAtlas (V := V) ρ a s σ t
  disjoint : ∀ vi, atlas.disk vi ∉ o::l
  cover : ∀ d, (∃ vi, atlas.disk vi = d) ∨ d ∈ o::l ∨ (σ d = d ∧ θ d = d)
  u : D → A
  corners : ∀ v i, vertexCorner ρ a atlas.ε (v,i) = corner σ θ u (atlas.disk (v,i))

def OuterRibbon.value {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) : FreeProd A :=
  dartEval r.t (corner r.σ r.θ r.u) (o::l)

end
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
end KervaireRibbon

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.RibbonProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {D A : Type*} [Group A]

def transportLetter (θ : Perm D) (t : D → ℤ) (u : D → A) (d : D) : FreeProd A :=
  (Coprod.inl (u d))⁻¹ * Coprod.inr (ofAdd (t d)) * Coprod.inl (u (θ d))
def transportEval (θ : Perm D) (t : D → ℤ) (u : D → A) (l : List D) : FreeProd A :=
  (l.map (transportLetter θ t u)).prod

lemma dartEval_path (σ θ : Perm D) (t : D → ℤ) (u : D → A) (o x : D) (l : List D)
    (hc : (x::(l++[o])).IsChain (fun a b ↦ σ a = b)) :
    (Coprod.inl (u (σ x)))⁻¹ * dartEval t (corner σ θ u) l =
      transportEval θ t u l * (Coprod.inl (u o))⁻¹ := by
  induction l generalizing x with
  | nil =>
    have hh : σ x = o := by simpa only [List.nil_append,List.isChain_cons_cons,List.isChain_singleton,and_true] using hc
    simp only [hh,dartEval,transportEval,List.map_nil,List.prod_nil,mul_one,one_mul]
  | cons d l ih =>
    obtain ⟨hs,ht⟩ := List.isChain_cons_cons.mp hc
    have hi := ih d ht
    simp only [transportEval,List.map_cons,List.prod_cons] at hi ⊢
    rw [hs,dartEval_cons]
    simp only [dartLetter,corner,map_mul,map_inv,transportLetter]
    calc
      _ = ((Coprod.inl (u d))⁻¹ * Coprod.inr (ofAdd (t d)) * Coprod.inl (u (θ d))) *
        ((Coprod.inl (u (σ d)))⁻¹ * dartEval t (corner σ θ u) l) := by group
      _ = _ := by rw [hi]; group

variable {V I : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D]
omit [Fintype V] [Fintype I] [DecidableEq D] in
lemma OuterRibbon.value_formula {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) :
    r.value = Coprod.inl (r.u o) * transportEval r.θ r.t r.u l * (Coprod.inl (r.u o))⁻¹ := by
  have hh := dartEval_path r.σ r.θ r.t r.u o o l r.circle
  simp only [OuterRibbon.value,dartEval_cons,dartLetter,r.marker_sign,ofAdd_zero,map_one,one_mul,
    corner,r.marker,map_mul,map_inv]
  rw [mul_assoc,hh]
  group
end

open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {V W I D E A : Type*} [Fintype V] [Fintype W] [Fintype I]
  [Fintype D] [Fintype E] [DecidableEq D] [DecidableEq E] [Group A]

omit [Fintype V] [Fintype W] [Fintype I] [Fintype D] [Fintype E] [DecidableEq D] [DecidableEq E] in
lemma transportEval_map_gauge (θ : Perm D) (η : Perm E) (t : D → ℤ) (t' : E → ℤ)
    (u : D → A) (u' : E → A) (f : D → E) (h : A)
    (hθ : ∀ d, η (f d) = f (θ d)) (ht : ∀ d, t' (f d) = t d)
    (hu : ∀ d, u' (f d) = u d*h) (l : List D) :
    transportEval η t' u' (l.map f) = (Coprod.inl h)⁻¹ * transportEval θ t u l * Coprod.inl h := by
  induction l with
  | nil => simp [transportEval]
  | cons d l ih =>
    simp only [transportEval,List.map_cons,List.prod_cons] at ih ⊢
    rw [ih]
    simp only [transportLetter,hθ,ht,hu,map_mul,mul_inv_rev]
    group

omit [Fintype V] [Fintype W] [Fintype I] [Fintype D] [Fintype E] [DecidableEq D] [DecidableEq E] in
lemma transportEval_append (θ : Perm D) (t : D → ℤ) (u : D → A) (l m : List D) :
    transportEval θ t u (l++m) = transportEval θ t u l * transportEval θ t u m := by
  simp only [transportEval,List.map_append,List.prod_append]

/-- Gluing the marked outside disks along a zero-sign corner concatenates their
words. The second potential is gauged to agree at the glued marker. -/
def OuterRibbon.mul {ρ : Perm I} {a : I → A} {s : I → ℤ}
    {o : D} {p : E} {l : List D} {m : List E}
    (r : OuterRibbon (V := V) ρ a s o l) (q : OuterRibbon (V := W) ρ a s p m) :
    OuterRibbon (V := V ⊕ W) ρ a s (Sum.inl o) (l.map Sum.inl ++ m.map Sum.inr) := by
  let σ := splice r.σ q.σ o p
  let θ := r.θ.sumCongr q.θ
  let t : D ⊕ E → ℤ := Sum.elim r.t q.t
  let h := (q.u p)⁻¹*r.u o
  let u : D ⊕ E → A := Sum.elim r.u (fun d ↦ q.u d*h)
  let ε : V ⊕ W → ℤ := Sum.elim r.atlas.ε q.atlas.ε
  let f : (V ⊕ W) × I → D ⊕ E := fun vi ↦ match vi.1 with
    | Sum.inl v => Sum.inl (r.atlas.disk (v,vi.2))
    | Sum.inr v => Sum.inr (q.atlas.disk (v,vi.2))
  have hf : Function.Injective f := by
    rintro ⟨v,i⟩ ⟨w,j⟩ he
    cases v <;> cases w
    · have hh := r.atlas.disk.injective (Sum.inl.inj he)
      cases hh; rfl
    · exact False.elim (Sum.inl_ne_inr he)
    · exact False.elim (Sum.inr_ne_inl he)
    · have hh := q.atlas.disk.injective (Sum.inr.inj he)
      cases hh; rfl
  have hrd (vi : V × I) : r.atlas.disk vi ≠ o := fun he ↦ r.disjoint vi (by simp [he])
  have hqd (vi : W × I) : q.atlas.disk vi ≠ p := fun he ↦ q.disjoint vi (by simp [he])
  have hrs (v : V) (i : I) : r.σ (r.atlas.disk (v,i)) ≠ o := by
    rw [r.atlas.next]; exact hrd _
  have hqs (v : W) (i : I) : q.σ (q.atlas.disk (v,i)) ≠ p := by
    rw [q.atlas.next]; exact hqd _
  let b : DiskAtlas (V := V ⊕ W) ρ a s σ t := {
    disk := ⟨f,hf⟩
    ε := ε
    polarity := by rintro (v|v); exact r.atlas.polarity v; exact q.atlas.polarity v
    next := by
      rintro (v|v) i
      · change splice r.σ q.σ o p (Sum.inl (r.atlas.disk (v,i))) = _
        rw [splice_inl,ite_eq_right (hrs v i),r.atlas.next]
        rfl
      · change splice r.σ q.σ o p (Sum.inr (q.atlas.disk (v,i))) = _
        rw [splice_inr _ _ _ _ _ (hqd _),ite_eq_right (hqs v i),q.atlas.next]
        rfl
    sign := by rintro (v|v) i; exact r.atlas.sign v i; exact q.atlas.sign v i }
  refine {
    σ := σ, θ := θ, t := t, u := u, atlas := b
    involutive := ?_, planar' := planar_splice _ _ _ _ _ _ r.planar' q.planar'
    opposite := ?_, marker := ?_, marker_sign := r.marker_sign
    circle := circle_splice _ _ _ _ _ _ r.circle q.circle (List.nodup_cons.mp r.nodup).1 (List.nodup_cons.mp q.nodup).1
    nodup := ?_, unit := ?_, disjoint := ?_, cover := ?_, corners := ?_ }
  · rintro (d|d)
    · exact congrArg Sum.inl (r.involutive d)
    · exact congrArg Sum.inr (q.involutive d)
  · rintro (d|d); exact r.opposite d; exact q.opposite d
  · exact congrArg Sum.inl r.marker
  · change ((o::l).map Sum.inl ++ m.map Sum.inr).Nodup
    apply List.nodup_append.mpr
    refine ⟨r.nodup.map Sum.inl_injective,q.nodup.of_cons.map Sum.inr_injective,?_⟩
    intro d hd e he hh
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hd
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp he
    exact Sum.inl_ne_inr hh
  · intro d hd
    obtain hd | hd := List.mem_append.mp hd
    · obtain ⟨d,hx,rfl⟩ := List.mem_map.mp hd
      exact r.unit d hx
    · obtain ⟨d,hx,rfl⟩ := List.mem_map.mp hd
      exact q.unit d hx
  · rintro ⟨v|v,i⟩ he
    · have hh : r.atlas.disk (v,i) ∈ o::l := by simpa [b,f,List.mem_map] using he
      exact r.disjoint (v,i) hh
    · have hh : q.atlas.disk (v,i) ∈ m := by simpa [b,f,List.mem_map] using he
      exact q.disjoint (v,i) (by simp [hh])
  · rintro (d|d)
    · obtain ⟨⟨v,i⟩,hi⟩ | hi | ⟨hs,hθ⟩ := r.cover d
      · exact Or.inl ⟨(Sum.inl v,i),congrArg Sum.inl hi⟩
      · exact Or.inr (Or.inl (by simpa [List.mem_map] using hi))
      · by_cases hd : d=o
        · subst d; exact Or.inr (Or.inl (by simp))
        · apply Or.inr ∘ Or.inr
          constructor
          · change splice r.σ q.σ o p (Sum.inl d) = Sum.inl d
            rw [splice_inl,hs,ite_eq_right hd]
          · exact congrArg Sum.inl hθ
    · obtain ⟨⟨v,i⟩,hi⟩ | hi | ⟨hs,hθ⟩ := q.cover d
      · exact Or.inl ⟨(Sum.inr v,i),congrArg Sum.inr hi⟩
      · rcases List.mem_cons.mp hi with hd | hd
        · subst d
          exact Or.inr (Or.inr ⟨splice_marker _ _ _ _,congrArg Sum.inr q.marker⟩)
        · exact Or.inr (Or.inl (by simp [List.mem_map,hd]))
      · apply Or.inr ∘ Or.inr
        constructor
        · change splice r.σ q.σ o p (Sum.inr d) = Sum.inr d
          by_cases hd : d=p
          · subst d; exact splice_marker _ _ _ _
          · rw [splice_inr _ _ _ _ _ hd,hs,ite_eq_right hd]
        · exact congrArg Sum.inr hθ
  · rintro (v|v) i
    · change vertexCorner ρ a r.atlas.ε (v,i) = corner σ θ u (Sum.inl (r.atlas.disk (v,i)))
      rw [r.corners]
      unfold corner
      simp only [σ,θ,splice_inl,hrs,ite_false,Equiv.Perm.sumCongr_apply,Sum.map_inl,u,Sum.elim_inl]
    · change vertexCorner ρ a q.atlas.ε (v,i) = corner σ θ u (Sum.inr (q.atlas.disk (v,i)))
      rw [q.corners]
      unfold corner
      simp only [σ,θ,splice_inr _ _ _ _ _ (hqd _),hqs,ite_false,Equiv.Perm.sumCongr_apply,Sum.map_inr,u,Sum.elim_inr]
      group

omit [Fintype V] [Fintype W] [Fintype I] in
lemma OuterRibbon.value_mul {ρ : Perm I} {a : I → A} {s : I → ℤ}
    {o : D} {p : E} {l : List D} {m : List E}
    (r : OuterRibbon (V := V) ρ a s o l) (q : OuterRibbon (V := W) ρ a s p m) :
    (r.mul q).value = r.value*q.value := by
  rw [OuterRibbon.value_formula,OuterRibbon.value_formula,OuterRibbon.value_formula,transportEval_append]
  change Coprod.inl (r.u o) *
    (transportEval (r.θ.sumCongr q.θ) (Sum.elim r.t q.t)
      (Sum.elim r.u (fun d ↦ q.u d*((q.u p)⁻¹*r.u o))) (l.map Sum.inl) *
     transportEval (r.θ.sumCongr q.θ) (Sum.elim r.t q.t)
      (Sum.elim r.u (fun d ↦ q.u d*((q.u p)⁻¹*r.u o))) (m.map Sum.inr)) * (Coprod.inl (r.u o))⁻¹ = _
  rw [transportEval_map_gauge r.θ _ r.t _ r.u _ Sum.inl 1 (fun _ ↦ rfl) (fun _ ↦ rfl) (fun d ↦ (mul_one _).symm),
    transportEval_map_gauge q.θ _ q.t _ q.u _ Sum.inr ((q.u p)⁻¹*r.u o) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)]
  simp only [map_one,inv_one,one_mul,mul_one,map_mul,map_inv]
  group
end KervaireRibbon

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.Conjugation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

def OuterRibbon.conjLetter {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) (n : ℤ) (hn : n=1 ∨ n = -1) :
    OuterRibbon (V := V) ρ a s (Sum.inl o) (Sum.inr false :: l.map Sum.inl ++ [Sum.inr true]) := by
  let σ := whisker r.σ o
  let θ := r.θ.sumCongr (swap false true)
  let t : D ⊕ Bool → ℤ := Sum.elim r.t (fun b ↦ if b then -n else n)
  let u : D ⊕ Bool → A := Sum.elim r.u (fun _ ↦ r.u o)
  have hd (vi : V × I) : r.atlas.disk vi ≠ o := fun he ↦ r.disjoint vi (by simp [he])
  have hs (v : V) (i : I) : r.σ (r.atlas.disk (v,i)) ≠ o := by rw [r.atlas.next]; exact hd _
  let b : DiskAtlas (V := V) ρ a s σ t := {
    disk := r.atlas.disk.trans ⟨Sum.inl,Sum.inl_injective⟩
    ε := r.atlas.ε
    polarity := r.atlas.polarity
    next := by intro v i; change whisker r.σ o (Sum.inl (r.atlas.disk (v,i))) = _
               rw [whisker_inl _ _ _ (hd _),ite_eq_right (hs _ _)]; exact congrArg Sum.inl (r.atlas.next v i)
    sign := r.atlas.sign }
  refine {
    σ := σ, θ := θ, t := t, u := u, atlas := b
    involutive := ?_, planar' := planar_whisker _ _ _ r.marker r.planar'
    opposite := ?_, marker := congrArg Sum.inl r.marker, marker_sign := r.marker_sign
    circle := circle_whisker _ _ _ r.circle (List.nodup_cons.mp r.nodup).1
    nodup := ?_, unit := ?_, disjoint := ?_, cover := ?_, corners := ?_ }
  · rintro (d|d)
    · exact congrArg Sum.inl (r.involutive d)
    · simp only [θ,Equiv.Perm.sumCongr_apply,Sum.map_inr,swap_apply_self]
  · rintro (d|d)
    · exact r.opposite d
    · cases d <;> simp [θ,t]
  · have hl : (l.map (Sum.inl : D → D ⊕ Bool) ++ [Sum.inr true]).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨r.nodup.of_cons.map Sum.inl_injective,by simp,?_⟩
      intro d hd e he hde
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hd
      have he' : e = Sum.inr true := List.mem_singleton.mp he
      exact Sum.inl_ne_inr (hde.trans he')
    apply List.nodup_cons.mpr
    constructor
    · simpa only [List.mem_cons,List.mem_append,List.mem_map,List.mem_singleton,
        Sum.inl_ne_inr,List.not_mem_nil,or_false,false_or,Sum.inl.injEq,exists_eq_right] using
        (List.nodup_cons.mp r.nodup).1
    · apply List.nodup_cons.mpr
      exact ⟨by simp [List.mem_map],hl⟩
  · intro d hd'
    simp only [List.cons_append,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hd'
    rcases hd' with rfl | hd' | rfl
    · exact hn
    · obtain ⟨d,hmem,rfl⟩ := List.mem_map.mp hd'
      exact r.unit d hmem
    · rcases hn with h|h <;> simp [t,h]
  · intro vi he
    have hh : r.atlas.disk vi ∈ o::l := by simpa [b,List.mem_map] using he
    exact r.disjoint vi hh
  · rintro (d|d)
    · obtain ⟨vi,hi⟩ | hi | ⟨hs',hθ⟩ := r.cover d
      · exact Or.inl ⟨vi,congrArg Sum.inl hi⟩
      · exact Or.inr (Or.inl (by simpa [List.mem_map] using hi))
      · by_cases he : d=o
        · subst d; exact Or.inr (Or.inl (by simp))
        · refine Or.inr (Or.inr ⟨?_,congrArg Sum.inl hθ⟩)
          change whisker r.σ o (Sum.inl d) = Sum.inl d
          rw [whisker_inl _ _ _ he,hs',ite_eq_right he]
    · cases d <;> exact Or.inr (Or.inl (by simp))
  · intro v i
    rw [r.corners]
    change corner r.σ r.θ r.u (r.atlas.disk (v,i)) = corner σ θ u (Sum.inl (r.atlas.disk (v,i)))
    simp only [corner,σ,whisker_inl _ _ _ (hd _),hs,ite_false,θ,Equiv.Perm.sumCongr_apply,Sum.map_inl,u,Sum.elim_inl]

end

open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

omit [Fintype V] [Fintype I] [DecidableEq D] in
lemma OuterRibbon.theta_ne_marker {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) {d : D} (hd : d ≠ o) : r.θ d ≠ o :=
  fun he ↦ hd (r.θ.injective (he.trans r.marker.symm))

def OuterRibbon.conjCoefficient {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) (g : A) : OuterRibbon (V := V) ρ a s o l := by
  refine { r with u := Function.update r.u o (g*r.u o), corners := ?_ }
  intro v i
  have hn (vi : V × I) : r.atlas.disk vi ≠ o := fun he ↦ r.disjoint vi (by simp [he])
  have hs : r.σ (r.atlas.disk (v,i)) ≠ o := by rw [r.atlas.next]; exact hn _
  rw [r.corners]
  simp only [corner,Function.update_of_ne (r.theta_ne_marker (hn _)),Function.update_of_ne hs]

end KervaireRibbon

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.Inversion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace KervaireRibbon
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

omit [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A] in
lemma perm_apply_inverse (σ : Perm D) (d : D) : σ (σ⁻¹ d) = d := by
  rw [Equiv.Perm.inv_def]; exact σ.apply_symm_apply d
omit [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A] in
lemma perm_inverse_apply (σ : Perm D) (d : D) : σ⁻¹ (σ d) = d := by
  rw [Equiv.Perm.inv_def]; exact σ.symm_apply_apply d

omit [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A] in
lemma cycles_inv (σ : Perm D) : SameCycle.setoid σ⁻¹ = SameCycle.setoid σ := by
  ext x y; exact sameCycle_inv

omit [Fintype V] [Fintype I] [DecidableEq D] [Group A] in
lemma numCycles_inverse (σ : Perm D) : numCycles σ⁻¹ = numCycles σ := by
  exact Fintype.card_congr (Quotient.congrRight (fun _ _ ↦ sameCycle_inv))

omit [Fintype V] [Fintype I] [DecidableEq D] [Group A] in
lemma planar_inverse (σ θ : Perm D) (hθ : ∀ d, θ (θ d) = d) (hp : planar σ θ) :
    planar σ⁻¹ θ := by
  have heθ : θ⁻¹ = θ := by
    apply Equiv.ext; intro d
    apply θ.injective
    simp only [perm_apply_inverse,hθ]
  have hf : numCycles (σ⁻¹*θ) = numCycles (σ*θ) := by
    calc
      _ = numCycles (θ*σ)⁻¹ := by rw [mul_inv_rev,heθ]
      _ = numCycles (θ*σ) := numCycles_inverse _
      _ = _ := numCycles_mul_comm _ _
  unfold planar at hp ⊢
  simpa only [numCycles_inverse,hf,components,cycles_inv] using hp

omit [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A] in
lemma circle_inverse (σ : Perm D) (o : D) (l : List D) (h : Circle σ o l) :
    Circle σ⁻¹ o l.reverse := by
  have hh : (o::(l++[o])).IsChain (fun a b ↦ σ⁻¹ b = a) := by
    apply h.imp
    intro x y he
    apply σ.injective
    simpa only [perm_apply_inverse] using he.symm
  have hr := List.isChain_reverse.mpr hh
  simpa only [Circle,List.reverse_cons,List.reverse_append,List.reverse_singleton,List.singleton_append,
    List.append_assoc,List.cons_append,List.nil_append,List.reverse_nil] using hr

/-- Reflection reverses every vertex, negates the traversal signs, and exchanges
both sides of each band potential. -/
def OuterRibbon.inv {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) : OuterRibbon (V := V) ρ a s o l.reverse := by
  let ε : V → ℤ := fun v ↦ -r.atlas.ε v
  have hn (v : V) (i : I) : r.σ⁻¹ (r.atlas.disk (v,i)) = r.atlas.disk (vertexNext ρ ε (v,i)) := by
    apply r.σ.injective
    rw [perm_apply_inverse]
    rcases r.atlas.polarity v with hv | hv
    · simp only [vertexNext,ε,hv,show -(1:ℤ) ≠ 1 by omega,ite_false]
      rw [r.atlas.next]
      simp only [vertexNext,hv,ite_true,ρ.apply_symm_apply]
    · simp only [vertexNext,ε,hv,neg_neg,ite_true]
      rw [r.atlas.next]
      simp only [vertexNext,hv,show (-1:ℤ) ≠ 1 by omega,ite_false,ρ.symm_apply_apply]
  let b : DiskAtlas (V := V) ρ a s r.σ⁻¹ (fun d ↦ -r.t d) := {
    disk := r.atlas.disk, ε := ε
    polarity := by intro v; rcases r.atlas.polarity v with hv|hv <;> simp [ε,hv]
    next := hn
    sign := by intro v i; rw [r.atlas.sign]; exact (neg_mul _ _).symm }
  refine {
    σ := r.σ⁻¹, θ := r.θ, t := fun d ↦ -r.t d, u := r.u ∘ r.θ, atlas := b
    involutive := r.involutive, planar' := planar_inverse _ _ r.involutive r.planar'
    opposite := by intro d; rw [r.opposite]
    marker := r.marker, marker_sign := by rw [r.marker_sign,neg_zero]
    circle := circle_inverse _ _ _ r.circle
    nodup := by simpa only [List.nodup_cons,List.mem_reverse,List.nodup_reverse] using r.nodup
    unit := by intro d hd; rcases r.unit d (List.mem_reverse.mp hd) with h|h <;> simp [h]
    disjoint := by intro vi; simpa only [List.mem_cons,List.mem_reverse] using r.disjoint vi
    cover := ?_, corners := ?_ }
  · intro d
    obtain hd | hd | ⟨hs,ht⟩ := r.cover d
    · exact Or.inl hd
    · exact Or.inr (Or.inl (by simpa only [List.mem_cons,List.mem_reverse] using hd))
    · exact Or.inr (Or.inr ⟨by rw [show r.σ⁻¹ d = r.σ⁻¹ (r.σ d) from congrArg (fun x ↦ r.σ⁻¹ x) hs.symm,perm_inverse_apply],ht⟩)
  · intro v i
    have hc : corner r.σ⁻¹ r.θ (r.u ∘ r.θ) (r.atlas.disk (v,i)) =
        (corner r.σ r.θ r.u (r.σ⁻¹ (r.atlas.disk (v,i))))⁻¹ := by
      simp only [corner,Function.comp_apply,r.involutive,perm_apply_inverse,mul_inv_rev,inv_inv]
    rw [hc,hn]
    rcases r.atlas.polarity v with hv|hv
    · change vertexCorner ρ a ε (v,i) = _
      simp only [vertexNext,ε,hv,show -(1:ℤ) ≠ 1 by omega,ite_false]
      rw [← r.corners]
      simp only [vertexCorner,hv,show -(1:ℤ) ≠ 1 by omega,ite_false,ite_true]
    · change vertexCorner ρ a ε (v,i) = _
      simp only [vertexNext,ε,hv,neg_neg,ite_true]
      rw [← r.corners]
      simp only [vertexCorner,hv,neg_neg,ite_true,show (-1:ℤ) ≠ 1 by omega,ite_false,ρ.symm_apply_apply,inv_inv]

omit [Fintype V] [Fintype I] [DecidableEq D] in
lemma OuterRibbon.value_inv {ρ : Perm I} {a : I → A} {s : I → ℤ} {o : D} {l : List D}
    (r : OuterRibbon (V := V) ρ a s o l) : r.inv.value = r.value⁻¹ := by
  have he (d) : transportLetter r.θ (fun d ↦ -r.t d) (r.u ∘ r.θ) d =
      (transportLetter r.θ r.t r.u d)⁻¹ := by
    simp only [transportLetter,Function.comp_apply,r.involutive,ofAdd_neg,map_inv,mul_inv_rev,inv_inv]
    group
  have hh : transportEval r.θ (fun d ↦ -r.t d) (r.u ∘ r.θ) l.reverse =
      (transportEval r.θ r.t r.u l)⁻¹ := by
    rw [transportEval,transportEval,List.prod_inv_reverse,List.map_map,List.map_reverse]
    congr 2
    exact List.map_congr_left (fun d _ ↦ he d)
  rw [OuterRibbon.value_formula,OuterRibbon.value_formula]
  change Coprod.inl (r.u (r.θ o)) * transportEval r.θ (fun d ↦ -r.t d) (r.u ∘ r.θ) l.reverse * (Coprod.inl (r.u (r.θ o)))⁻¹ = _
  rw [r.marker,hh]
  group
end KervaireRibbon

end
end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.Realization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace KervaireRibbon
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {I : Type} {A : Type*} [Group A]

def OuterRibbon.one (ρ : Perm I) (a : I → A) (s : I → ℤ) :
    OuterRibbon (V := (PEmpty : Type)) ρ a s (PUnit.unit : (PUnit : Type)) [] := by
  let b : DiskAtlas (V := (PEmpty : Type)) ρ a s (1 : Perm (PUnit : Type)) (fun _ ↦ 0) := {
    disk := ⟨fun vi ↦ vi.1.elim,by rintro ⟨v,i⟩; exact v.elim⟩
    ε := fun v ↦ v.elim
    polarity := fun v ↦ v.elim
    next := fun v ↦ v.elim
    sign := fun v ↦ v.elim }
  exact {
    σ := 1, θ := 1, t := fun _ ↦ 0, u := fun _ ↦ 1, atlas := b
    involutive := fun _ ↦ rfl, planar' := planar_one_right 1
    opposite := fun _ ↦ (neg_zero : -(0:ℤ)=0).symm
    marker := rfl, marker_sign := rfl
    circle := by simp [Circle]
    nodup := by simp
    unit := by simp
    disjoint := fun vi ↦ vi.1.elim
    cover := fun d ↦ Or.inr (Or.inr ⟨rfl,rfl⟩)
    corners := fun v ↦ v.elim }

lemma OuterRibbon.value_one (ρ : Perm I) (a : I → A) (s : I → ℤ) :
    (OuterRibbon.one ρ a s).value = 1 := by
  simp [OuterRibbon.value,OuterRibbon.one,dartEval,dartLetter,corner]

/-- A word is realized by a finite genus-zero relator ribbon. The dart and vertex
sets range over ordinary finite types; the coefficient group has arbitrary universe. -/
def Realized (ρ : Perm I) (a : I → A) (s : I → ℤ) (w : FreeProd A) : Prop :=
  ∃ (D V : Type) (_ : Fintype D) (_ : DecidableEq D) (_ : Fintype V)
    (o : D) (l : List D) (r : OuterRibbon (V := V) ρ a s o l), r.value = w

lemma Realized.one (ρ : Perm I) (a : I → A) (s : I → ℤ) : Realized ρ a s 1 :=
  ⟨PUnit,PEmpty,inferInstance,inferInstance,inferInstance,PUnit.unit,[],OuterRibbon.one ρ a s,
    OuterRibbon.value_one ρ a s⟩

lemma Realized.mul {ρ : Perm I} {a : I → A} {s : I → ℤ} {w z : FreeProd A}
    (h : Realized ρ a s w) (k : Realized ρ a s z) : Realized ρ a s (w*z) := by
  obtain ⟨D,V,fd,dd,fv,o,l,r,rfl⟩ := h
  obtain ⟨E,W,fe,de,fw,p,m,q,rfl⟩ := k
  exact ⟨D⊕E,V⊕W,inferInstance,inferInstance,inferInstance,Sum.inl o,
    l.map Sum.inl ++ m.map Sum.inr,r.mul q,r.value_mul q⟩

lemma Realized.inv {ρ : Perm I} {a : I → A} {s : I → ℤ} {w : FreeProd A}
    (h : Realized ρ a s w) : Realized ρ a s w⁻¹ := by
  obtain ⟨D,V,fd,dd,fv,o,l,r,rfl⟩ := h
  exact ⟨D,V,fd,dd,fv,o,l.reverse,r.inv,r.value_inv⟩

def realizedSubgroup (ρ : Perm I) (a : I → A) (s : I → ℤ) : Subgroup (FreeProd A) where
  carrier := Realized ρ a s
  one_mem' := Realized.one ρ a s
  mul_mem' := Realized.mul
  inv_mem' := Realized.inv

end KervaireRibbon

end
end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.Annulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

def annulus (ρ : Perm I) : Perm (I ⊕ I) := ρ.symm.sumCongr ρ
def pairing : Perm (I ⊕ I) := Equiv.sumComm I I

omit [DecidableEq I] in
lemma annulus_planar (ρ : Perm I) (hc : ∀ i j, ρ.SameCycle i j) : planar (annulus ρ) pairing := by
  have hn : numCycles ρ = 1 := by
    have hh := numCycles_eq_card ρ (fun _ : I ↦ (PUnit.unit : (PUnit : Type)))
      (fun _ ↦ ⟨Classical.arbitrary I,rfl⟩) (fun x y ↦ ⟨fun _ ↦ rfl,fun _ ↦ hc x y⟩)
    simpa only [Fintype.card_punit] using hh
  have hv : numCycles (annulus ρ) = 2 := by
    rw [annulus,numCycles_sumPerm,← Equiv.Perm.inv_def,numCycles_inverse,hn]
  have ht : ∀ d : I ⊕ I, pairing (pairing d) = d := by rintro (d|d) <;> rfl
  have he : ∀ d : I ⊕ I, pairing d ≠ d := by rintro (d|d) <;> simp [pairing]
  have hf : ∀ d : I ⊕ I, ((annulus ρ * (pairing : Perm (I ⊕ I))) : Perm (I ⊕ I)) (((annulus ρ * (pairing : Perm (I ⊕ I))) : Perm (I ⊕ I)) d) = d := by
    rintro (d|d) <;> simp [annulus,pairing]
  have hg : ∀ d : I ⊕ I, ((annulus ρ * (pairing : Perm (I ⊕ I))) : Perm (I ⊕ I)) d ≠ d := by rintro (d|d) <;> simp [annulus,pairing]
  have hnt := numCycles_involution pairing ht he
  have hnf := numCycles_involution ((annulus ρ * (pairing : Perm (I ⊕ I))) : Perm (I ⊕ I)) hf hg
  have hcc : components (annulus ρ) pairing = ⊤ := by
    apply top_unique
    intro x y _
    have hh (i j : I) : (annulus ρ).SameCycle (Sum.inr i) (Sum.inr j) := by
      rw [annulus,sameCycle_sumPerm]
      exact congrArg Sum.inr (Quotient.sound (s := SameCycle.setoid ρ) (hc i j))
    have hi (i : I) : components (annulus ρ) pairing (Sum.inl i) (Sum.inr i) :=
      (le_sup_right : SameCycle.setoid pairing ≤ components (annulus ρ) pairing) SameCycle.rfl.apply_right
    have hj (i j : I) : components (annulus ρ) pairing (Sum.inr i) (Sum.inr j) :=
      (le_sup_left : SameCycle.setoid (annulus ρ) ≤ components (annulus ρ) pairing) (hh i j)
    cases x with
    | inl i =>
      cases y with
      | inl j => exact (components _ _).trans' (hi i) ((components _ _).trans' (hj i j) ((components _ _).symm' (hi j)))
      | inr j => exact (components _ _).trans' (hi i) (hj i j)
    | inr i =>
      cases y with
      | inl j => exact (components _ _).trans' (hj i j) ((components _ _).symm' (hi j))
      | inr j => exact hj i j
  unfold planar
  rw [hv,hcc,classes_top]
  simp only [Fintype.card_sum] at hnt hnf ⊢
  omega

/-- Adding a zero-sign marked corner just inserts a bivalent boundary point. -/
def markAnnulus (ρ : Perm I) (i : I) : Perm ((I ⊕ I) ⊕ (PUnit : Type)) :=
  swap (Sum.inl (Sum.inr i)) (Sum.inr PUnit.unit) * ((annulus ρ).sumCongr 1)

omit [Fintype I] [Nonempty I] in
lemma markAnnulus_marker (ρ : Perm I) (i : I) : markAnnulus ρ i (Sum.inr PUnit.unit) = Sum.inl (Sum.inr i) := by
  simp [markAnnulus]
omit [Fintype I] [Nonempty I] in
lemma markAnnulus_disk (ρ : Perm I) (i j : I) : markAnnulus ρ i (Sum.inl (Sum.inl j)) = Sum.inl (Sum.inl (ρ.symm j)) := by
  simp [markAnnulus,annulus,swap_apply_def]
omit [Fintype I] [Nonempty I] in
lemma markAnnulus_outside (ρ : Perm I) (i j : I) : markAnnulus ρ i (Sum.inl (Sum.inr j)) =
    if ρ j = i then Sum.inr PUnit.unit else Sum.inl (Sum.inr (ρ j)) := by
  simp only [markAnnulus,mul_apply,Equiv.Perm.sumCongr_apply,Sum.map_inl,annulus,Sum.map_inr]
  by_cases h : ρ j = i
  · simp only [h,ite_true,swap_apply_left]
  · rw [swap_apply_of_ne_of_ne (by simpa using h) (by simp),ite_eq_right h]

lemma markAnnulus_planar (ρ : Perm I) (hc : ∀ i j, ρ.SameCycle i j) (i : I) :
    planar (markAnnulus ρ i) (pairing.sumCongr (1 : Perm (PUnit : Type))) := by
  apply planar_vertex_join
  · rw [components_sumPerm]
    change ¬ Sum.inl _ = Sum.inr _
    simp
  · exact planar_sumPerm _ _ _ _ (annulus_planar ρ hc) (planar_one_right 1)

omit [Fintype I] [Nonempty I] in
lemma markAnnulus_circle (ρ : Perm I) (i : I) (l : List I) (hc : Circle ρ i l) (hn : i ∉ l) :
    Circle (markAnnulus ρ i) (Sum.inr PUnit.unit) ((i::l).map (fun j ↦ Sum.inl (Sum.inr j))) := by
  have hh := chain_redirect ρ (markAnnulus ρ i) (fun j ↦ Sum.inl (Sum.inr j)) i (Sum.inr PUnit.unit)
    i l hc hn (fun j _ ↦ markAnnulus_outside ρ i j)
  apply List.isChain_cons_cons.mpr
  exact ⟨markAnnulus_marker _ _,by simpa only [List.map_cons,List.cons_append,List.append_eq] using hh⟩
end KervaireRibbon

end

section
namespace KervaireRibbon
open Equiv Equiv.Perm Monoid Multiplicative
open scoped Classical
variable {I A : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Group A]

def basePotential (ρ : Perm I) (a : I → A) (i : I) : ((I ⊕ I) ⊕ (PUnit : Type)) → A :=
  Sum.elim (Sum.elim (fun _ ↦ 1) (fun j ↦ (a (ρ.symm j))⁻¹)) (fun _ ↦ (a (ρ.symm i))⁻¹)
def baseSign (s : I → ℤ) : ((I ⊕ I) ⊕ (PUnit : Type)) → ℤ :=
  Sum.elim (Sum.elim (fun j ↦ -s j) s) (fun _ ↦ 0)

omit [Fintype I] [Nonempty I] in
lemma base_corner_disk (ρ : Perm I) (a : I → A) (i j : I) :
    corner (markAnnulus ρ i) (pairing.sumCongr 1) (basePotential ρ a i) (Sum.inl (Sum.inl j)) =
      (a (ρ.symm j))⁻¹ := by
  simp [corner,markAnnulus_disk,pairing,basePotential]

/-- The annulus between a single oppositely oriented relator disk and its outside
word has a literal genus-zero ribbon witness. -/
def OuterRibbon.base (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (i : I) (l : List I)
    (hc : Circle ρ i l) (hn : (i::l).Nodup) (hcover : ∀ j, j ∈ i::l) :
    OuterRibbon (D := (I⊕I)⊕(PUnit : Type)) (V := (PUnit : Type)) ρ a s (Sum.inr PUnit.unit) ((i::l).map (fun j ↦ Sum.inl (Sum.inr j))) := by
  let σ := markAnnulus ρ i
  let θ : Perm ((I ⊕ I) ⊕ (PUnit : Type)) := pairing.sumCongr 1
  let b : DiskAtlas (V := (PUnit : Type)) ρ a s σ (baseSign s) := {
    disk := ⟨fun vi ↦ Sum.inl (Sum.inl vi.2),by
      rintro ⟨v,i⟩ ⟨w,j⟩ he
      have hi := Sum.inl.inj (Sum.inl.inj he)
      cases v; cases w; cases hi; rfl⟩
    ε := fun _ ↦ -1
    polarity := fun _ ↦ Or.inr rfl
    next := by
      intro v j
      change markAnnulus ρ i (Sum.inl (Sum.inl j)) =
        Sum.inl (Sum.inl (if (-1:ℤ)=1 then ρ j else ρ.symm j))
      simpa only [show (-1:ℤ) ≠ 1 by omega,ite_false] using markAnnulus_disk ρ i j
    sign := by intro v j; change -s j = (-1)*s j; exact (neg_one_mul _).symm }
  refine {
    σ := σ, θ := θ, t := baseSign s, u := basePotential ρ a i, atlas := b
    involutive := ?_, planar' := markAnnulus_planar ρ hρ i
    opposite := ?_, marker := rfl, marker_sign := rfl
    circle := markAnnulus_circle ρ i l hc (List.nodup_cons.mp hn).1
    nodup := ?_, unit := ?_, disjoint := ?_, cover := ?_, corners := ?_ }
  · rintro ((j|j)|j) <;> rfl
  · rintro ((j|j)|j) <;> simp [θ,pairing,baseSign]
  · apply List.nodup_cons.mpr
    refine ⟨by simp [List.mem_map],hn.map ?_⟩
    intro x y h
    exact Sum.inr.inj (Sum.inl.inj h)
  · intro d hd
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hd
    exact hs j
  · rintro ⟨v,j⟩
    change Sum.inl (Sum.inl j) ∉ Sum.inr PUnit.unit :: (i::l).map (fun j ↦ Sum.inl (Sum.inr j))
    simp [List.mem_map]
  · rintro ((j|j)|j)
    · exact Or.inl ⟨(PUnit.unit,j),rfl⟩
    · exact Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,hcover j,rfl⟩)))
    · cases j; exact Or.inr (Or.inl (by simp))
  · intro v j
    change vertexCorner ρ a (fun _ : PUnit ↦ -1) (v,j) =
      corner (markAnnulus ρ i) (pairing.sumCongr 1) (basePotential ρ a i) (Sum.inl (Sum.inl j))
    simpa [vertexCorner] using (base_corner_disk ρ a i j).symm

end KervaireRibbon

end

end OAI
end

section
-- module Solutions.OAIQW_KervaireMain.WordNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KervaireRibbon

section
open Monoid Multiplicative
variable {A : Type*} [Group A]

def syllableEval (l : List (ℤ × A)) : FreeProd A :=
  (l.map (fun x ↦ Coprod.inr (ofAdd x.1)*Coprod.inl x.2)).prod

def UnitSyllables (l : List (ℤ × A)) : Prop := ∀ x ∈ l, x.1=1 ∨ x.1 = -1

def Normalized (w : FreeProd A) : Prop :=
  ∃ g : A, ∃ l : List (ℤ × A), UnitSyllables l ∧ w = Coprod.inl g*syllableEval l

end

open Equiv Equiv.Perm
open scoped Classical
end KervaireRibbon

end OAI
end


