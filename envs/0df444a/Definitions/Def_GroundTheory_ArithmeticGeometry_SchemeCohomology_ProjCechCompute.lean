-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechCompute
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechCompute
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:34:54.682739+00:00
-- url     : https://prove2.me/theorems/3f2e288c-228c-57b1-bbd0-49a650d95058
-- title:
--   Proj Cech Compute
-- statement:
--   Definitions and structural lemmas for Proj Cech Compute, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjCechCompute.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechModel
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_altProj_apply_of_strictMono
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_altProj_congr
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_altProj_eq_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_cls_altProj
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_LDeg_mono
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_awayDegEquiv_apply
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_cochain_ext
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_coeff_toLaurent_eq_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_coeff_toLaurent_expHom
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_expHom_injective
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_d
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_ofL
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_single_mem_LDeg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_sum_expHom
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_theta_lval
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_toLaurent_injective
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_ext
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_mkSection
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_neg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cons_comp_succAbove_succ
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cons_comp_succAbove_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.awayDegEquiv_apply
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.lval_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.lval_ofL
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.lval_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.lval_zero
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_mkSection
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_zero


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial
universe u
noncomputable section
open scoped Classical
namespace ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}
def filterL (S : (Fin (n + 1) → ℤ) → Prop) : Laurent A n →+ Laurent A n where
  toFun ℓ := AddMonoidAlgebra.ofCoeff (ℓ.coeff.filter S)
  map_zero' := by
    apply AddMonoidAlgebra.coeff_injective
    ext m
    simp [Finsupp.filter_apply]
  map_add' ℓ ℓ' := by
    apply AddMonoidAlgebra.coeff_injective
    ext m
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.filter_add]
lemma coeff_filterL (S : (Fin (n + 1) → ℤ) → Prop) (ℓ : Laurent A n) (m : Fin (n + 1) → ℤ) :
    (filterL S ℓ).coeff m = if S m then ℓ.coeff m else 0 :=
  Finsupp.filter_apply _ _ _
lemma coeff_zsmul' (z : ℤ) (ℓ : Laurent A n) (m : Fin (n + 1) → ℤ) :
    (z • ℓ).coeff m = z • ℓ.coeff m := by
  have := map_zsmul (AddMonoidAlgebra.coeffAddEquiv (R := A) (M := Fin (n + 1) → ℤ)) z ℓ
  exact congrArg (fun f : (Fin (n + 1) → ℤ) →₀ A => f m) this
lemma coeff_sum' {α : Type*} (s : Finset α) (f : α → Laurent A n) (m : Fin (n + 1) → ℤ) :
    (∑ a ∈ s, f a).coeff m = ∑ a ∈ s, (f a).coeff m := by
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
def IsSel (j : Fin (n + 1)) (m : Fin (n + 1) → ℤ) : Prop := 0 ≤ m j ∧ ∀ j' < j, m j' < 0
lemma exists_isSel {m : Fin (n + 1) → ℤ} (h : ¬ ∀ j, m j < 0) : ∃ j, IsSel j m := by
  push Not at h
  let S := Finset.univ.filter fun j => 0 ≤ m j
  have hS : S.Nonempty := by
    obtain ⟨j, hj⟩ := h
    exact ⟨j, by simp [S, hj]⟩
  refine ⟨S.min' hS, (Finset.mem_filter.mp (S.min'_mem hS)).2, fun j' hj' => ?_⟩
  by_contra hc
  push Not at hc
  exact absurd (S.min'_le j' (by simp [S, hc])) (not_le.mpr hj')
lemma isSel_unique {m : Fin (n + 1) → ℤ} {j j' : Fin (n + 1)} (h : IsSel j m) (h' : IsSel j' m) :
    j = j' := by
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd h.1 (not_le.mpr (h'.2 j hlt))
  · exact heq
  · exact absurd h'.1 (not_le.mpr (h.2 j' hgt))
lemma not_allNeg_of_isSel {m : Fin (n + 1) → ℤ} {j : Fin (n + 1)} (h : IsSel j m) :
    ¬ ∀ j, m j < 0 := fun h' => absurd h.1 (not_le.mpr (h' j))
lemma coeff_lval_eq_zero {k : ℤ} {p : ℕ} (σ : Cochain (twistAb A n k) (cover A n) p)
    {i : Fin (p + 1) → Fin (n + 1)} (hi : ¬ Function.Surjective i) {m : Fin (n + 1) → ℤ}
    (hm : ∀ j, m j < 0) : (lval σ i).coeff m = 0 := by
  by_contra h
  have := (lval_mem σ i) m h
  obtain ⟨j, hj⟩ : ∃ j, j ∉ Set.range i := by
    by_contra! hc
    exact hi fun j => hc j
  exact absurd (this.2 j hj) (not_le.mpr (hm j))
theorem exists_d_eq_of_coeff_allNeg {k : ℤ} {p : ℕ}
    (σ : Cochain (twistAb A n k) (cover A n) (p + 1)) (hσ : d _ _ (p + 1) σ = 0)
    (hneg : ∀ i m, (∀ j, m j < 0) → (lval σ i).coeff m = 0) :
    ∃ τ, d _ _ p τ = σ := by
  have hmem : ∀ i : Fin (p + 1) → Fin (n + 1),
      ∑ j, filterL (IsSel j) (lval σ (Fin.cons j i)) ∈ LDeg A (Set.range i) k := by
    intro i
    refine AddSubgroup.sum_mem _ fun j _ => ?_
    intro m hm
    rw [coeff_filterL] at hm
    by_cases hs : IsSel j m
    swap
    · rw [if_neg hs] at hm
      exact absurd rfl hm
    rw [if_pos hs] at hm
    obtain ⟨hsum, hnn⟩ := lval_mem σ (Fin.cons j i) m hm
    refine ⟨hsum, fun j' hj' => ?_⟩
    by_cases hjj : j' = j
    · exact hjj ▸ hs.1
    · refine hnn j' fun ⟨a, ha⟩ => ?_
      cases a using Fin.cases with
      | zero => exact hjj (by simpa using ha.symm)
      | succ a => exact hj' ⟨a, by simpa using ha⟩
  refine ⟨ofL fun i => ⟨_, hmem i⟩, cochain_ext fun i => ?_⟩
  rw [lval_d]
  simp only [lval_ofL]
  apply AddMonoidAlgebra.coeff_injective
  ext m
  simp only [coeff_sum', coeff_zsmul', coeff_filterL]
  by_cases hm : ∀ j, m j < 0
  · rw [hneg i m hm]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Finset.sum_eq_zero fun j _ => ?_, smul_zero]
    rw [if_neg fun hs => not_allNeg_of_isSel hs hm]
  · obtain ⟨j₀, hj₀⟩ := exists_isSel hm
    have hsel : ∀ (f : Fin (n + 1) → A),
        (∑ j, if IsSel j m then f j else 0) = f j₀ := fun f => by
      rw [Finset.sum_eq_single j₀ (fun j _ hj => if_neg fun hs => hj (isSel_unique hs hj₀))
        (fun h => absurd (Finset.mem_univ _) h), if_pos hj₀]
    simp_rw [hsel]
    have hc := congrArg (fun ℓ => (ℓ : Laurent A n).coeff m) (lval_d σ (Fin.cons j₀ i))
    simp only [hσ, lval_zero, coeff_sum', coeff_zsmul'] at hc
    change (0 : Laurent A n).coeff m = _ at hc
    rw [Fin.sum_univ_succ, cons_comp_succAbove_zero] at hc
    simp only [cons_comp_succAbove_succ, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
      pow_succ, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib] at hc
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hc
    linear_combination hc
variable (n) in

abbrev NegMon (k : ℤ) : Type := {m : Fin (n + 1) → ℤ // (∀ j, m j < 0) ∧ ∑ j, m j = k}
def topCoeff {k : ℤ} : Cochain (twistAb A n k) (cover A n) n →+ (NegMon n k →₀ A) where
  toFun σ := (lval σ id).coeff.subtypeDomain fun e => (∀ j, e j < 0) ∧ ∑ j, e j = k
  map_zero' := by simp
  map_add' σ τ := by simp [Finsupp.subtypeDomain_add]
lemma topCoeff_apply {k : ℤ} (σ : Cochain (twistAb A n k) (cover A n) n) (e : NegMon n k) :
    topCoeff σ e = (lval σ id).coeff e.1 := rfl
lemma filterL_mem_LDeg {s : Set (Fin (n + 1))} {k : ℤ} (S : (Fin (n + 1) → ℤ) → Prop)
    {ℓ : Laurent A n} (h : ℓ ∈ LDeg A s k) : filterL S ℓ ∈ LDeg A s k := by
  intro m hm
  rw [coeff_filterL] at hm
  by_cases hS : S m
  · rw [if_pos hS] at hm
    exact h m hm
  · rw [if_neg hS] at hm
    exact absurd rfl hm
def posPart {k : ℤ} {q : ℕ} (σ : Cochain (twistAb A n k) (cover A n) q) :
    Cochain (twistAb A n k) (cover A n) q :=
  ofL fun i => ⟨filterL (fun e => ¬ ∀ j, e j < 0) (lval σ i), filterL_mem_LDeg _ (lval_mem σ i)⟩
lemma lval_posPart {k : ℤ} {q : ℕ} (σ : Cochain (twistAb A n k) (cover A n) q) (i) :
    lval (posPart σ) i = filterL (fun e => ¬ ∀ j, e j < 0) (lval σ i) := by
  simp [posPart]
lemma d_posPart {k : ℤ} {q : ℕ} (σ : Cochain (twistAb A n k) (cover A n) q) :
    d _ _ q (posPart σ) = posPart (d _ _ q σ) := by
  refine cochain_ext fun i => ?_
  rw [lval_d, lval_posPart, lval_d, map_sum]
  simp only [lval_posPart, map_zsmul]
lemma topCoeff_d {k : ℤ} {q : ℕ} (hq : q + 1 = n) (τ : Cochain (twistAb A n k) (cover A n) q) :
    topCoeff (hq ▸ d _ _ q τ) = 0 := by
  subst hq
  ext e
  rw [topCoeff_apply, lval_d, coeff_sum', Finsupp.coe_zero, Pi.zero_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [coeff_zsmul', coeff_lval_eq_zero τ ?_ e.2.1, smul_zero]
  intro hs
  obtain ⟨b, hb⟩ := hs a
  exact Fin.succAbove_ne a b hb
lemma posPart_zero {k : ℤ} {q : ℕ} : posPart (0 : Cochain (twistAb A n k) (cover A n) q) = 0 :=
  cochain_ext fun i => by rw [lval_posPart, lval_zero, map_zero]
def topMap {k : ℤ} {m : ℕ} :
    cechH (twistAb A (m + 1) k) (cover A (m + 1)) (m + 1) →+ (NegMon (m + 1) k →₀ A) :=
  QuotientAddGroup.lift _ (topCoeff.comp (cocycles _ _ (m + 1)).subtype) (by
    rintro ⟨σ, hσ⟩ hx
    rw [AddSubgroup.mem_addSubgroupOf, coboundaries_succ] at hx
    obtain ⟨τ, hτ⟩ := hx
    change topCoeff σ = 0
    rw [← show d _ _ m τ = σ from hτ]
    exact topCoeff_d rfl τ)
lemma topMap_cls {k : ℤ} {m : ℕ} (σ : Cochain (twistAb A (m + 1) k) (cover A (m + 1)) (m + 1))
    (hσ : d _ _ (m + 1) σ = 0) : topMap (cls σ hσ) = topCoeff σ := rfl
theorem topMap_bijective {k : ℤ} {m : ℕ} :
    Function.Bijective (topMap (A := A) (k := k) (m := m)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨σ, hσ, rfl⟩ := exists_cls c
    rw [topMap_cls] at hc
    have hneg0 : ∀ e, (∀ j, e j < 0) → (lval σ id).coeff e = 0 := fun e he => by
      by_cases hs : ∑ j, e j = k
      · exact DFunLike.congr_fun hc ⟨e, he, hs⟩
      · by_contra h
        exact hs (lval_mem σ id e h).1
    have hsame : ∀ t, StrictMono t → σ t = posPart σ t := fun t ht => by
      obtain rfl := ht.eq_id
      rw [← theta_lval σ id, ← theta_lval (posPart σ) id]
      congr 1
      apply Subtype.ext
      change lval σ id = lval (posPart σ) id
      rw [lval_posPart]
      apply AddMonoidAlgebra.coeff_injective
      ext e
      rw [coeff_filterL]
      split_ifs with he
      · exact hneg0 e he
      · rfl
    have hcong := CechOrdered.altProj_congr (m + 1) hsame
    have hσp : d _ _ (m + 1) (posPart σ) = 0 := by rw [d_posPart, hσ, posPart_zero]
    obtain ⟨τ, hτ⟩ := exists_d_eq_of_coeff_allNeg (posPart σ) hσp fun i e he => by
      rw [lval_posPart, coeff_filterL, if_neg (not_not_intro he)]
    rw [← CechOrdered.cls_altProj m σ hσ, cls_eq_zero_iff, coboundaries_succ, hcong, ← hτ,
      ← CechOrdered.d_altProj]
    exact ⟨_, rfl⟩
  · intro ν
    let ℓ : Laurent A (m + 1) := ∑ e ∈ ν.support, AddMonoidAlgebra.single e.1 (ν e)
    have hℓ : ∀ i : Fin (m + 2) → Fin (m + 2), Set.range i = Set.univ →
        ℓ ∈ LDeg A (Set.range i) k := fun i h =>
      AddSubgroup.sum_mem _ fun e _ => single_mem_LDeg ⟨e.2.2, fun j hj => (hj (h ▸ Set.mem_univ j)).elim⟩ _
    let σ₀ : Cochain (twistAb A (m + 1) k) (cover A (m + 1)) (m + 1) :=
      ofL fun i => if h : Set.range i = Set.univ then ⟨ℓ, hℓ i h⟩ else 0
    have hσ : d _ _ (m + 1) (CechOrdered.altProj _ _ (m + 1) σ₀) = 0 := by
      rw [CechOrdered.d_altProj, CechOrdered.altProj_eq_zero (by simp)]
    refine ⟨cls _ hσ, ?_⟩
    rw [topMap_cls]
    ext e
    rw [topCoeff_apply]
    have h1 : lval (CechOrdered.altProj _ _ (m + 1) σ₀) id = lval σ₀ id := by
      unfold lval
      rw [CechOrdered.altProj_apply_of_strictMono _ _ strictMono_id]
    rw [h1, lval_ofL, dif_pos Set.range_id]
    change (∑ e ∈ ν.support, AddMonoidAlgebra.single e.1 (ν e)).coeff e.1 = ν e
    rw [coeff_sum']
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [Finset.sum_eq_single e]
    · simp
    · intro b _ hb
      rw [if_neg fun h => hb (Subtype.ext h)]
    · intro he
      rw [if_pos rfl]
      exact Finsupp.notMem_support_iff.mp he
def cechHTopEquiv (k : ℤ) (m : ℕ) :
    cechH (twistAb A (m + 1) k) (cover A (m + 1)) (m + 1) ≃+ (NegMon (m + 1) k →₀ A) :=
  AddEquiv.ofBijective topMap topMap_bijective
lemma allowed_empty_of_forall {k : ℤ} (hk : 0 ≤ k) {m : Fin (n + 1) → ℤ}
    (h : ∀ j, Allowed {j} k m) : Allowed ∅ k m := by
  refine ⟨(h 0).1, fun j' _ => ?_⟩
  by_cases hn : ∃ j, j ≠ j'
  · obtain ⟨j, hj⟩ := hn
    exact (h j).2 j' fun h' => hj (Set.mem_singleton_iff.mp h').symm
  · push Not at hn
    have hsum := (h 0).1
    rw [Finset.sum_eq_single j' (fun b _ hb => absurd (hn b) hb) (by simp)] at hsum
    omega
lemma allowed_empty_of_forall' (hn : 0 < n) {k : ℤ} {m : Fin (n + 1) → ℤ}
    (h : ∀ j, Allowed {j} k m) : Allowed ∅ k m := by
  refine ⟨(h 0).1, fun j' _ => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), j ≠ j' := by
    by_cases h0 : j' = 0
    · exact ⟨1, by rw [h0]; exact Fin.ne_of_gt (Fin.pos_iff_ne_zero.mpr (by
        simp [Fin.ext_iff]; omega))⟩
    · exact ⟨0, fun h' => h0 h'.symm⟩
  exact (h j).2 j' fun h' => hj (Set.mem_singleton_iff.mp h').symm
lemma lval_eq_of_cocycle {k : ℤ} (σ : Cochain (twistAb A n k) (cover A n) 0)
    (hσ : d _ _ 0 σ = 0) (j j' : Fin 1 → Fin (n + 1)) : lval σ j = lval σ j' := by
  have h := congrArg (fun τ => lval τ (Fin.cons (j 0) j' : Fin 2 → Fin (n + 1))) hσ
  simp only [lval_d, lval_zero] at h
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  have e0 : (Fin.cons (j 0) j' : Fin 2 → Fin (n + 1)) ∘ (0 : Fin 2).succAbove = j' := by
    funext a; fin_cases a; rfl
  have e1 : (Fin.cons (j 0) j' : Fin 2 → Fin (n + 1)) ∘ (Fin.succ (0 : Fin 1)).succAbove = j := by
    funext a; fin_cases a; rfl
  rw [e0, e1] at h
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, zero_add, pow_one, neg_smul] at h
  exact (sub_eq_zero.mp ((sub_eq_add_neg _ _).trans h)).symm
lemma range_const_fin_one (j : Fin 1 → Fin (n + 1)) : Set.range j = {j 0} := by
  ext x
  simp only [Set.mem_range, Set.mem_singleton_iff]
  exact ⟨fun ⟨a, ha⟩ => by rw [← ha, Fin.fin_one_eq_zero a], fun h => ⟨0, h.symm⟩⟩
def zeroVal {k : ℤ} (hk : 0 ≤ k ∨ 0 < n) :
    cocycles (twistAb A n k) (cover A n) 0 →+ LDeg A (∅ : Set (Fin (n + 1))) k where
  toFun σ := ⟨lval σ.1 (fun _ => 0), fun m hm => by
    have hall : ∀ j : Fin (n + 1), Allowed {j} k m := fun j => by
      have := lval_mem σ.1 (fun _ => j) m (by
        rwa [lval_eq_of_cocycle σ.1 ((mem_cocycles _).1 σ.2) (fun _ => j) (fun _ => 0)])
      rwa [range_const_fin_one] at this
    rcases hk with hk | hn
    · exact allowed_empty_of_forall hk hall
    · exact allowed_empty_of_forall' hn hall⟩
  map_zero' := Subtype.ext (lval_zero _)
  map_add' σ τ := Subtype.ext (lval_add σ.1 τ.1 _)
lemma zeroVal_bijective {k : ℤ} (hk : 0 ≤ k ∨ 0 < n) :
    Function.Bijective (zeroVal (A := A) hk) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro σ hσ
    have h0 : lval σ.1 (fun _ => 0) = 0 := congrArg Subtype.val hσ
    apply Subtype.ext
    refine cochain_ext fun j => ?_
    rw [lval_eq_of_cocycle σ.1 ((mem_cocycles _).1 σ.2) j (fun _ => 0), h0]
    exact (lval_zero j).symm
  · intro ℓ
    let σ : Cochain (twistAb A n k) (cover A n) 0 :=
      ofL fun i => ⟨ℓ.1, LDeg_mono (Set.empty_subset _) k ℓ.2⟩
    have hσ : d _ _ 0 σ = 0 := by
      refine cochain_ext fun i => ?_
      rw [lval_d, lval_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
      simp [σ]
    exact ⟨⟨σ, (mem_cocycles _).2 hσ⟩, Subtype.ext (by simp [zeroVal, σ])⟩
def cechHZeroLEquiv {k : ℤ} (hk : 0 ≤ k ∨ 0 < n) :
    cechH (twistAb A n k) (cover A n) 0 ≃+ LDeg A (∅ : Set (Fin (n + 1))) k :=
  (QuotientAddGroup.quotientBot.symm.trans (QuotientAddGroup.quotientAddEquivOfEq (by
    rw [coboundaries_zero, AddSubgroup.bot_addSubgroupOf]))).symm.trans
    (AddEquiv.ofBijective _ (zeroVal_bijective hk))
lemma toLaurent_mem_LDeg_empty {k : ℕ} {p : MvPolynomial (Fin (n + 1)) A}
    (hp : p ∈ homogeneousSubmodule (Fin (n + 1)) A k) :
    toLaurent A n p ∈ LDeg A (∅ : Set (Fin (n + 1))) k := by
  intro m hm
  by_cases hr : m ∈ Set.range (expHom n)
  · obtain ⟨e, rfl⟩ := hr
    rw [coeff_toLaurent_expHom] at hm
    have h := hp hm
    refine ⟨?_, fun j _ => by simp [expHom]⟩
    rw [sum_expHom, Finsupp.degree_eq_weight_one]
    exact_mod_cast h
  · exact absurd (coeff_toLaurent_eq_zero hr) hm
def homogEquiv (k : ℕ) :
    homogeneousSubmodule (Fin (n + 1)) A k ≃+ LDeg A (∅ : Set (Fin (n + 1))) k :=
  AddEquiv.ofBijective
    ({ toFun p := ⟨toLaurent A n p.1, toLaurent_mem_LDeg_empty p.2⟩
       map_zero' := Subtype.ext (map_zero _)
       map_add' _ _ := Subtype.ext (map_add _ _ _) } :
      homogeneousSubmodule (Fin (n + 1)) A k →+ LDeg A (∅ : Set (Fin (n + 1))) k)
    ⟨fun p q h => Subtype.ext (toLaurent_injective (congrArg Subtype.val h)), fun ℓ => by
      have hsupp : (ℓ.1.coeff.support : Set (Fin (n + 1) → ℤ)) ⊆ Set.range (expHom n) := by
        intro m hm
        have hA := ℓ.2 m (Finsupp.mem_support_iff.mp hm)
        refine ⟨Finsupp.equivFunOnFinite.symm fun j => (m j).toNat, funext fun j => ?_⟩
        change ((m j).toNat : ℤ) = m j
        exact Int.toNat_of_nonneg (hA.2 j (Set.notMem_empty j))
      let p : MvPolynomial (Fin (n + 1)) A :=
        AddMonoidAlgebra.ofCoeff (Finsupp.comapDomain (expHom n) ℓ.1.coeff
          expHom_injective.injOn)
      have hp : toLaurent A n p = ℓ.1 := by
        apply AddMonoidAlgebra.coeff_injective
        exact Finsupp.mapDomain_comapDomain _ expHom_injective _ hsupp
      have hpk : p ∈ homogeneousSubmodule (Fin (n + 1)) A k := by
        intro e he
        have he' : ℓ.1.coeff (expHom n e) ≠ 0 := he
        have hA := ℓ.2 _ he'
        have := hA.1
        rw [sum_expHom, Finsupp.degree_eq_weight_one] at this
        exact_mod_cast this
      exact ⟨⟨p, hpk⟩, Subtype.ext hp⟩⟩
def cechHZeroEquiv' (k : ℕ) :
    cechH (twistAb A n k) (cover A n) 0 ≃+ homogeneousSubmodule (Fin (n + 1)) A k :=
  (cechHZeroLEquiv (Or.inl (Int.natCast_nonneg k))).trans (homogEquiv k).symm
end ProjSpace
end
end GroundTheory.Arith.SchemeCoh


