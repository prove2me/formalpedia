-- Prove2me | solution 1 for AppliedComb.Polya.polya_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:22:43.313331+00:00
-- url     : https://prove2.me/submissions/f6cf60a2-fc3e-4ef2-bd34-6945225ab62e

import Mathlib
import Definitions.Def_AppliedComb_Polya_cycleIndex
import Definitions.Def_AppliedComb_Polya_patternInventory



namespace AppliedComb.Polya

open MvPolynomial Finset Equiv

section Cycles

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Index type of the cycles of `σ`, fixed points included. -/
abbrev CT (σ : Perm S) := {c // c ∈ σ.cycleFactorsFinset} ⊕ {x : S // σ x = x}

/-- The cycle containing a point. -/
def cproj (σ : Perm S) (s : S) : CT σ :=
  if h : σ s = s then Sum.inr ⟨s, h⟩
  else Sum.inl ⟨σ.cycleOf s,
    Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Perm.mem_support.mpr h)⟩

lemma cproj_apply (σ : Perm S) (s : S) : cproj σ (σ s) = cproj σ s := by
  by_cases h : σ s = s
  · rw [h]
  · have h' : σ (σ s) ≠ σ s := fun e => h (σ.injective e)
    unfold cproj
    rw [dif_neg h, dif_neg h']
    congr 1
    exact Subtype.ext (Perm.cycleOf_self_apply σ s)

lemma cproj_sameCycle (σ : Perm S) {a b : S} (h : cproj σ a = cproj σ b) :
    σ.SameCycle a b := by
  unfold cproj at h
  by_cases ha : σ a = a <;> by_cases hb : σ b = b
  · rw [dif_pos ha, dif_pos hb] at h
    have := congrArg Subtype.val (Sum.inr.inj h)
    simp only at this
    subst this
    exact Perm.SameCycle.refl _ _
  · rw [dif_pos ha, dif_neg hb] at h
    cases h
  · rw [dif_neg ha, dif_pos hb] at h
    cases h
  · rw [dif_neg ha, dif_neg hb] at h
    have hc : σ.cycleOf a = σ.cycleOf b := congrArg Subtype.val (Sum.inl.inj h)
    have hb' : b ∈ (σ.cycleOf b).support :=
      Perm.mem_support_cycleOf_iff.mpr ⟨Perm.SameCycle.refl _ _, Perm.mem_support.mpr hb⟩
    rw [← hc] at hb'
    exact (Perm.mem_support_cycleOf_iff.mp hb').1

lemma cproj_surj (σ : Perm S) : Function.Surjective (cproj σ) := by
  rintro (⟨c, hc⟩ | ⟨x, hx⟩)
  · obtain ⟨a, ha⟩ := (Perm.mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
    have hsa : a ∈ σ.support := Perm.mem_cycleFactorsFinset_support_le hc ha
    refine ⟨a, ?_⟩
    unfold cproj
    rw [dif_neg (Perm.mem_support.mp hsa)]
    congr 1
    exact Subtype.ext (Perm.cycle_is_cycleOf ha hc).symm
  · exact ⟨x, by unfold cproj; rw [dif_pos hx]⟩

lemma fiber_inl (σ : Perm S) (c : {c // c ∈ σ.cycleFactorsFinset}) :
    #{s | cproj σ s = Sum.inl c} = #c.1.support := by
  congr 1
  ext s
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h
    unfold cproj at h
    by_cases hs : σ s = s
    · rw [dif_pos hs] at h; cases h
    · rw [dif_neg hs] at h
      have := congrArg Subtype.val (Sum.inl.inj h)
      simp only at this
      rw [← this]
      exact Perm.mem_support_cycleOf_iff.mpr ⟨Perm.SameCycle.refl _ _, Perm.mem_support.mpr hs⟩
  · intro h
    have hsa : s ∈ σ.support := Perm.mem_cycleFactorsFinset_support_le c.2 h
    unfold cproj
    rw [dif_neg (Perm.mem_support.mp hsa)]
    congr 1
    exact Subtype.ext (Perm.cycle_is_cycleOf h c.2).symm

lemma fiber_inr (σ : Perm S) (x : {x : S // σ x = x}) :
    #{s | cproj σ s = Sum.inr x} = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨x.1, ?_⟩
  ext s
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro h
    unfold cproj at h
    by_cases hs : σ s = s
    · rw [dif_pos hs] at h
      exact congrArg Subtype.val (Sum.inr.inj h)
    · rw [dif_neg hs] at h; cases h
  · rintro rfl
    unfold cproj
    rw [dif_pos x.2]

lemma fixed_iff (σ : Perm S) {m : ℕ} (f : S → Fin m) :
    f ∘ ⇑σ⁻¹ = f ↔ ∃ g : CT σ → Fin m, f = g ∘ cproj σ := by
  constructor
  · intro h
    have h1 : ∀ y, f (σ y) = f y := by
      intro y
      have := congrFun h (σ y)
      simpa using this.symm
    have hpow : ∀ (n : ℕ) (y : S), f ((σ ^ n) y) = f y := by
      intro n
      induction n with
      | zero => intro y; simp
      | succ n ih => intro y; rw [pow_succ', Perm.mul_apply, h1, ih]
    have hsc : ∀ a b, σ.SameCycle a b → f a = f b := by
      intro a b hab
      obtain ⟨i, _, hi⟩ := hab.exists_pow_eq'
      rw [← hi, hpow]
    refine ⟨f ∘ Function.surjInv (cproj_surj σ), ?_⟩
    funext s
    simp only [Function.comp_apply]
    apply hsc
    exact cproj_sameCycle σ (Function.surjInv_eq (cproj_surj σ) (cproj σ s)).symm
  · rintro ⟨g, rfl⟩
    funext s
    simp only [Function.comp_apply]
    have := cproj_apply σ (σ⁻¹ s)
    rw [show σ (σ⁻¹ s) = s by simp] at this
    rw [this]

end Cycles

/-- power sum -/
noncomputable def psum (m k : ℕ) : MvPolynomial (Fin m) ℚ := ∑ i : Fin m, X i ^ k

section Sums

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma weight_comp (σ : Perm S) {m : ℕ} (g : CT σ → Fin m) :
    colorWeight (g ∘ cproj σ) = ∏ t, (X (g t) : MvPolynomial (Fin m) ℚ) ^ #{s | cproj σ s = t} := by
  unfold colorWeight
  calc ∏ s, (X ((g ∘ cproj σ) s) : MvPolynomial (Fin m) ℚ)
      = ∏ s, (fun t => (X (g t) : MvPolynomial (Fin m) ℚ)) (cproj σ s) := rfl
    _ = ∏ t, ∏ s with cproj σ s = t, (fun t => (X (g t) : MvPolynomial (Fin m) ℚ)) t :=
        (Finset.prod_fiberwise' univ (cproj σ) (fun t => (X (g t) : MvPolynomial (Fin m) ℚ))).symm
    _ = _ := by simp only [Finset.prod_const]

lemma fixed_sum (σ : Perm S) (m : ℕ) :
    ∑ f ∈ univ.filter (fun f : S → Fin m => f ∘ ⇑σ⁻¹ = f), colorWeight f =
      (σ.cycleType.map (psum m)).prod * psum m 1 ^ Fintype.card {x : S // σ x = x} := by
  have hset : univ.filter (fun f : S → Fin m => f ∘ ⇑σ⁻¹ = f) =
      univ.image (fun g : CT σ → Fin m => g ∘ cproj σ) := by
    ext f
    simp only [mem_filter, mem_univ, true_and, mem_image, fixed_iff]
    constructor
    · rintro ⟨g, rfl⟩; exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩; exact ⟨g, rfl⟩
  rw [hset, Finset.sum_image (fun g _ g' _ h => (cproj_surj σ).injective_comp_right h)]
  simp only [weight_comp]
  rw [show (∑ g : CT σ → Fin m, ∏ t, (X (g t) : MvPolynomial (Fin m) ℚ) ^ #{s | cproj σ s = t})
      = ∏ t, ∑ i : Fin m, (X i : MvPolynomial (Fin m) ℚ) ^ #{s | cproj σ s = t} from
      (Fintype.prod_sum (fun t i => (X i : MvPolynomial (Fin m) ℚ) ^ #{s | cproj σ s = t})).symm]
  rw [Fintype.prod_sum_type]
  congr 1
  · have : ∀ c : {c // c ∈ σ.cycleFactorsFinset},
        (∑ i : Fin m, (X i : MvPolynomial (Fin m) ℚ) ^ #{s | cproj σ s = Sum.inl c})
          = psum m #c.1.support := fun c => by rw [fiber_inl]; rfl
    rw [Fintype.prod_congr _ _ this,
      Finset.prod_coe_sort σ.cycleFactorsFinset (fun c => psum m #c.support),
      Finset.prod_eq_multiset_prod, Perm.cycleType_def, Multiset.map_map]
    rfl
  · simp only [fiber_inr]
    rw [Finset.prod_const, Finset.card_univ]
    rfl

lemma mset_prod {R : Type*} [CommMonoid R] (P : ℕ → R) (r : ℕ) (s : Multiset ℕ)
    (hs : ∀ a ∈ s, 1 ≤ a ∧ a ≤ r) :
    (s.map P).prod = ∏ k ∈ range r, P (k + 1) ^ s.count (k + 1) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons,
      ih (fun b hb => hs b (Multiset.mem_cons_of_mem hb))]
    have ha := hs a (Multiset.mem_cons_self a s)
    simp only [Multiset.count_cons, pow_add, Finset.prod_mul_distrib]
    rw [mul_comm]
    congr 1
    rw [Finset.prod_eq_single (a - 1)]
    · have : a - 1 + 1 = a := by omega
      simp [this]
    · intro b _ hb
      have : b + 1 ≠ a := by omega
      simp [this]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h

lemma monomial_eval (σ : Perm S) (m : ℕ) :
    bind₁ (fun k : Fin (Fintype.card S) => ∑ i : Fin m, (X i : MvPolynomial (Fin m) ℚ) ^ (k.val + 1))
      (cycleMonomial σ) =
      (σ.cycleType.map (psum m)).prod * psum m 1 ^ Fintype.card {x : S // σ x = x} := by
  unfold cycleMonomial
  simp only [map_prod, map_pow, bind₁_X_right]
  rw [Fin.prod_univ_eq_prod_range (fun k => (∑ i : Fin m, (X i : MvPolynomial (Fin m) ℚ) ^ (k + 1))
    ^ cycleCount σ (k + 1))]
  have hcc : ∀ k, cycleCount σ (k + 1) =
      (if k = 0 then Fintype.card {x : S // σ x = x} else 0) + σ.cycleType.count (k + 1) := by
    intro k
    unfold cycleCount
    by_cases hk : k = 0
    · subst hk
      have : σ.cycleType.count 1 = 0 := Multiset.count_eq_zero.mpr
        (fun h => by have := Perm.two_le_of_mem_cycleType h; omega)
      simp [this]
    · have : k + 1 ≠ 1 := by omega
      simp [hk, this]
  simp only [hcc]
  rw [Finset.prod_congr rfl (fun k _ => pow_add _ _ _), Finset.prod_mul_distrib]
  rw [mul_comm]
  congr 1
  · rw [mset_prod (psum m) (Fintype.card S)]
    · rfl
    · intro a ha
      refine ⟨by have := Perm.two_le_of_mem_cycleType ha; omega, ?_⟩
      exact (Perm.le_card_support_of_mem_cycleType ha).trans (Finset.card_le_univ _)
  · rw [Finset.prod_eq_single 0]
    · simp [psum]
    · intro b _ hb
      simp [hb]
    · intro h
      have h0 : Fintype.card S = 0 := by
        by_contra hne
        exact h (Finset.mem_range.mpr (Nat.pos_of_ne_zero hne))
      have : Fintype.card {x : S // σ x = x} = 0 :=
        Nat.eq_zero_of_le_zero (h0 ▸ Fintype.card_subtype_le _)
      simp [this]

end Sums

section Burnside

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma weight_inv (π : Perm S) {m : ℕ} (g : S → Fin m) :
    colorWeight (g ∘ ⇑π⁻¹) = colorWeight g := by
  unfold colorWeight
  exact Equiv.prod_comp π⁻¹ (fun s => (X (g s) : MvPolynomial (Fin m) ℚ))

open Classical in
lemma orbit_stab (G : Subgroup (Perm S)) (m : ℕ) (f : S → Fin m) :
    #((univ.filter (fun σ : Perm S => σ ∈ G)).filter (fun σ : Perm S => f ∘ ⇑σ⁻¹ = f)) *
      #(univ.filter (fun f' : S → Fin m =>
        Quotient.mk (colorSetoid G m) f' = Quotient.mk (colorSetoid G m) f))
      = #(univ.filter (fun σ : Perm S => σ ∈ G)) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : Perm S => f ∘ ⇑σ⁻¹)
    (s := univ.filter (fun σ : Perm S => σ ∈ G))
    (t := univ.filter (fun f' : S → Fin m =>
        Quotient.mk (colorSetoid G m) f' = Quotient.mk (colorSetoid G m) f))]
  · rw [Finset.sum_const_nat (m := #((univ.filter (fun σ : Perm S => σ ∈ G)).filter (fun σ : Perm S => f ∘ ⇑σ⁻¹ = f)))]
    · ring
    · intro f' hf'
      simp only [mem_filter, mem_univ, true_and] at hf'
      obtain ⟨π, hπ, hf⟩ := Quotient.exact hf'
      have hf2 : f' = f ∘ ⇑π := by
        funext s
        rw [hf]
        simp
      subst hf2
      refine Finset.card_nbij' (fun ρ => π * ρ) (fun σ => π⁻¹ * σ) ?_ ?_ ?_ ?_
      · intro ρ hρ
        simp only [mem_filter, mem_univ, true_and, Finset.mem_coe] at hρ ⊢
        refine ⟨G.mul_mem hπ hρ.1, ?_⟩
        funext s
        have := congrFun hρ.2 (π⁻¹ s)
        simp only [Function.comp_apply] at this
        simp only [Function.comp_apply, mul_inv_rev, Perm.coe_mul, this]
        simp
      · intro σ hσ
        simp only [mem_filter, mem_univ, true_and, Finset.mem_coe] at hσ ⊢
        refine ⟨G.mul_mem (G.inv_mem hπ) hσ.1, ?_⟩
        funext s
        have := congrFun hσ.2 (π s)
        simp only [Function.comp_apply] at this
        simp only [Function.comp_apply, mul_inv_rev, inv_inv, Perm.coe_mul, this]
      · intro ρ _
        simp
      · intro σ _
        simp
  · intro σ hσ
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hσ ⊢
    exact (Quotient.sound ⟨σ, hσ, rfl⟩ : Quotient.mk (colorSetoid G m) f = _).symm

open Classical in
lemma burnside_weighted (G : Subgroup (Perm S)) (m : ℕ) :
    ∑ σ ∈ univ.filter (fun σ : Perm S => σ ∈ G),
        ∑ f ∈ univ.filter (fun f : S → Fin m => f ∘ ⇑σ⁻¹ = f), colorWeight f
      = (#(univ.filter (fun σ : Perm S => σ ∈ G)) : ℚ) • patternInventory G m := by
  set Gf := univ.filter (fun σ : Perm S => σ ∈ G) with hGf
  have h1 : ∑ σ ∈ Gf, ∑ f ∈ univ.filter (fun f : S → Fin m => f ∘ ⇑σ⁻¹ = f), colorWeight f
      = ∑ f : S → Fin m, ∑ σ ∈ (Gf.filter (fun σ : Perm S => f ∘ ⇑σ⁻¹ = f)), colorWeight f := by
    apply Finset.sum_comm'
    intro σ f
    simp [Gf]
  rw [h1, ← Finset.sum_fiberwise univ (fun f => Quotient.mk (colorSetoid G m) f), patternInventory,
    Finset.smul_sum]
  refine Finset.sum_congr (by ext; simp) (fun q _ => ?_)
  have hne : (#{f' ∈ (univ : Finset (S → Fin m)) | Quotient.mk (colorSetoid G m) f' = q} : ℚ) ≠ 0 := by
    have : q.out ∈ ({f' ∈ (univ : Finset (S → Fin m)) | Quotient.mk (colorSetoid G m) f' = q}) := by
      simp [Quotient.out_eq]
    exact_mod_cast (Finset.card_pos.mpr ⟨_, this⟩).ne'
  have hterm : ∀ f ∈ ({f' ∈ (univ : Finset (S → Fin m)) | Quotient.mk (colorSetoid G m) f' = q}),
      ∑ σ ∈ (Gf.filter (fun σ : Perm S => f ∘ ⇑σ⁻¹ = f)), colorWeight f =
        ((#Gf : ℚ) / #{f' ∈ (univ : Finset (S → Fin m)) | Quotient.mk (colorSetoid G m) f' = q})
          • colorWeight q.out := by
    intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    have hos := orbit_stab G m f
    rw [hf] at hos
    have hw : colorWeight f = colorWeight q.out := by
      have e : Quotient.mk (colorSetoid G m) q.out = Quotient.mk (colorSetoid G m) f := by
        rw [Quotient.out_eq, hf]
      obtain ⟨π, _, hπ⟩ := Quotient.exact e
      rw [hπ, weight_inv]
    rw [Finset.sum_const, hw, ← Nat.cast_smul_eq_nsmul ℚ]
    congr 1
    rw [eq_div_iff hne]
    exact_mod_cast hos
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  field_simp

end Burnside

theorem polya_core {S : Type*} [Fintype S] [DecidableEq S]
    (G : Subgroup (Equiv.Perm S)) (m : ℕ) :
    bind₁ (fun k : Fin (Fintype.card S) => ∑ i : Fin m, (X i : MvPolynomial (Fin m) ℚ) ^ (k.val + 1))
        (cycleIndex G) = patternInventory G m := by
  classical
  unfold cycleIndex
  rw [map_smul, map_sum]
  rw [Finset.sum_congr rfl (fun σ _ => monomial_eval σ m)]
  rw [Finset.sum_congr rfl (fun σ _ => (fixed_sum σ m).symm), burnside_weighted, smul_smul]
  have hN : (Nat.card G : ℚ) = #(univ.filter (fun σ : Perm S => σ ∈ G)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hpos : (#(univ.filter (fun σ : Perm S => σ ∈ G)) : ℚ) ≠ 0 := by
    have : (1 : Perm S) ∈ univ.filter (fun σ : Perm S => σ ∈ G) := by simp [G.one_mem]
    exact_mod_cast (Finset.card_pos.mpr ⟨_, this⟩).ne'
  rw [hN, inv_mul_cancel₀ hpos, one_smul]

end AppliedComb.Polya

open AppliedComb.Polya
open MvPolynomial

theorem solution {S : Type*} [Fintype S] [DecidableEq S]
    (G : Subgroup (Equiv.Perm S)) (m : ℕ) :
    bind₁ (fun k : Fin (Fintype.card S) => ∑ i : Fin m, (X i : MvPolynomial (Fin m) ℚ) ^ (k.val + 1))
        (cycleIndex G) = patternInventory G m := by
  exact polya_core G m
