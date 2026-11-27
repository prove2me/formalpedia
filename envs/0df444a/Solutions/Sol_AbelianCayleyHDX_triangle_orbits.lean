-- Prove2me | solution 1 for AbelianCayleyHDX.triangle_orbits
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T22:51:39.258309+00:00
-- url     : https://prove2.me/submissions/b2f3bb5d-25eb-4210-a921-5e90a533c099

import Mathlib
import Definitions.Def_AbelianCayleyHDX_IsGoodRelationMatrix
import Definitions.Def_AbelianCayleyHDX_kerF2
import Definitions.Def_AbelianCayleyHDX_Htilde
import Definitions.Def_AbelianCayleyHDX_relationComplex
import Definitions.Def_AbelianCayleyHDX_IsCayleyComplex
import Definitions.Def_AbelianCayleyHDX_IsTranslationInvariant
import Definitions.Def_AbelianCayleyHDX_linkVerts
import Definitions.Def_AbelianCayleyHDX_linkWeight
import Definitions.Def_AbelianCayleyHDX_PH
import Definitions.Def_AbelianCayleyHDX_HasLocalSpectralNorm
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX.RelCx

/-! ### Characteristic two -/

lemma z2_ne_zero_iff (a : ZMod 2) : a ≠ 0 ↔ a = 1 := by revert a; decide

lemma vadd_self {n : ℕ} (x : Vec n) : x + x = 0 := by
  ext k; simp only [Pi.add_apply, Pi.zero_apply]; grind

lemma vadd_cancel_left {n : ℕ} (x y : Vec n) : x + (x + y) = y := by
  rw [← add_assoc, vadd_self, zero_add]

lemma vadd_eq_iff {n : ℕ} (x y z : Vec n) : x + y = z ↔ y = x + z := by
  constructor
  · rintro rfl; rw [vadd_cancel_left]
  · rintro rfl; rw [vadd_cancel_left]

lemma vadd_eq_zero_iff {n : ℕ} (x y : Vec n) : x + y = 0 ↔ x = y := by
  rw [vadd_eq_iff, add_zero, eq_comm]

lemma z2_add_eq_zero_iff (x y : ZMod 2) : x + y = 0 ↔ x = y := by
  revert x y; decide

/-! ### The relation matrix -/

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] {n : ℕ}
  (H : Matrix ι κ (ZMod 2)) (φ : (κ → ZMod 2) →ₗ[ZMod 2] Vec n)

/-- The support of a row. -/
def supp (r : ι) : Finset κ := Finset.univ.filter fun i => H r i ≠ 0

/-- The generator `s_i = φ(e_i)`. -/
def s (i : κ) : Vec n := φ (Pi.single i 1)

lemma mem_supp {H : Matrix ι κ (ZMod 2)} {r : ι} {i : κ} : i ∈ supp H r ↔ H r i ≠ 0 := by
  simp [supp]

lemma eq_sum_single (v : κ → ZMod 2) :
    v = ∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), Pi.single i 1 := by
  ext k
  rw [Finset.sum_apply]
  simp only [Pi.single_apply]
  rw [Finset.sum_ite_eq]
  by_cases hk : v k = 0
  · simp [hk]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [if_pos hk]
    exact (z2_ne_zero_iff _).1 hk

lemma map_eq_sum (v : κ → ZMod 2) :
    φ v = ∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0), s φ i := by
  conv_lhs => rw [eq_sum_single v]
  rw [map_sum]; rfl

variable {H φ}
variable {ρ : ℕ} (hH : IsGoodRelationMatrix H ρ) (hker : LinearMap.ker φ = rowspan H)
include hH hker

lemma weight_ge_three (v : κ → ZMod 2) (hv : φ v = 0) (hne : v ≠ 0) :
    3 ≤ (Finset.univ.filter fun i => v i ≠ 0).card := by
  have : v ∈ rowspan H := by rw [← hker]; exact hv
  exact hH.2.2.2.2 v this hne

lemma s_ne_zero (i : κ) : s φ i ≠ 0 := by
  intro h
  have := weight_ge_three hH hker (Pi.single i 1) h (by
    intro h'; have := congrFun h' i; simp at this)
  have h1 : (Finset.univ.filter fun j => (Pi.single i (1 : ZMod 2) : κ → ZMod 2) j ≠ 0) = {i} := by
    ext j; by_cases hj : j = i <;> simp [Pi.single_apply, hj]
  rw [h1] at this; simp at this

lemma s_inj : Function.Injective (s φ) := by
  intro i j hij
  by_contra hne
  have h0 : φ (Pi.single i 1 + Pi.single j 1) = 0 := by
    rw [map_add]; change s φ i + s φ j = 0; rw [hij, vadd_self]
  have := weight_ge_three hH hker _ h0 (by
    intro h'; have := congrFun h' i; simp [Pi.single_apply, hne] at this)
  have h1 : (Finset.univ.filter fun k =>
      (Pi.single i (1 : ZMod 2) + Pi.single j 1 : κ → ZMod 2) k ≠ 0) ⊆ {i, j} := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    by_contra hk'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
    apply hk; simp [Pi.single_apply, hk'.1, hk'.2]
  have := (Finset.card_le_card h1).trans (Finset.card_le_two)
  omega

lemma supp_card (r : ι) : (supp H r).card = 3 := hH.2.1 r

lemma row_sum (r : ι) : ∑ i ∈ supp H r, s φ i = 0 := by
  have h1 : φ (H r) = 0 := by
    have : H r ∈ rowspan H := Submodule.subset_span ⟨r, rfl⟩
    rw [← hker] at this; exact this
  rw [map_eq_sum] at h1
  exact h1

/-- Distinct rows share at most one column. -/
lemma rows_eq {r r' : ι} {i j : κ} (hij : i ≠ j) (hi : i ∈ supp H r) (hj : j ∈ supp H r)
    (hi' : i ∈ supp H r') (hj' : j ∈ supp H r') : r = r' := by
  by_contra hne
  have hv : H r + H r' ≠ 0 := by
    intro h
    apply hne; apply hH.1
    ext c; have := congrFun h c
    simp only [Pi.add_apply, Pi.zero_apply] at this
    exact (z2_add_eq_zero_iff _ _).1 this
  have hrow : ∀ r'' : ι, H r'' ∈ rowspan H := fun r'' => Submodule.subset_span ⟨r'', rfl⟩
  have hmem : H r + H r' ∈ rowspan H := Submodule.add_mem _ (hrow r) (hrow r')
  have h3 := hH.2.2.2.2 _ hmem hv
  rw [mem_supp] at hi hj hi' hj'
  -- the support of the sum is contained in (supp r ∪ supp r') \ {i, j}
  have hsub : (Finset.univ.filter fun c => (H r + H r') c ≠ 0) ⊆
      (supp H r ∪ supp H r') \ {i, j} := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply] at hc
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      not_or, mem_supp]
    refine ⟨?_, ?_, ?_⟩
    · by_contra h; push Not at h; rw [h.1, h.2] at hc; simp at hc
    · rintro rfl
      rw [(z2_ne_zero_iff _).1 hi, (z2_ne_zero_iff _).1 hi'] at hc; exact hc (by decide)
    · rintro rfl
      rw [(z2_ne_zero_iff _).1 hj, (z2_ne_zero_iff _).1 hj'] at hc; exact hc (by decide)
  have hcard := Finset.card_le_card hsub
  have hij2 : ({i, j} : Finset κ) ⊆ supp H r ∪ supp H r' := by
    intro c hc; simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact Finset.mem_union_left _ (mem_supp.2 hi)
    · exact Finset.mem_union_left _ (mem_supp.2 hj)
  rw [Finset.card_sdiff_of_subset hij2, Finset.card_pair hij] at hcard
  have hu := Finset.card_union_add_card_inter (supp H r) (supp H r')
  have hint : ({i, j} : Finset κ) ⊆ supp H r ∩ supp H r' := by
    intro c hc; simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact Finset.mem_inter.2 ⟨mem_supp.2 hi, mem_supp.2 hi'⟩
    · exact Finset.mem_inter.2 ⟨mem_supp.2 hj, mem_supp.2 hj'⟩
  have hi2 := Finset.card_le_card hint
  rw [Finset.card_pair hij] at hi2
  rw [supp_card hH hker, supp_card hH hker] at hu
  omega

lemma inter_card_le_one {r r' : ι} (hne : r ≠ r') :
    (supp H r ∩ supp H r').card ≤ 1 := by
  by_contra h; push Not at h
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 h
  rw [Finset.mem_inter] at hi hj
  exact hne (rows_eq hH hker hij hi.1 hj.1 hi.2 hj.2)

/-- The third column of a row. -/
lemma third {r : ι} {i j : κ} (hij : i ≠ j) (hi : i ∈ supp H r) (hj : j ∈ supp H r) :
    ∃ k ∈ supp H r, k ≠ i ∧ k ≠ j ∧ supp H r = {i, j, k} ∧ s φ i + s φ j = s φ k := by
  obtain ⟨a, b, c, hab, hac, hbc, he⟩ := Finset.card_eq_three.1 (supp_card hH hker r)
  have hsum := row_sum hH hker r
  rw [he, Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc] at hsum
  rw [he] at hi hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
  all_goals first | exact absurd rfl hij | skip
  · refine ⟨c, by simp [he], hac.symm, hbc.symm, he, ?_⟩
    ext k; have := congrFun hsum k; simp only [Pi.add_apply, Pi.zero_apply] at *; grind
  · refine ⟨b, by simp [he], hab.symm, hbc, by rw [he]; ext; simp; tauto, ?_⟩
    ext k; have := congrFun hsum k; simp only [Pi.add_apply, Pi.zero_apply] at *; grind
  · refine ⟨c, by simp [he], hbc.symm, hac.symm, by rw [he]; ext; simp; tauto, ?_⟩
    ext k; have := congrFun hsum k; simp only [Pi.add_apply, Pi.zero_apply] at *; grind
  · refine ⟨a, by simp [he], hab, hac, by rw [he]; ext; simp; tauto, ?_⟩
    ext k; have := congrFun hsum k; simp only [Pi.add_apply, Pi.zero_apply] at *; grind
  · refine ⟨b, by simp [he], hbc, hab.symm, by rw [he]; ext; simp; tauto, ?_⟩
    ext k; have := congrFun hsum k; simp only [Pi.add_apply, Pi.zero_apply] at *; grind
  · refine ⟨a, by simp [he], hac, hab, by rw [he]; ext; simp; tauto, ?_⟩
    ext k; have := congrFun hsum k; simp only [Pi.add_apply, Pi.zero_apply] at *; grind

omit hH hker in
lemma mem_T {τ : Finset (Vec n)} :
    τ ∈ relationComplex H φ ↔ ∃ (r : ι) (g : Vec n) (i j : κ), i ≠ j ∧ i ∈ supp H r ∧
      j ∈ supp H r ∧ τ = {g, g + s φ i, g + s φ i + s φ j} := by
  simp only [relationComplex, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Prod.exists, mem_supp, s]
  constructor
  · rintro ⟨r, g, i, j, ⟨hij, hi, hj⟩, rfl⟩; exact ⟨r, g, i, j, hij, hi, hj, rfl⟩
  · rintro ⟨r, g, i, j, hij, hi, hj, rfl⟩; exact ⟨r, g, i, j, ⟨hij, hi, hj⟩, rfl⟩

/-- Pairwise sums of a triangle are generators of its row. -/
lemma pair_sum {r : ι} {g : Vec n} {i j : κ} (hij : i ≠ j) (hi : i ∈ supp H r)
    (hj : j ∈ supp H r) {x y : Vec n}
    (hx : x ∈ ({g, g + s φ i, g + s φ i + s φ j} : Finset (Vec n)))
    (hy : y ∈ ({g, g + s φ i, g + s φ i + s φ j} : Finset (Vec n))) (hxy : x ≠ y) :
    ∃ m ∈ supp H r, x + y = s φ m := by
  obtain ⟨k, hk, -, -, -, hijk⟩ := third hH hker hij hi hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals first | exact absurd rfl hxy | skip
  · refine ⟨i, hi, ?_⟩; ext t; simp only [Pi.add_apply]; grind
  · refine ⟨k, hk, ?_⟩; ext t; have := congrFun hijk t; simp only [Pi.add_apply] at *; grind
  · refine ⟨i, hi, ?_⟩; ext t; simp only [Pi.add_apply]; grind
  · refine ⟨j, hj, ?_⟩; ext t; simp only [Pi.add_apply]; grind
  · refine ⟨k, hk, ?_⟩; ext t; have := congrFun hijk t; simp only [Pi.add_apply] at *; grind
  · refine ⟨j, hj, ?_⟩; ext t; simp only [Pi.add_apply]; grind

lemma card_tri {g : Vec n} {i j : κ} (hij : i ≠ j) :
    ({g, g + s φ i, g + s φ i + s φ j} : Finset (Vec n)).card = 3 := by
  have hi := s_ne_zero hH hker i
  have hj := s_ne_zero hH hker j
  have hij' : s φ i ≠ s φ j := fun h => hij (s_inj hH hker h)
  rw [Finset.card_eq_three]
  refine ⟨g, g + s φ i, g + s φ i + s φ j, ?_, ?_, ?_, rfl⟩
  · intro h; apply hi; ext t; have := congrFun h t
    simp only [Pi.add_apply, Pi.zero_apply] at this ⊢; grind
  · intro h; apply hij'; ext t; have := congrFun h t
    simp only [Pi.add_apply, Pi.zero_apply] at this ⊢; grind
  · intro h; apply hj; ext t; have := congrFun h t
    simp only [Pi.add_apply, Pi.zero_apply] at this ⊢; grind

lemma card_of_mem {τ : Finset (Vec n)} (hτ : τ ∈ relationComplex H φ) : τ.card = 3 := by
  obtain ⟨r, g, i, j, hij, -, -, rfl⟩ := mem_T.1 hτ
  exact card_tri hH hker hij

/-- `{g, g + s_i, g + s_j}` is a triangle when `i ≠ j` share a row. -/
lemma tri_mem' {r : ι} (g : Vec n) {i j : κ} (hij : i ≠ j) (hi : i ∈ supp H r)
    (hj : j ∈ supp H r) : ({g, g + s φ i, g + s φ j} : Finset (Vec n)) ∈ relationComplex H φ := by
  obtain ⟨k, hk, hki, hkj, -, hijk⟩ := third hH hker hij hi hj
  rw [mem_T]
  refine ⟨r, g, i, k, hki.symm, hi, hk, ?_⟩
  have : s φ i + s φ k = s φ j := by
    rw [← hijk, vadd_cancel_left]
  rw [add_assoc g, this]

omit hH hker in
/-- Triangle membership is translation invariant. -/
lemma image_add_mem {τ : Finset (Vec n)} (hτ : τ ∈ relationComplex H φ) (x : Vec n) :
    τ.image (· + x) ∈ relationComplex H φ := by
  obtain ⟨r, g, i, j, hij, hi, hj, rfl⟩ := mem_T.1 hτ
  rw [mem_T]
  refine ⟨r, g + x, i, j, hij, hi, hj, ?_⟩
  simp only [Finset.image_insert, Finset.image_singleton]
  congr 1
  · congr 1
    · abel
    · congr 1; abel

/-- The row of a triangle. -/
lemma exists_row_of_mem {τ : Finset (Vec n)} (hτ : τ ∈ relationComplex H φ) :
    ∃ r : ι, ∀ x ∈ τ, ∀ y ∈ τ, x ≠ y → ∃ m ∈ supp H r, x + y = s φ m := by
  obtain ⟨r, g, i, j, hij, hi, hj, rfl⟩ := mem_T.1 hτ
  exact ⟨r, fun x hx y hy hxy => pair_sum hH hker hij hi hj hx hy hxy⟩

end

/-- `j` is a neighbour of `i`: they are distinct and share a row. -/
def IsNbr {ι κ : Type*} [Fintype κ] (H : Matrix ι κ (ZMod 2)) (i j : κ) : Prop :=
  i ≠ j ∧ ∃ r : ι, i ∈ Finset.univ.filter (fun c => H r c ≠ 0) ∧
    j ∈ Finset.univ.filter (fun c => H r c ≠ 0)

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] {n : ℕ}
  {H : Matrix ι κ (ZMod 2)} {φ : (κ → ZMod 2) →ₗ[ZMod 2] Vec n}
  {ρ : ℕ} (hH : IsGoodRelationMatrix H ρ) (hker : LinearMap.ker φ = rowspan H)
include hH hker

lemma isNbr_iff {i j : κ} : IsNbr H i j ↔ i ≠ j ∧ ∃ r : ι, i ∈ supp H r ∧ j ∈ supp H r :=
  Iff.rfl

lemma rows_through_card (i : κ) :
    (Finset.univ.filter fun r : ι => i ∈ supp H r).card = ρ := by
  rw [← hH.2.2.2.1 i]; simp [mem_supp, colWeight]

open Classical in
lemma card_nbrs (i : κ) : (Finset.univ.filter fun j => IsNbr H i j).card = 2 * ρ := by
  have heq : (Finset.univ.filter fun j => IsNbr H i j) =
      (Finset.univ.filter fun r : ι => i ∈ supp H r).biUnion fun r => (supp H r).erase i := by
    ext j
    simp only [isNbr_iff hH hker, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.mem_erase]
    constructor
    · rintro ⟨hij, r, hi, hj⟩; exact ⟨r, hi, Ne.symm hij, hj⟩
    · rintro ⟨r, hi, hji, hj⟩; exact ⟨Ne.symm hji, r, hi, hj⟩
  rw [heq, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (g := fun _ => 2)]
    · simp [rows_through_card hH hker, mul_comm]
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      rw [Finset.card_erase_of_mem hr, supp_card hH hker]
  · intro r hr r' hr' hne
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hr hr'
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro j hj hj'
    rw [Finset.mem_erase] at hj hj'
    exact hne (rows_eq hH hker (Ne.symm hj.1) hr hj.2 hr' hj'.2)

/-- Triangles through `0`. -/
lemma zero_tri_iff (u w : Vec n) :
    ({0, u, w} : Finset (Vec n)) ∈ relationComplex H φ ↔
      ∃ i j, u = s φ i ∧ w = s φ j ∧ IsNbr H i j := by
  constructor
  · intro hτ
    have hc := card_of_mem hH hker hτ
    have h0u : (0 : Vec n) ≠ u := by
      intro h; subst h
      have := Finset.card_le_two (a := (0 : Vec n)) (b := w)
      simp only [Finset.insert_eq_of_mem, Finset.mem_insert, true_or] at hc; omega
    have h0w : (0 : Vec n) ≠ w := by
      intro h; subst h
      have := Finset.card_le_two (a := (0 : Vec n)) (b := u)
      have e : ({0, u, 0} : Finset (Vec n)) = {0, u} := by ext; simp; tauto
      rw [e] at hc; omega
    have huw : u ≠ w := by
      intro h; subst h
      have := Finset.card_le_two (a := (0 : Vec n)) (b := u)
      simp at hc; omega
    obtain ⟨r, hr⟩ := exists_row_of_mem hH hker hτ
    obtain ⟨i, hi, hiu⟩ := hr 0 (by simp) u (by simp) h0u
    obtain ⟨j, hj, hjw⟩ := hr 0 (by simp) w (by simp) h0w
    rw [zero_add] at hiu hjw
    refine ⟨i, j, hiu, hjw, ?_, r, hi, hj⟩
    rintro rfl; exact huw (hiu.trans hjw.symm)
  · rintro ⟨i, j, rfl, rfl, hij, r, hi, hj⟩
    have := tri_mem' hH hker (0 : Vec n) hij hi hj
    simpa using this

lemma exists_row_through (m : κ) : ∃ r : ι, ∃ j, m ∈ supp H r ∧ j ∈ supp H r ∧ m ≠ j := by
  have hpos : 0 < (Finset.univ.filter fun r : ι => m ∈ supp H r).card := by
    rw [rows_through_card hH hker]; exact hH.2.2.1
  obtain ⟨r, hr⟩ := Finset.card_pos.1 hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
  have : 1 < (supp H r).card := by rw [supp_card hH hker]; norm_num
  obtain ⟨j, hj, hjm⟩ := Finset.exists_mem_ne this m
  exact ⟨r, j, hr, hj, Ne.symm hjm⟩

lemma linkVerts_zero :
    linkVerts (relationComplex H φ) 0 = Finset.univ.image (s φ) := by
  ext u
  simp only [linkVerts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hu0, τ, hτ, h0, hu⟩
    obtain ⟨r, hr⟩ := exists_row_of_mem hH hker hτ
    obtain ⟨m, -, hm⟩ := hr 0 h0 u hu (Ne.symm hu0)
    exact ⟨m, by rw [zero_add] at hm; exact hm.symm⟩
  · rintro ⟨m, rfl⟩
    refine ⟨s_ne_zero hH hker m, ?_⟩
    obtain ⟨r, j, hm, hj, hmj⟩ := exists_row_through hH hker m
    exact ⟨_, tri_mem' hH hker (0 : Vec n) hmj hm hj, by simp, by simp⟩

open Classical in
lemma linkWeight_zero (i j : κ) :
    linkWeight (relationComplex H φ) 0 (s φ i) (s φ j) = if IsNbr H i j then 1 else 0 := by
  unfold linkWeight
  by_cases h : IsNbr H i j
  · rw [if_pos h, if_pos ((zero_tri_iff hH hker _ _).2 ⟨i, j, rfl, rfl, h⟩)]
  · rw [if_neg h, if_neg]
    rw [zero_tri_iff hH hker]
    rintro ⟨i', j', hi, hj, hn⟩
    rw [s_inj hH hker hi, s_inj hH hker hj] at h; exact h hn

open Classical in
lemma gram_entry (i j : κ) :
    ((Htilde H).transpose * Htilde H - (ρ : ℝ) • (1 : Matrix κ κ ℝ)) i j =
      if IsNbr H i j then 1 else 0 := by
  have hval : ∀ r c, ((H r c).val : ℝ) = if c ∈ supp H r then 1 else 0 := by
    intro r c
    by_cases h : H r c = 0
    · simp [h, mem_supp]
    · rw [if_pos (mem_supp.2 h), (z2_ne_zero_iff _).1 h]; simp [ZMod.val_one]
  have hsum : ∀ i j : κ, ((Htilde H).transpose * Htilde H) i j =
      ((Finset.univ.filter fun r : ι => i ∈ supp H r ∧ j ∈ supp H r).card : ℝ) := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Htilde, Matrix.of_apply, hval]
    rw [Finset.card_filter]; push_cast
    refine Finset.sum_congr rfl (fun r _ => ?_)
    by_cases h1 : i ∈ supp H r <;> by_cases h2 : j ∈ supp H r <;> simp [h1, h2]
  rw [Matrix.sub_apply, hsum, Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp only [and_self, if_true, smul_eq_mul, mul_one, rows_through_card hH hker]
    rw [if_neg (fun h => h.1 rfl)]; ring
  · simp only [hij, if_false, smul_eq_mul, mul_zero, sub_zero]
    by_cases hn : IsNbr H i j
    · rw [if_pos hn]
      obtain ⟨-, r, hi, hj⟩ := (isNbr_iff hH hker).1 hn
      have : (Finset.univ.filter fun r : ι => i ∈ supp H r ∧ j ∈ supp H r) = {r} := by
        ext r'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hi', hj'⟩; exact (rows_eq hH hker hij hi hj hi' hj').symm
        · rintro rfl; exact ⟨hi, hj⟩
      rw [this]; simp
    · rw [if_neg hn]
      have : (Finset.univ.filter fun r : ι => i ∈ supp H r ∧ j ∈ supp H r) = ∅ := by
        ext r'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨hi', hj'⟩; exact hn ((isNbr_iff hH hker).2 ⟨hij, r', hi', hj'⟩)
      rw [this]; simp

open Classical in
lemma linkWeight_sum (i : κ) :
    ∑ w ∈ linkVerts (relationComplex H φ) 0, linkWeight (relationComplex H φ) 0 (s φ i) w =
      2 * (ρ : ℝ) := by
  rw [linkVerts_zero hH hker, Finset.sum_image (fun a _ b _ h => s_inj hH hker h)]
  simp only [linkWeight_zero hH hker, Finset.sum_boole]
  rw [card_nbrs hH hker]; push_cast; ring

/-! ### Triangles containing an edge -/

lemma tri_count (x : Vec n) (m : κ) :
    triCount (relationComplex H φ) {x, x + s φ m} = 2 * ρ := by
  classical
  unfold triCount
  rw [← card_nbrs hH hker m]
  symm
  apply Finset.card_bij (fun j _ => ({x, x + s φ m, x + s φ j} : Finset (Vec n)))
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    obtain ⟨hmj, r, hm, hj⟩ := (isNbr_iff hH hker).1 hj
    refine ⟨tri_mem' hH hker x hmj hm hj, ?_⟩
    intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢; tauto
  · intro j hj j' hj' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
    have hmem : x + s φ j ∈ ({x, x + s φ m, x + s φ j'} : Finset (Vec n)) := by
      rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1 | h1
    · exact absurd (left_eq_add.1 h1.symm) (s_ne_zero hH hker j)
    · rw [add_right_inj] at h1; exact absurd (s_inj hH hker h1) (Ne.symm hj.1)
    · rw [add_right_inj] at h1; exact s_inj hH hker h1
  · intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    obtain ⟨hτT, hsub⟩ := hτ
    have hc := card_of_mem hH hker hτT
    have hxm : x ≠ x + s φ m := by
      intro h; apply s_ne_zero hH hker m
      exact left_eq_add.1 h
    have hx : x ∈ τ := hsub (by simp)
    have hxm' : x + s φ m ∈ τ := hsub (by simp)
    obtain ⟨z, hz, hz1, hz2⟩ : ∃ z ∈ τ, z ≠ x ∧ z ≠ x + s φ m := by
      by_contra hcon; push Not at hcon
      have : τ ⊆ {x, x + s φ m} := by
        intro z hz
        by_cases h1 : z = x
        · simp [h1]
        · simp [hcon z hz h1]
      have := Finset.card_le_card this
      rw [Finset.card_pair hxm] at this; omega
    obtain ⟨r, hr⟩ := exists_row_of_mem hH hker hτT
    obtain ⟨j, hj, hjz⟩ := hr x hx z hz (Ne.symm hz1)
    obtain ⟨m', hm', hm'e⟩ := hr x hx _ hxm' hxm
    rw [vadd_cancel_left] at hm'e
    rw [← s_inj hH hker hm'e] at hm'
    have hzj : z = x + s φ j := by rw [← hjz, vadd_cancel_left]
    refine ⟨j, (isNbr_iff hH hker).2 ⟨?_, r, hm', hj⟩, ?_⟩
    · rintro rfl; exact hz2 hzj
    · apply Finset.eq_of_subset_of_card_le
      · intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact hx
        · exact hxm'
        · rw [← hzj]; exact hz
      · rw [hc]
        have hne3 : x + s φ m ≠ x + s φ j := by
          intro h; apply hz2; rw [hzj, ← h]
        rw [Finset.card_insert_of_notMem, Finset.card_pair hne3]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hxm, fun h => hz1 (hzj.trans h.symm)⟩

/-! ### The edges -/

lemma edges_eq :
    edges (relationComplex H φ) = (Finset.univ ×ˢ Finset.univ.image (s φ)).image
      (fun p : Vec n × Vec n => ({p.1, p.1 + p.2} : Finset (Vec n))) := by
  ext e
  simp only [edges, Finset.mem_biUnion, Finset.mem_powersetCard, Finset.mem_image,
    Finset.mem_product, Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨τ, hτ, hsub, hcard⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hcard
    obtain ⟨r, hr⟩ := exists_row_of_mem hH hker hτ
    obtain ⟨m, -, hm⟩ := hr a (hsub (by simp)) b (hsub (by simp)) hab
    refine ⟨a, s φ m, ⟨m, rfl⟩, ?_⟩
    rw [← hm, vadd_cancel_left]
  · rintro ⟨x, u, ⟨m, rfl⟩, rfl⟩
    obtain ⟨r, j, hm, hj, hmj⟩ := exists_row_through hH hker m
    refine ⟨_, tri_mem' hH hker x hmj hm hj, ?_, ?_⟩
    · intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢; tauto
    · rw [Finset.card_pair]
      intro h; apply s_ne_zero hH hker m
      exact left_eq_add.1 h

/-! ### Dimension -/

omit hH in
lemma dim_eq (hφ : Function.Surjective φ) : n = Module.finrank (ZMod 2) (kerF2 H) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  rw [LinearMap.range_eq_top.2 hφ, finrank_top, Module.finrank_fin_fun, hker] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker H.mulVecLin
  have h3 : Module.finrank (ZMod 2) (LinearMap.range H.mulVecLin) =
      Module.finrank (ZMod 2) (rowspan H) := by
    have := Matrix.rank_eq_finrank_span_row H
    rw [Matrix.rank] at this
    rw [this]; rfl
  rw [h3] at h2
  unfold kerF2
  omega

end

end AbelianCayleyHDX.RelCx


open ReplParity (Vec)

namespace AbelianCayleyHDX.RelCx

lemma three_smul_vec {n : ℕ} (g : Vec n) : (3 : ℕ) • g = g := by
  ext t; simp only [Pi.smul_apply, nsmul_eq_mul]; push_cast; grind

lemma card_vec (n : ℕ) : Fintype.card (Vec n) = 2 ^ n := by simp

lemma sum_image_add {n : ℕ} (τ : Finset (Vec n)) (g : Vec n) :
    ∑ y ∈ τ.image (· + g), y = ∑ y ∈ τ, y + τ.card • g := by
  rw [Finset.sum_image (fun a _ b _ h => add_right_cancel h), Finset.sum_add_distrib,
    Finset.sum_const]

lemma translate_inj {n : ℕ} (τ : Finset (Vec n)) (hτ : τ.card = 3) :
    Function.Injective fun g : Vec n => τ.image (· + g) := by
  intro g g' h
  have := congrArg (fun σ : Finset (Vec n) => ∑ y ∈ σ, y) h
  simp only [sum_image_add, hτ, three_smul_vec] at this
  exact add_left_cancel this

lemma tri_perm {n : ℕ} {a b c a' b' c' : Vec n}
    (h : (a' = a ∧ b' = b ∧ c' = c) ∨ (a' = a ∧ b' = c ∧ c' = b) ∨ (a' = b ∧ b' = a ∧ c' = c) ∨
      (a' = b ∧ b' = c ∧ c' = a) ∨ (a' = c ∧ b' = a ∧ c' = b) ∨ (a' = c ∧ b' = b ∧ c' = a)) :
    ({a, b, c} : Finset (Vec n)) = {a', b', c'} := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals (ext; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] {n : ℕ}
  {H : Matrix ι κ (ZMod 2)} {φ : (κ → ZMod 2) →ₗ[ZMod 2] Vec n}
  {ρ : ℕ} (hH : IsGoodRelationMatrix H ρ) (hker : LinearMap.ker φ = rowspan H)
include hH hker

lemma row_recover {r r' : ι} {g g' x : Vec n} {i j i' j' : κ} (hij : i ≠ j)
    (hi : i ∈ supp H r) (hj : j ∈ supp H r) (hij' : i' ≠ j') (hi' : i' ∈ supp H r')
    (hj' : j' ∈ supp H r')
    (h : ({g, g + s φ i, g + s φ i + s φ j} : Finset (Vec n)).image (· + x) =
      {g', g' + s φ i', g' + s φ i' + s φ j'}) : r = r' := by
  have hA : g + x ∈ ({g', g' + s φ i', g' + s φ i' + s φ j'} : Finset (Vec n)) := by
    rw [← h]; exact Finset.mem_image_of_mem _ (by simp)
  have hB : g + s φ i + x ∈ ({g', g' + s φ i', g' + s φ i' + s φ j'} : Finset (Vec n)) := by
    rw [← h]; exact Finset.mem_image_of_mem _ (by simp)
  have hC : g + s φ i + s φ j + x ∈
      ({g', g' + s φ i', g' + s φ i' + s φ j'} : Finset (Vec n)) := by
    rw [← h]; exact Finset.mem_image_of_mem _ (by simp)
  have hsi := s_ne_zero hH hker i
  have hsj := s_ne_zero hH hker j
  obtain ⟨m, hm, hme⟩ := pair_sum hH hker hij' hi' hj' hA hB (by
    intro e; apply hsi; ext t; have := congrFun e t
    simp only [Pi.add_apply, Pi.zero_apply] at this ⊢; grind)
  obtain ⟨m', hm', hme'⟩ := pair_sum hH hker hij' hi' hj' hB hC (by
    intro e; apply hsj; ext t; have := congrFun e t
    simp only [Pi.add_apply, Pi.zero_apply] at this ⊢; grind)
  have e1 : s φ i = s φ m := by
    rw [← hme]; ext t; simp only [Pi.add_apply]; grind
  have e2 : s φ j = s φ m' := by
    rw [← hme']; ext t; simp only [Pi.add_apply]; grind
  rw [← s_inj hH hker e1] at hm
  rw [← s_inj hH hker e2] at hm'
  exact rows_eq hH hker hij hi hj hm hm'

lemma card_T : (relationComplex H φ).card = Fintype.card ι * 2 ^ n := by
  classical
  -- choose two distinct columns in every row
  have hpair : ∀ r : ι, ∃ a b : κ, a ≠ b ∧ a ∈ supp H r ∧ b ∈ supp H r := by
    intro r
    obtain ⟨a, b, c, hab, -, -, he⟩ := Finset.card_eq_three.1 (supp_card hH hker r)
    exact ⟨a, b, hab, by simp [he], by simp [he]⟩
  choose a b hab ha hb using hpair
  let O : ι × Vec n → Finset (Vec n) := fun p =>
    {p.2, p.2 + s φ (a p.1), p.2 + s φ (a p.1) + s φ (b p.1)}
  have hT : relationComplex H φ = Finset.univ.image O := by
    ext τ
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
    constructor
    · intro hτ
      obtain ⟨r, g, i, j, hij, hi, hj, rfl⟩ := mem_T.1 hτ
      obtain ⟨c, hc, hca, hcb, he, habc⟩ := third hH hker (hab r) (ha r) (hb r)
      have hC : s φ c = s φ (a r) + s φ (b r) := habc.symm
      rw [he] at hi hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      refine ⟨r, ?_⟩
      simp only [O]
      rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
      all_goals first | exact absurd rfl hij | skip
      · exact ⟨g, rfl⟩
      · refine ⟨g + s φ (a r), tri_perm ?_⟩
        try rw [hC]
        first
          | (left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; right; right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; right; right; right; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
      · refine ⟨g + s φ (a r) + s φ (b r), tri_perm ?_⟩
        try rw [hC]
        first
          | (left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; right; right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; right; right; right; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
      · refine ⟨g + s φ (a r), tri_perm ?_⟩
        try rw [hC]
        first
          | (left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; right; right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; right; right; right; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
      · refine ⟨g + s φ (a r) + s φ (b r), tri_perm ?_⟩
        try rw [hC]
        first
          | (left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; right; right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; right; right; right; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
      · refine ⟨g, tri_perm ?_⟩
        try rw [hC]
        first
          | (left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; right; right; left; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
          | (right; right; right; right; right; refine ⟨?_, ?_, ?_⟩ <;> first | rfl | (ext t; simp only [Pi.add_apply]; grind))
    · rintro ⟨r, g, rfl⟩
      exact mem_T.2 ⟨r, g, a r, b r, hab r, ha r, hb r, rfl⟩
  rw [hT, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_prod, card_vec]
  intro ⟨r, g⟩ ⟨r', g'⟩ h
  simp only [O] at h
  have hr : r = r' := by
    apply row_recover hH hker (hab r) (ha r) (hb r) (hab r') (ha r') (hb r') (x := 0)
    simpa using h
  subst hr
  have := congrArg (fun σ : Finset (Vec n) => ∑ y ∈ σ, y) h
  have hA := s_ne_zero hH hker (a r)
  have hB := s_ne_zero hH hker (b r)
  have hAB : s φ (a r) ≠ s φ (b r) := fun e => hab r (s_inj hH hker e)
  have hsum : ∀ g : Vec n, ∑ y ∈ ({g, g + s φ (a r), g + s φ (a r) + s φ (b r)} :
      Finset (Vec n)), y = g + s φ (b r) := by
    intro g
    have hc := card_tri hH hker (g := g) (hab r)
    rw [Finset.card_eq_three] at hc
    rw [Finset.sum_insert, Finset.sum_pair]
    · ext t; simp only [Pi.add_apply]; grind
    · intro e; apply hB; ext t; have := congrFun e t
      simp only [Pi.add_apply, Pi.zero_apply] at this ⊢; grind
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · intro e; apply hA; ext t; have := congrFun e t
        simp only [Pi.add_apply, Pi.zero_apply] at this ⊢; grind
      · intro e; apply hAB; ext t; have := congrFun e t
        simp only [Pi.add_apply, Pi.zero_apply] at this ⊢; grind
  simp only [hsum] at this
  rw [add_left_inj] at this
  rw [this]

end AbelianCayleyHDX.RelCx

open AbelianCayleyHDX AbelianCayleyHDX.RelCx in
theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] {n : ℕ}
    (H : Matrix ι κ (ZMod 2)) (ρ : ℕ) (hH : IsGoodRelationMatrix H ρ)
    (φ : (κ → ZMod 2) →ₗ[ZMod 2] Vec n) (hφ : Function.Surjective φ)
    (hker : LinearMap.ker φ = rowspan H) :
    (∀ τ ∈ relationComplex H φ,
      ((Finset.univ : Finset (Vec n)).image fun g => τ.image (· + g)).card = 2 ^ n) ∧
    (∀ (r r' : ι) (g g' x : Vec n) (i j i' j' : κ), i ≠ j → H r i ≠ 0 → H r j ≠ 0 →
      i' ≠ j' → H r' i' ≠ 0 → H r' j' ≠ 0 →
      ({g, g + φ (Pi.single i 1), g + φ (Pi.single i 1) + φ (Pi.single j 1)} : Finset (Vec n)).image
          (· + x) =
        ({g', g' + φ (Pi.single i' 1), g' + φ (Pi.single i' 1) + φ (Pi.single j' 1)} :
          Finset (Vec n)) → r = r') ∧
    (relationComplex H φ).card = Fintype.card ι * 2 ^ n := by
  refine ⟨?_, ?_, card_T hH hker⟩
  · intro τ hτ
    rw [Finset.card_image_of_injective _ (translate_inj τ (card_of_mem hH hker hτ)),
      Finset.card_univ, card_vec]
  · intro r r' g g' x i j i' j' hij hi hj hij' hi' hj' h
    exact row_recover hH hker hij (mem_supp.2 hi) (mem_supp.2 hj) hij' (mem_supp.2 hi')
      (mem_supp.2 hj') h
