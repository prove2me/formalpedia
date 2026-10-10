-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_differentiable_dedekindZeta_eq_mul_of_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T08:51:18.825116+00:00
-- url     : https://prove2.me/submissions/f8fd39f3-9b06-4e8d-9619-09aca361a1a8

import Mathlib
import Theorems.Thm_NumberField_dedekindZeta_ne_zero_of_one_lt_re
import Theorems.Thm_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
import Theorems.Thm_ArtinL_lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum
import Theorems.Thm_ArtinL_Abelian_exists_completedLSeries_functionalEquation_u0

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ABC

open scoped Classical

section Core

variable {A : Type*} [CommGroup A] [Fintype A]

/-- Sum of `ψ(a⁻¹)` over the generators `a` of the subgroup `E`. -/
noncomputable def genSum (ψ : AddChar (Additive A) ℂ) (E : Subgroup A) : ℂ :=
  ∑ a ∈ Finset.univ.filter (fun a : A => Subgroup.zpowers a = E), ψ (Additive.ofMul a⁻¹)

/-- `ψ(a⁻¹)` restricted to `E`, as a monoid hom into `ℂ`. -/
noncomputable def resInv (ψ : AddChar (Additive A) ℂ) (E : Subgroup A) : E →* ℂ where
  toFun a := ψ (Additive.ofMul (a : A)⁻¹)
  map_one' := by simp
  map_mul' a b := by
    simp only [Subgroup.coe_mul, mul_inv]
    rw [ofMul_mul, AddChar.map_add_eq_mul]

lemma genSum_mem (ψ : AddChar (Additive A) ℂ) :
    ∀ n : ℕ, ∀ E : Subgroup A, Nat.card E = n → genSum ψ E ∈ (Int.castRingHom ℂ).range := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E hE
  by_cases hex : ∃ a : A, Subgroup.zpowers a = E
  swap
  · have : genSum ψ E = 0 := by
      unfold genSum
      rw [Finset.sum_eq_zero]
      intro a ha
      exact absurd ⟨a, (Finset.mem_filter.1 ha).2⟩ hex
    rw [this]; exact Subring.zero_mem _
  set s : Finset A := Finset.univ.filter (fun a : A => a ∈ E) with hs
  set t : Finset (Subgroup A) := s.image Subgroup.zpowers with ht
  have hEt : E ∈ t := by
    obtain ⟨a, ha⟩ := hex
    exact Finset.mem_image.2 ⟨a, by simp [hs, ← ha, Subgroup.mem_zpowers], ha⟩
  -- the full sum over `E`
  have hfull : ∑ a ∈ s, ψ (Additive.ofMul a⁻¹) = ∑ E' ∈ t, genSum ψ E' := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := t) (g := Subgroup.zpowers)
      (fun a ha => Finset.mem_image_of_mem _ ha)]
    refine Finset.sum_congr rfl (fun E' hE' => ?_)
    unfold genSum
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hE'
    have hbE : b ∈ E := (Finset.mem_filter.1 hb).2
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      have : a ∈ Subgroup.zpowers a := Subgroup.mem_zpowers a
      rw [h] at this
      exact (Subgroup.zpowers_le.2 hbE) this
  have hint : ∑ a ∈ s, ψ (Additive.ofMul a⁻¹) ∈ (Int.castRingHom ℂ).range := by
    have h1 : ∑ a ∈ s, ψ (Additive.ofMul a⁻¹) = ∑ a : E, resInv ψ E a := by
      rw [Finset.sum_subtype s (p := fun a => a ∈ E) (by simp [hs])]
      rfl
    rw [h1, sum_hom_units]
    split_ifs
    · exact ⟨(Fintype.card E : ℤ), by simp⟩
    · exact ⟨0, by simp⟩
  rw [hfull, ← Finset.add_sum_erase t _ hEt] at hint
  have hrest : ∑ E' ∈ t.erase E, genSum ψ E' ∈ (Int.castRingHom ℂ).range := by
    refine Subring.sum_mem _ (fun E' hE' => ?_)
    obtain ⟨hne, hE't⟩ := Finset.mem_erase.1 hE'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hE't
    have hle : Subgroup.zpowers b ≤ E := Subgroup.zpowers_le.2 (Finset.mem_filter.1 hb).2
    have hlt : Nat.card (Subgroup.zpowers b) < n := by
      rw [← hE]
      refine lt_of_le_of_ne (Subgroup.card_le_of_le hle) (fun h => hne ?_)
      exact Subgroup.eq_of_le_of_card_ge hle h.ge
    exact ih _ hlt _ rfl
  simpa using Subring.sub_mem _ hint hrest

/-- Number of generators of `A`. -/
noncomputable def phi (A : Type*) [Group A] [Fintype A] : ℕ :=
  (Finset.univ.filter (fun a : A => Subgroup.zpowers a = ⊤)).card

lemma genSum_top_exists (ψ : AddChar (Additive A) ℂ) :
    ∃ z : ℤ, z ≤ phi A ∧ genSum ψ ⊤ = z := by
  obtain ⟨z, hz⟩ := genSum_mem ψ _ ⊤ rfl
  refine ⟨z, ?_, by simpa using hz.symm⟩
  have hn : ‖genSum ψ ⊤‖ ≤ phi A := by
    unfold genSum phi
    refine (norm_sum_le _ _).trans ?_
    simp
  have : ‖genSum ψ ⊤‖ = |(z : ℝ)| := by
    rw [← hz]; simp [Complex.norm_intCast]
  rw [this] at hn
  exact_mod_cast (le_abs_self (z : ℝ)).trans hn

/-- The (natural) multiplicity `φ(A) − Σ_{a gen} ψ(a⁻¹)`. -/
noncomputable def mcoef (ψ : AddChar (Additive A) ℂ) : ℕ :=
  ((phi A : ℤ) - (genSum_top_exists ψ).choose).toNat

lemma mcoef_cast (ψ : AddChar (Additive A) ℂ) :
    (mcoef ψ : ℂ) = phi A - genSum ψ ⊤ := by
  obtain ⟨h1, h2⟩ := (genSum_top_exists ψ).choose_spec
  unfold mcoef
  generalize (genSum_top_exists ψ).choose = z at h1 h2 ⊢
  have h3 := Int.toNat_of_nonneg (sub_nonneg.2 h1)
  have : ((((phi A : ℤ) - z).toNat : ℤ) : ℂ) = (((phi A : ℤ) - z : ℤ) : ℂ) := by rw [h3]
  rw [h2]
  push_cast at this
  exact this

lemma mcoef_one : mcoef (1 : AddChar (Additive A) ℂ) = 0 := by
  have h := mcoef_cast (1 : AddChar (Additive A) ℂ)
  have : genSum (1 : AddChar (Additive A) ℂ) ⊤ = phi A := by
    unfold genSum phi; simp
  rw [this, sub_self] at h
  exact_mod_cast h

lemma sum_mcoef_mul (u : A) :
    ∑ ψ : AddChar (Additive A) ℂ, (mcoef ψ : ℂ) * ψ (Additive.ofMul u) =
      (phi A : ℂ) * (if u = 1 then (Fintype.card A : ℂ) else 0) -
        (if Subgroup.zpowers u = ⊤ then (Fintype.card A : ℂ) else 0) := by
  simp_rw [mcoef_cast, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  · rw [AddChar.sum_apply_eq_ite]
    simp [Fintype.card_congr Additive.toMul]
  · unfold genSum
    simp_rw [Finset.sum_mul, ← AddChar.map_add_eq_mul]
    rw [Finset.sum_comm]
    simp_rw [← ofMul_mul, AddChar.sum_apply_eq_ite]
    simp only [ofMul_eq_zero, inv_mul_eq_one]
    rw [Finset.sum_ite_eq']
    simp [Fintype.card_congr Additive.toMul]

end Core

section QLevel

variable {Q : Type*} [Group Q] [Fintype Q]

lemma zpowers_eq_top_iff (C : Subgroup Q) (a : C) :
    Subgroup.zpowers a = ⊤ ↔ Subgroup.zpowers (a : Q) = C := by
  constructor
  · intro h
    refine le_antisymm (Subgroup.zpowers_le.2 a.2) (fun b hb => ?_)
    have : (⟨b, hb⟩ : C) ∈ Subgroup.zpowers a := h ▸ Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 this
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  · intro h
    refine eq_top_iff.2 (fun b _ => ?_)
    have : (b : Q) ∈ Subgroup.zpowers (a : Q) := by rw [h]; exact b.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 this
    exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩

lemma phi_eq (C : Subgroup Q) :
    phi C = (Finset.univ.filter (fun a : Q => Subgroup.zpowers a = C)).card := by
  unfold phi
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext b
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact (zpowers_eq_top_iff C a).1 ha
  · intro hb
    have hbC : b ∈ C := hb ▸ Subgroup.mem_zpowers b
    exact ⟨⟨b, hbC⟩, (zpowers_eq_top_iff C ⟨b, hbC⟩).2 hb, rfl⟩

/-- A chosen generator of a cyclic subgroup. -/
noncomputable def rep (C : Subgroup Q) : Q :=
  if h : ∃ q : Q, Subgroup.zpowers q = C then h.choose else 1

lemma zpowers_rep (q : Q) : Subgroup.zpowers (rep (Subgroup.zpowers q)) = Subgroup.zpowers q := by
  have h : ∃ q' : Q, Subgroup.zpowers q' = Subgroup.zpowers q := ⟨q, rfl⟩
  unfold rep; rw [dif_pos h]; exact h.choose_spec

/-- The chosen generators, one per cyclic subgroup. -/
noncomputable def reps (Q : Type*) [Group Q] [Fintype Q] : Finset Q :=
  (Finset.univ.image (fun q : Q => Subgroup.zpowers q)).image rep

lemma sum_reps {M : Type*} [AddCommMonoid M] (F : Subgroup Q → M) :
    ∑ q ∈ reps Q, F (Subgroup.zpowers q) =
      ∑ C ∈ Finset.univ.image (fun q : Q => Subgroup.zpowers q), F C := by
  unfold reps
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl (fun C hC => ?_)
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hC
    rw [zpowers_rep]
  · intro C hC D hD hCD
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hC
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hD
    have := congrArg Subgroup.zpowers hCD
    rwa [zpowers_rep, zpowers_rep] at this

open IsMulCommutative in
lemma q_identity (u : Q) :
    ∑ q ∈ reps Q, ∑ ψ : AddChar (Additive (Subgroup.zpowers q)) ℂ,
      (mcoef ψ : ℂ) * ((Nat.card (Subgroup.zpowers q) : ℂ)⁻¹ *
        (if hu : u ∈ Subgroup.zpowers q then ψ (Additive.ofMul ⟨u, hu⟩) else 0)) =
      (Fintype.card Q : ℂ) * (if u = 1 then 1 else 0) - 1 := by
  have hstep : ∀ q : Q, ∑ ψ : AddChar (Additive (Subgroup.zpowers q)) ℂ,
      (mcoef ψ : ℂ) * ((Nat.card (Subgroup.zpowers q) : ℂ)⁻¹ *
        (if hu : u ∈ Subgroup.zpowers q then ψ (Additive.ofMul ⟨u, hu⟩) else 0)) =
      (phi (Subgroup.zpowers q) : ℂ) * (if u = 1 then 1 else 0) -
        (if Subgroup.zpowers u = Subgroup.zpowers q then 1 else 0) := by
    intro q
    have hc : (Nat.card (Subgroup.zpowers q) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := Subgroup.zpowers q)).ne'
    by_cases hu : u ∈ Subgroup.zpowers q
    · simp_rw [dif_pos hu]
      simp_rw [mul_left_comm (mcoef _ : ℂ), ← Finset.mul_sum]
      rw [sum_mcoef_mul (A := Subgroup.zpowers q) (⟨u, hu⟩ : Subgroup.zpowers q), ← Nat.card_eq_fintype_card]
      have h1 : ((⟨u, hu⟩ : Subgroup.zpowers q) = 1) ↔ u = 1 := by
        simp [Subtype.ext_iff]
      rw [zpowers_eq_top_iff]
      simp only [h1]
      split_ifs <;> field_simp <;> ring
    · simp_rw [dif_neg hu, mul_zero, Finset.sum_const_zero]
      have h1 : u ≠ 1 := fun h => hu (h ▸ Subgroup.one_mem _)
      have h2 : Subgroup.zpowers u ≠ Subgroup.zpowers q :=
        fun h => hu (h ▸ Subgroup.mem_zpowers u)
      simp [h1, h2]
  simp_rw [hstep]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [sum_reps (fun C => (phi C : ℂ)), sum_reps (fun C => if Subgroup.zpowers u = C then (1 : ℂ) else 0)]
  rw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_image_of_mem _ (Finset.mem_univ u))]
  congr 2
  simp_rw [phi_eq]
  rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_image]
  simp

end QLevel

section Lift

/-- An additive character of `Additive C` as a multiplicative character `C →* ℂˣ`. -/
noncomputable def charOf {C : Type*} [Group C] (ψ : AddChar (Additive C) ℂ) : C →* ℂˣ where
  toFun c := ⟨ψ (Additive.ofMul c), ψ (Additive.ofMul c⁻¹),
    by rw [← AddChar.map_add_eq_mul, ← ofMul_mul, mul_inv_cancel]; simp,
    by rw [← AddChar.map_add_eq_mul, ← ofMul_mul, inv_mul_cancel]; simp⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [ofMul_mul, AddChar.map_add_eq_mul]

variable {G : Type*} [Group G] [Fintype G] (H K : Subgroup G) [(H.subgroupOf K).Normal]

local notation "Qt" => K ⧸ H.subgroupOf K
local notation "π" => QuotientGroup.mk' (H.subgroupOf K)

/-- Preimage in `K` (as a subgroup of `G`) of a cyclic subgroup of `K/H`. -/
noncomputable def Jsub (q : Qt) : Subgroup G :=
  ((Subgroup.zpowers q).comap π).map K.subtype

lemma mem_Jsub_iff (q : Qt) (y : G) :
    y ∈ Jsub H K q ↔ ∃ hk : y ∈ K, π ⟨y, hk⟩ ∈ Subgroup.zpowers q := by
  unfold Jsub
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x.2, hx⟩
  · rintro ⟨hk, h⟩; exact ⟨⟨y, hk⟩, h, rfl⟩

lemma memK {q : Qt} {y : G} (hy : y ∈ Jsub H K q) : y ∈ K :=
  ((mem_Jsub_iff H K q y).1 hy).1

lemma memC {q : Qt} {y : G} (hy : y ∈ Jsub H K q) :
    π ⟨y, memK H K hy⟩ ∈ Subgroup.zpowers q :=
  ((mem_Jsub_iff H K q y).1 hy).2

/-- The pulled-back character on `Jsub q`. -/
noncomputable def chiOf (q : Qt) (ψ : AddChar (Additive (Subgroup.zpowers q)) ℂ) :
    Jsub H K q →* ℂˣ where
  toFun y := charOf ψ ⟨π ⟨y.1, memK H K y.2⟩, memC H K y.2⟩
  map_one' := by
    rw [← map_one (charOf ψ)]; congr 1
  map_mul' a b := by
    rw [← map_mul (charOf ψ)]; congr 1

lemma chiOf_dite (q : Qt) (ψ : AddChar (Additive (Subgroup.zpowers q)) ℂ) (y : G) :
    (if hy : y ∈ Jsub H K q then ((chiOf H K q ψ ⟨y, hy⟩ : ℂˣ) : ℂ) else 0) =
      if hk : y ∈ K then
        (if hu : π ⟨y, hk⟩ ∈ Subgroup.zpowers q then ψ (Additive.ofMul ⟨π ⟨y, hk⟩, hu⟩) else 0)
      else 0 := by
  by_cases hy : y ∈ Jsub H K q
  · rw [dif_pos hy, dif_pos (memK H K hy), dif_pos (memC H K hy)]; rfl
  · rw [dif_neg hy]
    split_ifs with hk hu
    · exact absurd ((mem_Jsub_iff H K q y).2 ⟨hk, hu⟩) hy
    · rfl
    · rfl

lemma chiOf_ne_one (q : Qt) (ψ : AddChar (Additive (Subgroup.zpowers q)) ℂ) (hψ : ψ ≠ 1) :
    chiOf H K q ψ ≠ 1 := by
  obtain ⟨c, hc⟩ := AddChar.ne_one_iff.1 hψ
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (H.subgroupOf K) (Additive.toMul c).1
  have hy : (k : G) ∈ Jsub H K q :=
    (mem_Jsub_iff H K q k).2 ⟨k.2, by rw [show (⟨(k : G), k.2⟩ : K) = k from rfl, hk]; exact (Additive.toMul c).2⟩
  intro h
  have := congrArg (fun f : Jsub H K q →* ℂˣ => ((f ⟨k, hy⟩ : ℂˣ) : ℂ)) h
  simp only [MonoidHom.one_apply, Units.val_one] at this
  apply hc
  rw [← this]
  change ψ c = ψ (Additive.ofMul ⟨π ⟨(k : G), _⟩, _⟩)
  congr 1
  apply Additive.toMul.injective
  apply Subtype.ext
  change _ = π k
  rw [hk]

lemma card_Jsub (hHK : H ≤ K) (q : Qt) :
    Nat.card (Jsub H K q) = Nat.card H * Nat.card (Subgroup.zpowers q) := by
  unfold Jsub
  rw [Subgroup.card_map_of_injective K.subtype_injective]
  have h1 := Subgroup.card_mul_index ((Subgroup.zpowers q).comap π)
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
  have h2 := Subgroup.card_mul_index (Subgroup.zpowers q)
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (H.subgroupOf K)
  have h4 : Nat.card (H.subgroupOf K) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv
  have hi : 0 < (Subgroup.zpowers q).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [h4, ← h2] at h3
  rw [h3] at h1
  have : Nat.card ((Subgroup.zpowers q).comap π) * (Subgroup.zpowers q).index =
      (Nat.card H * Nat.card (Subgroup.zpowers q)) * (Subgroup.zpowers q).index := by
    rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_right hi this

open IsMulCommutative in
lemma pointwise (hHK : H ≤ K) (y : G) :
    (Nat.card Qt : ℂ) * ((Nat.card H : ℂ)⁻¹ * (if y ∈ H then 1 else 0)) =
      (Nat.card Qt : ℂ) * ((Nat.card K : ℂ)⁻¹ * (if y ∈ K then 1 else 0)) +
      ∑ q ∈ reps Qt, ∑ ψ : AddChar (Additive (Subgroup.zpowers q)) ℂ,
        (mcoef ψ : ℂ) * ((Nat.card (Jsub H K q) : ℂ)⁻¹ *
          (if hy : y ∈ Jsub H K q then ((chiOf H K q ψ ⟨y, hy⟩ : ℂˣ) : ℂ) else 0)) := by
  have h4 : Nat.card (H.subgroupOf K) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv
  have hK : (Nat.card K : ℂ) = Nat.card Qt * Nat.card H := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (H.subgroupOf K), h4]; push_cast; rfl
  have hH0 : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  have hQ0 : (Nat.card Qt : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := Qt)).ne'
  simp_rw [chiOf_dite, card_Jsub H K hHK]
  by_cases hk : y ∈ K
  · simp_rw [dif_pos hk]
    have hsum : ∀ q : Qt, ∑ ψ : AddChar (Additive (Subgroup.zpowers q)) ℂ,
        (mcoef ψ : ℂ) * (((Nat.card H * Nat.card (Subgroup.zpowers q) : ℕ) : ℂ)⁻¹ *
          (if hu : π ⟨y, hk⟩ ∈ Subgroup.zpowers q then
            ψ (Additive.ofMul ⟨π ⟨y, hk⟩, hu⟩) else 0)) =
        (Nat.card H : ℂ)⁻¹ * ∑ ψ : AddChar (Additive (Subgroup.zpowers q)) ℂ,
        (mcoef ψ : ℂ) * ((Nat.card (Subgroup.zpowers q) : ℂ)⁻¹ *
          (if hu : π ⟨y, hk⟩ ∈ Subgroup.zpowers q then
            ψ (Additive.ofMul ⟨π ⟨y, hk⟩, hu⟩) else 0)) := by
      intro q
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ψ _ => ?_)
      push_cast
      rw [mul_inv]; ring
    simp_rw [hsum]
    rw [← Finset.mul_sum, q_identity, ← Nat.card_eq_fintype_card]
    have hHu : y ∈ H ↔ π ⟨y, hk⟩ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rw [hK, if_pos hk]
    by_cases hy : y ∈ H
    · rw [if_pos hy, if_pos (hHu.1 hy)]; field_simp; ring
    · rw [if_neg hy, if_neg (fun h => hy (hHu.2 h))]; field_simp; ring
  · have hy : y ∉ H := fun h => hk (hHK h)
    simp [hk, hy]

open IsMulCommutative in
theorem aramataBrauer_identity {G : Type*} [Group G] [Fintype G]
    (H K : Subgroup G) (hHK : H ≤ K) (hN : (H.subgroupOf K).Normal) :
    ∃ N : ℕ, 0 < N ∧ ∃ (k : ℕ) (J : Fin k → Subgroup G) (χ : (i : Fin k) → (J i →* ℂˣ))
      (m : Fin k → ℕ), (∀ i, χ i ≠ 1) ∧ ∀ g : G,
        (N : ℂ) * ((Nat.card H : ℂ)⁻¹ * ∑ x : G,
            if hx : x⁻¹ * g * x ∈ H then (((1 : H →* ℂˣ) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0) =
          (N : ℂ) * ((Nat.card K : ℂ)⁻¹ * ∑ x : G,
            if hx : x⁻¹ * g * x ∈ K then (((1 : K →* ℂˣ) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0) +
          ∑ i, (m i : ℂ) * ((Nat.card (J i) : ℂ)⁻¹ * ∑ x : G,
            if hx : x⁻¹ * g * x ∈ J i then (((χ i) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0) := by
  let ι := Σ q : reps (K ⧸ H.subgroupOf K), AddChar (Additive (Subgroup.zpowers q.1)) ℂ
  let ι' := {p : ι // p.2 ≠ 1}
  let e : Fin (Fintype.card ι') ≃ ι' := (Fintype.equivFin ι').symm
  refine ⟨Nat.card (K ⧸ H.subgroupOf K), Nat.card_pos, Fintype.card ι',
    fun i => Jsub H K (e i).1.1.1, fun i => chiOf H K (e i).1.1.1 (e i).1.2,
    fun i => mcoef (e i).1.2, fun i => chiOf_ne_one H K _ _ (e i).2, fun g => ?_⟩
  -- reindex the character sum
  have hre : ∀ f : (q : K ⧸ H.subgroupOf K) → AddChar (Additive (Subgroup.zpowers q)) ℂ → ℂ,
      (∀ q, f q 1 = 0) →
      ∑ i : Fin (Fintype.card ι'), f (e i).1.1.1 (e i).1.2 =
        ∑ q ∈ reps (K ⧸ H.subgroupOf K),
          ∑ ψ : AddChar (Additive (Subgroup.zpowers q)) ℂ, f q ψ := by
    intro f hf
    rw [Equiv.sum_comp e (fun p : ι' => f p.1.1.1 p.1.2)]
    rw [← Finset.sum_coe_sort (reps (K ⧸ H.subgroupOf K))
      (fun q => ∑ ψ : AddChar (Additive (Subgroup.zpowers q)) ℂ, f q ψ)]
    rw [← Fintype.sum_sigma (fun p : ι => f p.1.1 p.2)]
    rw [← Finset.sum_filter_of_ne (s := Finset.univ) (p := fun p : ι => p.2 ≠ 1)
      (fun p _ h hp => h (by rw [hp]; exact hf _))]
    exact (Finset.sum_subtype _ (fun p => by simp) (fun p : ι => f p.1.1 p.2)).symm
  simp only [MonoidHom.one_apply, Units.val_one, dite_eq_ite]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have := pointwise H K hHK (x⁻¹ * g * x)
  rw [hre (fun q ψ => (mcoef ψ : ℂ) * ((Nat.card (Jsub H K q) : ℂ)⁻¹ *
      (if hy : x⁻¹ * g * x ∈ Jsub H K q then
        ((chiOf H K q ψ ⟨x⁻¹ * g * x, hy⟩ : ℂˣ) : ℂ) else 0)))
    (fun q => by simp [mcoef_one])]
  exact this

end Lift

section PermRep

end PermRep

end ABC
end

section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open Filter Topology

namespace ABR

/-- Arithmetic in `WithTop ℤ`: from `N * a = N * b + e` with `e ≥ 0`, `b` finite, `N > 0`,
we get `0 ≤ a - b`. -/
lemma withTop_sub_nonneg {a b e : WithTop ℤ} {N : ℕ} (hN : 0 < N) (hb : b ≠ ⊤) (he : 0 ≤ e)
    (h : (N : WithTop ℤ) * a = (N : WithTop ℤ) * b + e) : 0 ≤ a - b := by
  induction b using WithTop.recTopCoe with
  | top => exact absurd rfl hb
  | coe b =>
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe a =>
  induction e using WithTop.recTopCoe with
  | top =>
    exfalso
    rw [WithTop.add_top,
      show ((N : WithTop ℤ) * (a : WithTop ℤ)) = ((N * a : ℤ) : WithTop ℤ) by norm_cast] at h
    exact WithTop.coe_ne_top h
  | coe e =>
    have h' : ((N * a : ℤ) : WithTop ℤ) = ((N * b + e : ℤ) : WithTop ℤ) := by
      push_cast; exact h
    have h'' : (N : ℤ) * a = N * b + e := WithTop.coe_injective h'
    have he' : (0 : ℤ) ≤ e := by exact_mod_cast he
    have hN' : (0 : ℤ) < N := by exact_mod_cast hN
    have hba : b ≤ a := by
      by_contra hc
      push Not at hc
      have : (N : ℤ) * a < N * b := mul_lt_mul_of_pos_left hc hN'
      linarith
    have : ((a : WithTop ℤ) - (b : WithTop ℤ)) = ((a - b : ℤ) : WithTop ℤ) := by norm_cast
    rw [this]
    exact_mod_cast sub_nonneg.mpr hba

theorem exists_differentiable_eq_mul_of_pow_eq_pow_mul
    {A B E : ℂ → ℂ} {N : ℕ} (hN : 0 < N)
    (hA : Differentiable ℂ A) (hB : Differentiable ℂ B) (hE : Differentiable ℂ E)
    (hB0 : ∃ z, B z ≠ 0) {U : Set ℂ} (hUo : IsOpen U) (hUn : U.Nonempty)
    (hEq : ∀ z ∈ U, A z ^ N = B z ^ N * E z) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ ∀ z, A z = B z * h z := by
  have hAa : AnalyticOnNhd ℂ A Set.univ := fun z _ => hA.analyticAt z
  have hBa : AnalyticOnNhd ℂ B Set.univ := fun z _ => hB.analyticAt z
  have hEa : AnalyticOnNhd ℂ E Set.univ := fun z _ => hE.analyticAt z
  -- Step 1: the identity holds everywhere.
  obtain ⟨u, hu⟩ := hUn
  have hglob : (fun z => A z ^ N) = fun z => B z ^ N * E z := by
    apply AnalyticOnNhd.eq_of_eventuallyEq (𝕜 := ℂ) (z₀ := u)
    · exact fun z _ => (hAa z trivial).pow N
    · exact fun z _ => ((hBa z trivial).pow N).mul (hEa z trivial)
    · filter_upwards [hUo.mem_nhds hu] with z hz using hEq z hz
  -- Step 2: orders.
  obtain ⟨z₁, hz₁⟩ := hB0
  have hBfin : ∀ z, meromorphicOrderAt B z ≠ ⊤ := by
    have hmB : Meromorphic B := fun z => (hBa z trivial).meromorphicAt
    refine (hmB.exists_meromorphicOrderAt_ne_top_iff_forall).1 ⟨z₁, ?_⟩
    rw [(hBa z₁ trivial).meromorphicOrderAt_eq,
      (hBa z₁ trivial).analyticOrderAt_eq_zero.2 hz₁]
    simp
  set f : ℂ → ℂ := A / B with hf
  have hfm : MeromorphicOn f Set.univ := fun z _ =>
    (hAa z trivial).meromorphicAt.div (hBa z trivial).meromorphicAt
  have hord : ∀ z, 0 ≤ meromorphicOrderAt f z := by
    intro z
    have hAm := (hAa z trivial).meromorphicAt
    have hBm := (hBa z trivial).meromorphicAt
    have hEm := (hEa z trivial).meromorphicAt
    rw [hf, meromorphicOrderAt_div hAm hBm]
    have key := congrArg (fun F => meromorphicOrderAt F z) hglob
    have e1 : meromorphicOrderAt (fun z => A z ^ N) z = N * meromorphicOrderAt A z :=
      meromorphicOrderAt_pow hAm
    have e2 : meromorphicOrderAt (fun z => B z ^ N * E z) z
        = N * meromorphicOrderAt B z + meromorphicOrderAt E z := by
      rw [show (fun z => B z ^ N * E z) = B ^ N * E from rfl,
        meromorphicOrderAt_mul (hBm.pow N) hEm, meromorphicOrderAt_pow hBm]
    rw [e1, e2] at key
    have hE0 : 0 ≤ meromorphicOrderAt E z := by
      rw [(hEa z trivial).meromorphicOrderAt_eq]
      cases analyticOrderAt E z <;> simp
    exact withTop_sub_nonneg hN (hBfin z) hE0 key
  -- Step 3: the normal form of f is entire.
  set h := toMeromorphicNFOn f Set.univ with hh
  have hNF : MeromorphicNFOn h Set.univ := meromorphicNFOn_toMeromorphicNFOn f Set.univ
  have han : ∀ z, AnalyticAt ℂ h z := by
    intro z
    rw [← (hNF (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt,
      hh, meromorphicOrderAt_toMeromorphicNFOn hfm (Set.mem_univ z)]
    exact hord z
  refine ⟨h, fun z => (han z).differentiableAt, ?_⟩
  -- Step 4: A = B * h near z₁, hence everywhere.
  have hfa : AnalyticAt ℂ f z₁ := (hAa z₁ trivial).div (hBa z₁ trivial) hz₁
  have hloc : h =ᶠ[𝓝 z₁] f := by
    have := toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hfm (Set.mem_univ z₁)
    rwa [toMeromorphicNFAt_eq_self.2 hfa.meromorphicNFAt] at this
  have hBne : ∀ᶠ z in 𝓝 z₁, B z ≠ 0 :=
    (hB z₁).continuousAt.eventually_ne hz₁
  have hfun : A = fun z => B z * h z := by
    apply AnalyticOnNhd.eq_of_eventuallyEq (𝕜 := ℂ) (z₀ := z₁) hAa
    · exact fun z _ => (hBa z trivial).mul (han z)
    · filter_upwards [hloc, hBne] with z hz hz'
      rw [hz, hf, Pi.div_apply, mul_div_cancel₀ _ hz']
  exact fun z => congrFun hfun z

theorem exists_differentiable_eq_mul_of_pow_eq_pow_mul_of_one_lt_re
    {f g E F G : ℂ → ℂ} {N : ℕ} (hN : 0 < N)
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (hE : Differentiable ℂ E)
    (hFf : ∀ s : ℂ, 1 < s.re → F s = (s - 1) * f s)
    (hGg : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * g s)
    (hg : ∃ s : ℂ, 1 < s.re ∧ g s ≠ 0)
    (hEq : ∀ s : ℂ, 1 < s.re → f s ^ N = g s ^ N * E s) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ ∀ s : ℂ, 1 < s.re → f s = g s * h s := by
  have hne : ∀ s : ℂ, 1 < s.re → s - 1 ≠ 0 := by
    intro s hs h0
    have : s = 1 := sub_eq_zero.mp h0
    rw [this] at hs; simp at hs
  obtain ⟨s₀, hs₀, hgs₀⟩ := hg
  have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  obtain ⟨h, hhd, hh⟩ := exists_differentiable_eq_mul_of_pow_eq_pow_mul hN hF hG hE
    ⟨s₀, by rw [hGg s₀ hs₀]; exact mul_ne_zero (hne s₀ hs₀) hgs₀⟩ hU ⟨s₀, hs₀⟩
    (fun s hs => by
      rw [hFf s hs, hGg s hs, mul_pow, mul_pow, hEq s hs, mul_assoc])
  refine ⟨h, hhd, fun s hs => ?_⟩
  have := hh s
  rw [hFf s hs, hGg s hs, mul_assoc] at this
  exact mul_left_cancel₀ (hne s hs) this

end ABR

end

section
namespace ABR

theorem exists_differentiable_dedekindZeta_eq_mul_of_pow_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    {N : ℕ} (hN : 0 < N) {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hEq : ∀ s : ℂ, 1 < s.re →
      NumberField.dedekindZeta L s ^ N = NumberField.dedekindZeta K s ^ N * E s) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧
      ∀ s : ℂ, 1 < s.re → NumberField.dedekindZeta L s = NumberField.dedekindZeta K s * h s := by
  obtain ⟨RL, hRL, -, hRLeq, -⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero L
  obtain ⟨RK, hRK, -, hRKeq, -⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero K
  exact exists_differentiable_eq_mul_of_pow_eq_pow_mul_of_one_lt_re hN hRL hRK hE hRLeq hRKeq
    ⟨2, by norm_num, NumberField.dedekindZeta_ne_zero_of_one_lt_re K (by norm_num)⟩ hEq

end ABR

end

section
set_option autoImplicit false
set_option linter.style.haveILetI false

open NumberField

namespace ABA

theorem card_absNorm_eq_congr {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] (e : K₁ ≃+* K₂) (n : ℕ) :
    Nat.card {I : Ideal (𝓞 K₁) // Ideal.absNorm I = n} =
      Nat.card {I : Ideal (𝓞 K₂) // Ideal.absNorm I = n} := by
  set f : 𝓞 K₁ ≃+* 𝓞 K₂ := RingOfIntegers.mapRingEquiv e
  have hnorm : ∀ I : Ideal (𝓞 K₁), Ideal.absNorm (I.map f) = Ideal.absNorm I := by
    intro I
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv I (I.map f) f rfl).toEquiv).symm
  have h1 : ∀ I : Ideal (𝓞 K₁), (I.map f).map f.symm = I := fun I => Ideal.map_of_equiv f
  have h2 : ∀ J : Ideal (𝓞 K₂), (J.map f.symm).map f = J := fun J => by
    have := Ideal.map_of_equiv (I := J) f.symm; rwa [RingEquiv.symm_symm] at this
  refine Nat.card_congr
    { toFun := fun I => ⟨I.1.map f, by rw [hnorm]; exact I.2⟩
      invFun := fun J => ⟨J.1.map f.symm, by rw [← hnorm, h2]; exact J.2⟩
      left_inv := fun I => Subtype.ext (h1 I.1)
      right_inv := fun J => Subtype.ext (h2 J.1) }

theorem dedekindZeta_congr {K₁ K₂ : Type*} [Field K₁] [NumberField K₁] [Field K₂]
    [NumberField K₂] (e : K₁ ≃+* K₂) : dedekindZeta K₁ = dedekindZeta K₂ := by
  funext s
  unfold dedekindZeta
  congr 1
  funext n
  rw [card_absNorm_eq_congr e n]


/-- `ℚ̄` is an algebraic closure of `ℚ` for the `ℚ`-algebra structure that elaboration picks
(`DivisionRing.toRatAlgebra`). -/
theorem isAlgClosure_rat : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  have h : (AlgebraicClosure.instAlgebra ℚ (R := ℚ)) = DivisionRing.toRatAlgebra :=
    Subsingleton.elim _ _
  have i : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  rw [h] at i
  exact ⟨inferInstance, i⟩

/-- A3 (Aramata–Brauer for subfields of `ℚ̄`), as used by the transport. -/
def A3Statement : Prop :=
  ∀ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (H K : Subgroup (F ≃ₐ[ℚ] F)), H ≤ K → (∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H) →
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ∀ s : ℂ, 1 < s.re →
      dedekindZeta (IntermediateField.fixedField H) s =
        dedekindZeta (IntermediateField.fixedField K) s * f s

/-- If `M/ℚ` is finite Galois and `ψ : L →ₐ[ℚ] M`, then `ζ` of the fixed field of the fixing
subgroup of `ψ(L)` is `ζ_L`. -/
theorem dedekindZeta_fixedField_fixingSubgroup_fieldRange {L M : Type} [Field L] [NumberField L]
    [Field M] [NumberField M] [IsGalois ℚ M] (ψ : L →ₐ[ℚ] M) :
    dedekindZeta (IntermediateField.fixedField ψ.fieldRange.fixingSubgroup) =
      dedekindZeta L := by
  have h := IsGalois.fixedField_fixingSubgroup ψ.fieldRange
  rw [dedekindZeta_congr (IntermediateField.equivOfEq h).toRingEquiv]
  exact (dedekindZeta_congr (AlgEquiv.ofInjectiveField ψ).toRingEquiv).symm

theorem of_A3 (hA3 : A3Statement) (K L : Type) [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧
      ∀ s : ℂ, 1 < s.re → dedekindZeta L s = dedekindZeta K s * h s := by
  let φ : L →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)
  haveI : NumberField M := ⟨⟩
  haveI := isAlgClosure_rat
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ _
  haveI : IsGalois ℚ M := IsGalois.normalClosure ℚ L (AlgebraicClosure ℚ)
  let ψ : L →ₐ[ℚ] M := φ.codRestrict M.toSubalgebra
    (fun x => φ.fieldRange_le_normalClosure ⟨x, rfl⟩)
  let ψK : K →ₐ[ℚ] M := ψ.comp (IsScalarTower.toAlgHom ℚ K L)
  set HL := ψ.fieldRange.fixingSubgroup with hHL
  set HK := ψK.fieldRange.fixingSubgroup with hHK
  have hle : HL ≤ HK := by
    apply IntermediateField.fixingSubgroup_antitone
    rintro _ ⟨x, rfl⟩
    exact ⟨algebraMap K L x, rfl⟩
  have hnormal : ∀ k ∈ HK, ∀ h ∈ HL, k * h * k⁻¹ ∈ HL := by
    intro k hk h hh
    have hk' : k⁻¹ ∈ HK := HK.inv_mem hk
    have hmap : ∀ y : L, ∃ y' : L, k⁻¹ (ψ y) = ψ y' := by
      intro y
      letI : Algebra K M := (ψK : K →+* M).toAlgebra
      letI : Algebra L M := (ψ : L →+* M).toAlgebra
      haveI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      let ϕ : M →ₐ[K] M :=
        { (k⁻¹ : M ≃ₐ[ℚ] M).toRingEquiv.toRingHom with
          commutes' := fun x =>
            (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk' _ ⟨x, rfl⟩ }
      exact ⟨ϕ.restrictNormal L y, (ϕ.restrictNormal_commutes L y).symm⟩
    rw [hHL, IntermediateField.mem_fixingSubgroup_iff]
    rintro _ ⟨y, rfl⟩
    obtain ⟨y', hy'⟩ := hmap y
    have hfix : h (ψ y') = ψ y' :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh _ ⟨y', rfl⟩
    change k (h (k⁻¹ (ψ y))) = ψ y
    rw [hy', hfix, ← hy', ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  obtain ⟨f, hf, hEq⟩ := hA3 M HL HK hle hnormal
  refine ⟨f, hf, fun s hs => ?_⟩
  have := hEq s hs
  rwa [hHL, hHK, dedekindZeta_fixedField_fixingSubgroup_fieldRange,
    dedekindZeta_fixedField_fixingSubgroup_fieldRange] at this

end ABA
end

section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.style.haveILetI false

open NumberField

namespace ABA

/-- Dividing a completed L-function by its Γ and conductor factors: if `Λ` is entire and equals
`c^{s/2} Γℝ(s)^a Γℝ(s+1)^b Γℂ(s)^r L(s)` on `Re s > 1` with `c > 0`, then `L` agrees with an
entire function on `Re s > 1`. -/
theorem exists_entire_of_completed {L Λ : ℂ → ℂ} (c : ℝ) (hc : 0 < c) (a b r : ℕ)
    (hΛ : Differentiable ℂ Λ)
    (h : ∀ s : ℂ, 1 < s.re → Λ s = ((c : ℝ) : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ a *
      Complex.Gammaℝ (s + 1) ^ b * Complex.Gammaℂ s ^ r * L s) :
    ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ ∀ s : ℂ, 1 < s.re → L s = E s := by
  have hc0 : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨fun s => Λ s * ((c : ℝ) : ℂ) ^ (-(s / 2)) * (Complex.Gammaℝ s)⁻¹ ^ a *
      (Complex.Gammaℝ (s + 1))⁻¹ ^ b * (Complex.Gammaℂ s)⁻¹ ^ r, ?_, ?_⟩
  · have h1 : Differentiable ℂ fun s : ℂ => ((c : ℝ) : ℂ) ^ (-(s / 2)) :=
      fun s => ((differentiableAt_id.div_const 2).neg).const_cpow (Or.inl hc0)
    have h2 := Complex.differentiable_Gammaℝ_inv
    have h3 : Differentiable ℂ fun s : ℂ => (Complex.Gammaℝ (s + 1))⁻¹ :=
      h2.comp (differentiable_id.add_const 1)
    have h4 := Complex.differentiable_Gammaℂ_inv
    exact ((((hΛ.mul h1).mul (h2.pow a)).mul (h3.pow b)).mul (h4.pow r))
  · intro s hs
    have hs0 : 0 < s.re := by linarith
    have g1 : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs0
    have g2 : Complex.Gammaℝ (s + 1) ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    have g3 : Complex.Gammaℂ s ≠ 0 := by
      rw [Complex.Gammaℂ]
      refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hs0)
      exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by
        intro h0; rw [neg_eq_zero.1 h0] at hs0; simp at hs0)).2 (by
        exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0))
    have hcs : ((c : ℝ) : ℂ) ^ (-(s / 2)) * ((c : ℝ) : ℂ) ^ (s / 2) = 1 := by
      rw [Complex.cpow_neg, inv_mul_cancel₀ ((Complex.cpow_ne_zero_iff_of_exponent_ne_zero
        (by intro h0; have := congrArg Complex.re h0; simp at this; linarith)).2 hc0)]
    have e1 : Complex.Gammaℝ s ^ a * (Complex.Gammaℝ s)⁻¹ ^ a = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ g1, one_pow]
    have e2 : Complex.Gammaℝ (s + 1) ^ b * (Complex.Gammaℝ (s + 1))⁻¹ ^ b = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ g2, one_pow]
    have e3 : Complex.Gammaℂ s ^ r * (Complex.Gammaℂ s)⁻¹ ^ r = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ g3, one_pow]
    show L s = Λ s * ((c : ℝ) : ℂ) ^ (-(s / 2)) * (Complex.Gammaℝ s)⁻¹ ^ a *
      (Complex.Gammaℝ (s + 1))⁻¹ ^ b * (Complex.Gammaℂ s)⁻¹ ^ r
    rw [h s hs]
    calc L s = L s * (((c : ℝ) : ℂ) ^ (-(s / 2)) * ((c : ℝ) : ℂ) ^ (s / 2)) *
        (Complex.Gammaℝ s ^ a * (Complex.Gammaℝ s)⁻¹ ^ a) *
        (Complex.Gammaℝ (s + 1) ^ b * (Complex.Gammaℝ (s + 1))⁻¹ ^ b) *
        (Complex.Gammaℂ s ^ r * (Complex.Gammaℂ s)⁻¹ ^ r) := by
          rw [hcs, e1, e2, e3]; ring
      _ = _ := by ring

open scoped Classical in
theorem coeff_one {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] {n : ℕ} (hn : n ≠ 0) :
    ArtinL.Abelian.coeff (1 : (M ≃ₐ[K] M) →* ℂˣ) n =
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) := by
  have hloc : ∀ v, ArtinL.Abelian.localValue (1 : (M ≃ₐ[K] M) →* ℂˣ) v = 1 := by
    intro v
    simp [ArtinL.Abelian.localValue, ArtinL.Abelian.IsUnramifiedAt]
  have hval : ∀ I, ArtinL.Abelian.idealValue (1 : (M ≃ₐ[K] M) →* ℂˣ) I = 1 := by
    intro I
    simp [ArtinL.Abelian.idealValue, hloc]
  rw [ArtinL.Abelian.coeff, if_neg hn]
  simp only [hval, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [← Set.ncard_eq_toFinset_card _ _, ← Nat.card_coe_set_eq]
  rfl

theorem lSeries_one {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [IsGalois K M] :
    ArtinL.Abelian.LSeries (1 : (M ≃ₐ[K] M) →* ℂˣ) = dedekindZeta K := by
  funext s
  exact LSeries_congr (fun hn => coeff_one hn) s

theorem ofSubgroup_one {k F : Type*} [Field k] [Field F] [Algebra k F] [FiniteDimensional k F]
    (H : Subgroup (F ≃ₐ[k] F)) : ArtinL.Abelian.ofSubgroup H (1 : H →* ℂˣ) = 1 := by
  simp [ArtinL.Abelian.ofSubgroup]

theorem ofSubgroup_ne_one {k F : Type*} [Field k] [Field F] [Algebra k F] [FiniteDimensional k F]
    (H : Subgroup (F ≃ₐ[k] F)) {χ : H →* ℂˣ} (hχ : χ ≠ 1) : ArtinL.Abelian.ofSubgroup H χ ≠ 1 := by
  intro h
  apply hχ
  ext x
  have := ArtinL.Abelian.ofSubgroup_fixingSubgroupEquiv H χ x
  rw [h] at this
  simp only [MonoidHom.one_apply] at this ⊢
  rw [← this]

/-- Entirety of `L(ψ)` for `ψ = ofSubgroup J χ`, `χ ≠ 1`, from 3508ac81. -/
theorem exists_entire_lSeries_ofSubgroup (F : IntermediateField ℚ (AlgebraicClosure ℚ))
    [NumberField F] [IsGalois ℚ F] (J : Subgroup (F ≃ₐ[ℚ] F)) (χ : J →* ℂˣ) (hχ : χ ≠ 1) :
    ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ ∀ s : ℂ, 1 < s.re →
      ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup J χ) s = E s := by
  have hψ := ofSubgroup_ne_one J hχ
  obtain ⟨W, Λ, Λ', -, hΛ, -, hEq, -⟩ :=
    ArtinL.Abelian.exists_completedLSeries_functionalEquation_u0
      (IntermediateField.fixedField J) F (ArtinL.Abelian.ofSubgroup J χ)
  have hc : (0 : ℝ) < |((discr (IntermediateField.fixedField J) : ℤ) : ℝ)| *
      (Ideal.absNorm (ArtinL.Abelian.conductor (ArtinL.Abelian.ofSubgroup J χ)) : ℝ) := by
    apply mul_pos
    · exact abs_pos.2 (by exact_mod_cast discr_ne_zero _)
    · exact_mod_cast ArtinL.Abelian.absNorm_conductor_pos _
  refine exists_entire_of_completed _ hc (ArtinL.Abelian.nPlus (ArtinL.Abelian.ofSubgroup J χ))
    (ArtinL.Abelian.nMinus (ArtinL.Abelian.ofSubgroup J χ))
    (InfinitePlace.nrComplexPlaces (IntermediateField.fixedField J)) hΛ (fun s hs => ?_)
  rw [(hEq s hs).1, if_neg hψ, one_mul, ArtinL.Abelian.completedLSeries]

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

/-- Induction data: a subgroup with a character. -/
abbrev IndDatum (F : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
  Σ J : Subgroup (F ≃ₐ[ℚ] F), (J →* ℂˣ)

open scoped Classical in
/-- The induced character `Ind(J, χ)(g)`, by Frobenius' formula as in 63e4cbfd. -/
noncomputable def ind {F : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField F]
    (q : IndDatum F)
    (g : F ≃ₐ[ℚ] F) : ℂ :=
  (Nat.card q.1 : ℂ)⁻¹ * ∑ x : F ≃ₐ[ℚ] F,
    if hx : x⁻¹ * g * x ∈ q.1 then (((q.2) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0

/-- `L(ψ)` for `ψ = ofSubgroup J χ`. -/
noncomputable def lf {F : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField F]
    [IsGalois ℚ F] (q : IndDatum F) (s : ℂ) : ℂ :=
  ArtinL.Abelian.LSeries (ArtinL.Abelian.ofSubgroup q.1 q.2) s

/-- 63e4cbfd applied to the trivial one-dimensional representation (trace `1`). -/
theorem artin_trivial (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F]
    [IsGalois ℚ F] {k : ℕ} (p : Fin k → IndDatum F) (a : Fin k → ℤ)
    (htr : ∀ g : F ≃ₐ[ℚ] F, ∑ i : Fin k, (a i : ℂ) * ind (p i) g = 1)
    {s : ℂ} (hs : 1 < s.re) :
    _root_.LSeries (ArtinL.coeff (1 : Γℚ →* GL (Fin 1) ℂ)) s * ∏ i, lf (p i) s ^ (-a i).toNat =
      ∏ i, lf (p i) s ^ (a i).toNat :=
  ArtinL.lSeries_mul_prod_pow_eq_prod_pow_of_trace_eq_sum 1 F 1 (MonoidHom.one_comp _).symm
    (fun i => (p i).1) (fun i => (p i).2) a (fun g => by
      have h := htr g
      simp only [ind] at h
      rw [h]; simp) hs

open scoped Classical in
/-- The Aramata–Brauer character identity A1 (prover C's `ABC.aramataBrauer_identity`,
specialised to `G : Type`). -/
def A1Statement : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (H K : Subgroup G), H ≤ K → (H.subgroupOf K).Normal →
    ∃ N : ℕ, 0 < N ∧ ∃ (k : ℕ) (J : Fin k → Subgroup G) (χ : (i : Fin k) → (J i →* ℂˣ))
      (m : Fin k → ℕ), (∀ i, χ i ≠ 1) ∧ ∀ g : G,
        (N : ℂ) * ((Nat.card H : ℂ)⁻¹ * ∑ x : G,
            if hx : x⁻¹ * g * x ∈ H then (((1 : H →* ℂˣ) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0) =
          (N : ℂ) * ((Nat.card K : ℂ)⁻¹ * ∑ x : G,
            if hx : x⁻¹ * g * x ∈ K then (((1 : K →* ℂˣ) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0) +
          ∑ i, (m i : ℂ) * ((Nat.card (J i) : ℂ)⁻¹ * ∑ x : G,
            if hx : x⁻¹ * g * x ∈ J i then (((χ i) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0)

theorem lf_one {F : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField F]
    [IsGalois ℚ F] (X : Subgroup (F ≃ₐ[ℚ] F)) :
    lf (⟨X, 1⟩ : IndDatum F) = dedekindZeta (IntermediateField.fixedField X) := by
  funext s
  rw [lf, ofSubgroup_one, lSeries_one]

/-- **A3**: Aramata–Brauer for subfields of `ℚ̄`, from A1. -/
theorem a3_of_a1 (hA1 : A1Statement) : A3Statement := by
  intro F _ _ H K hHK hnorm
  have hN : (H.subgroupOf K).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g.1 g.2 n.1 hn⟩
  obtain ⟨N, hN0, k, J, χ, m, hχ, hid⟩ := hA1 (F ≃ₐ[ℚ] F) H K hHK hN
  let pT : IndDatum F := ⟨⊤, 1⟩
  have htop : ∀ g : F ≃ₐ[ℚ] F, ind pT g = 1 := by
    intro g
    simp only [ind, pT, Subgroup.mem_top, dite_true, MonoidHom.one_apply, Units.val_one,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)), Nat.card_eq_fintype_card]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  let p2 : Fin (k + 3) → IndDatum F :=
    Fin.cons pT (Fin.cons ⟨H, 1⟩ (Fin.cons ⟨K, 1⟩ (fun i => ⟨J i, χ i⟩)))
  let a2 : Fin (k + 3) → ℤ := Fin.cons 1 (Fin.cons (N : ℤ) (Fin.cons (-(N : ℤ))
    (fun i => -(m i : ℤ))))
  have h1 : ∀ s : ℂ, 1 < s.re →
      _root_.LSeries (ArtinL.coeff (1 : Γℚ →* GL (Fin 1) ℂ)) s = lf pT s := by
    intro s hs
    have := artin_trivial F (fun _ : Fin 1 => pT) (fun _ => 1) (fun g => by simp [htop g]) hs
    simpa using this
  have h2 : ∀ s : ℂ, 1 < s.re →
      _root_.LSeries (ArtinL.coeff (1 : Γℚ →* GL (Fin 1) ℂ)) s *
        (lf ⟨K, 1⟩ s ^ N * ∏ i, lf ⟨J i, χ i⟩ s ^ m i) = lf pT s * lf ⟨H, 1⟩ s ^ N := by
    intro s hs
    have := artin_trivial F p2 a2 (fun g => by
      have hg : (N : ℂ) * ind ⟨H, 1⟩ g =
          (N : ℂ) * ind ⟨K, 1⟩ g + ∑ i, (m i : ℂ) * ind ⟨J i, χ i⟩ g := hid g
      simp only [Fin.sum_univ_succ, p2, a2, Fin.cons_zero, Fin.cons_succ, htop g,
        Int.cast_one, Int.cast_neg, Int.cast_natCast, neg_mul, Finset.sum_neg_distrib, one_mul]
      linear_combination hg) hs
    simpa [Fin.prod_univ_succ, p2, a2] using this
  have hE : ∀ i, ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ ∀ s : ℂ, 1 < s.re →
      lf ⟨J i, χ i⟩ s = E s :=
    fun i => exists_entire_lSeries_ofSubgroup F (J i) (χ i) (hχ i)
  choose E hEd hEq using hE
  refine ABR.exists_differentiable_dedekindZeta_eq_mul_of_pow_eq _ _ hN0
    (E := fun s => ∏ i, E i s ^ m i) ?_ (fun s hs => ?_)
  · exact Differentiable.fun_finsetProd (fun i _ => (hEd i).pow (m i))
  · have hT : lf pT s ≠ 0 := by
      rw [lf_one]
      exact NumberField.dedekindZeta_ne_zero_of_one_lt_re _ hs
    have h := h2 s hs
    rw [h1 s hs] at h
    have h' := mul_left_cancel₀ hT h
    rw [lf_one, lf_one] at h'
    rw [← h']
    simp only [hEq _ s hs]

/-- bcaac77f from A1 (A3 + A5). -/
theorem goal_of_a1 (hA1 : A1Statement) (K L : Type) [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧
      ∀ s : ℂ, 1 < s.re → dedekindZeta L s = dedekindZeta K s * h s :=
  of_A3 (a3_of_a1 hA1) K L

end ABA
end

section
namespace ArtinPrimitiveRoots

open NumberField

end ArtinPrimitiveRoots

end

section
open ArtinPrimitiveRoots
open NumberField
theorem solution (K L : Type) [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧
      ∀ s : ℂ, 1 < s.re → dedekindZeta L s = dedekindZeta K s * h s :=
  ABA.goal_of_a1 (fun G _ _ H K hHK hN => ABC.aramataBrauer_identity H K hHK hN) K L
end
