-- Prove2me | solution 1 for AlgebraicCurve.GluedPic0.closure_setOf_mk_single_sub_single_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/10396280-ca7a-59f4-a146-2a5582717d5e

import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_GluedPic0_closure_setOf_mk_single_sub_single_eq_top

set_option autoImplicit false

open AlgebraicCurve

namespace GluedGenAux

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (S : Finset (Place K F × Place K F)) (T₀ T₁ : Finset (Place K F))

def gen : Set (GluedPic0 K F S) :=
  {ξ : GluedPic0 K F S |
      ∃ (i : Fin 2) (P Q : Place K F) (x : ↥(GluingData.admissible S)),
        P ∉ (if i = 0 then T₀ else T₁) ∧ Q ∉ (if i = 0 then T₀ else T₁) ∧
        (x : GluingData K F S).1 =
            (if i = 0 then Finsupp.single P 1 - Finsupp.single Q 1 else 0) ∧
        (x : GluingData K F S).2.1 =
            (if i = 1 then Finsupp.single P 1 - Finsupp.single Q 1 else 0) ∧
        (x : GluingData K F S).2.2 = 0 ∧
        ξ = GluedPic0.mk S x}

omit [Algebra K F] in
theorem deg_eq_one [Algebra K F] (v : Place K F) (hv : Function.Surjective (algebraMap K v.ResidueField)) :
    v.deg = 1 := by
  have e : K ≃ₗ[K] v.ResidueField :=
    LinearEquiv.ofBijective (Algebra.linearMap K v.ResidueField)
      ⟨(algebraMap K v.ResidueField).injective, hv⟩
  rw [Place.deg, ← e.finrank_eq, Module.finrank_self]

theorem degree_eq_sum (hdeg : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) :
    Divisor.degree D = ∑ P ∈ D.support, D P := by
  have : Divisor.degree D = D.sum (fun v n => n * (v.deg : ℤ)) := by
    simp [Divisor.degree, Finsupp.liftAddHom_apply]
  rw [this, Finsupp.sum]
  exact Finset.sum_congr rfl fun v _ => by rw [hdeg v, Nat.cast_one, mul_one]

theorem eq_sum_smul_single_sub_single (hdeg : ∀ v : Place K F, v.deg = 1) (D : Divisor K F)
    (hD : Divisor.degree D = 0) (Q₀ : Place K F) :
    D = ∑ P ∈ D.support, D P • (Finsupp.single P (1 : ℤ) - Finsupp.single Q₀ 1) := by
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [← degree_eq_sum hdeg D, hD, zero_smul, sub_zero]
  conv_lhs => rw [← Finsupp.sum_single D, Finsupp.sum]
  exact Finset.sum_congr rfl fun P _ => by rw [Finsupp.smul_single_one]

theorem single_sub_single_mem_degZero (hdeg : ∀ v : Place K F, v.deg = 1) (P Q : Place K F) :
    Finsupp.single P (1 : ℤ) - Finsupp.single Q 1 ∈ Divisor.degZero (K := K) (F := F) := by
  rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg P, hdeg Q, sub_self]

theorem fst_mem_admissible {D : Divisor K F} (hD : D ∈ Divisor.degZero (K := K) (F := F))
    (hS : ∀ s ∈ S, D s.1 = 0) : ((D, 0, 0) : GluingData K F S) ∈ GluingData.admissible S :=
  ⟨hD, zero_mem _, fun s hs => ⟨hS s hs, rfl⟩⟩

theorem snd_mem_admissible {D : Divisor K F} (hD : D ∈ Divisor.degZero (K := K) (F := F))
    (hS : ∀ s ∈ S, D s.2 = 0) : ((0, D, 0) : GluingData K F S) ∈ GluingData.admissible S :=
  ⟨zero_mem _, hD, fun s hs => ⟨rfl, hS s hs⟩⟩

theorem mk_fst_mem_closure (hdeg : ∀ v : Place K F, v.deg = 1) {D : Divisor K F}
    (hD : D ∈ Divisor.degZero (K := K) (F := F)) (hDS : ∀ s ∈ S, D s.1 = 0) (hDT : ∀ P ∈ D.support, P ∉ T₀) :
    GluedPic0.mk S ⟨(D, 0, 0), fst_mem_admissible S hD hDS⟩ ∈ AddSubgroup.closure (gen S T₀ T₁) := by
  classical
  rcases D.support.eq_empty_or_nonempty with hsupp | ⟨Q₀, hQ₀⟩
  · have hD0 : D = 0 := Finsupp.support_eq_empty.1 hsupp
    subst hD0
    have : (⟨((0 : Divisor K F), 0, 0), fst_mem_admissible S hD hDS⟩ : ↥(GluingData.admissible S)) = 0 := rfl
    rw [this, map_zero]
    exact zero_mem _

  have hmem : ∀ P ∈ D.support, ((Finsupp.single P (1 : ℤ) - Finsupp.single Q₀ 1, 0, 0) : GluingData K F S) ∈
      GluingData.admissible S := fun P hP =>
    fst_mem_admissible S (single_sub_single_mem_degZero hdeg P Q₀) fun s hs => by
      have hP' : P ≠ s.1 := fun h => by rw [Finsupp.mem_support_iff, h] at hP; exact hP (hDS s hs)
      have hQ' : Q₀ ≠ s.1 := fun h => by rw [Finsupp.mem_support_iff, h] at hQ₀; exact hQ₀ (hDS s hs)
      rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hP'.symm, Finsupp.single_eq_of_ne hQ'.symm, sub_zero]
  let y : Place K F → ↥(GluingData.admissible S) := fun P =>
    if hP : P ∈ D.support then ⟨_, hmem P hP⟩ else 0
  have hy : ∀ P ∈ D.support, ((y P : ↥(GluingData.admissible S)) : GluingData K F S) =
      (Finsupp.single P (1 : ℤ) - Finsupp.single Q₀ 1, 0, 0) := fun P hP => by
    simp only [y, dif_pos hP]
  have hygen : ∀ P ∈ D.support, GluedPic0.mk S (y P) ∈ gen S T₀ T₁ := fun P hP =>
    ⟨0, P, Q₀, y P, by simpa using hDT P hP, by simpa using hDT Q₀ hQ₀,
      by rw [hy P hP, if_pos rfl], by rw [hy P hP, if_neg (by decide)], by rw [hy P hP], rfl⟩

  have hsum : (⟨(D, 0, 0), fst_mem_admissible S hD hDS⟩ : ↥(GluingData.admissible S)) =
      ∑ P ∈ D.support, D P • y P := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    have h1 : ∀ P ∈ D.support, (((D P • y P : ↥(GluingData.admissible S))) : GluingData K F S) =
        AddMonoidHom.inl (Divisor K F) (Divisor K F × (↥S → Additive Kˣ))
          (D P • (Finsupp.single P (1 : ℤ) - Finsupp.single Q₀ 1)) := fun P hP => by
      rw [AddSubgroupClass.coe_zsmul, hy P hP, map_zsmul]
      rfl
    rw [Finset.sum_congr rfl h1, ← map_sum, ← eq_sum_smul_single_sub_single hdeg D hD Q₀]
    rfl
  rw [hsum, map_sum]
  refine sum_mem fun P hP => ?_
  rw [map_zsmul]
  exact zsmul_mem (AddSubgroup.subset_closure (hygen P hP)) _

theorem mk_snd_mem_closure (hdeg : ∀ v : Place K F, v.deg = 1) {D : Divisor K F}
    (hD : D ∈ Divisor.degZero (K := K) (F := F)) (hDS : ∀ s ∈ S, D s.2 = 0) (hDT : ∀ P ∈ D.support, P ∉ T₁) :
    GluedPic0.mk S ⟨(0, D, 0), snd_mem_admissible S hD hDS⟩ ∈ AddSubgroup.closure (gen S T₀ T₁) := by
  classical
  rcases D.support.eq_empty_or_nonempty with hsupp | ⟨Q₀, hQ₀⟩
  · have hD0 : D = 0 := Finsupp.support_eq_empty.1 hsupp
    subst hD0
    have : (⟨((0 : Divisor K F), (0 : Divisor K F), 0), snd_mem_admissible S hD hDS⟩ :
      ↥(GluingData.admissible S)) = 0 := rfl
    rw [this, map_zero]
    exact zero_mem _
  have hmem : ∀ P ∈ D.support, ((0, Finsupp.single P (1 : ℤ) - Finsupp.single Q₀ 1, 0) : GluingData K F S) ∈
      GluingData.admissible S := fun P hP =>
    snd_mem_admissible S (single_sub_single_mem_degZero hdeg P Q₀) fun s hs => by
      have hP' : P ≠ s.2 := fun h => by rw [Finsupp.mem_support_iff, h] at hP; exact hP (hDS s hs)
      have hQ' : Q₀ ≠ s.2 := fun h => by rw [Finsupp.mem_support_iff, h] at hQ₀; exact hQ₀ (hDS s hs)
      rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hP'.symm, Finsupp.single_eq_of_ne hQ'.symm, sub_zero]
  let y : Place K F → ↥(GluingData.admissible S) := fun P =>
    if hP : P ∈ D.support then ⟨_, hmem P hP⟩ else 0
  have hy : ∀ P ∈ D.support, ((y P : ↥(GluingData.admissible S)) : GluingData K F S) =
      (0, Finsupp.single P (1 : ℤ) - Finsupp.single Q₀ 1, 0) := fun P hP => by
    simp only [y, dif_pos hP]
  have hygen : ∀ P ∈ D.support, GluedPic0.mk S (y P) ∈ gen S T₀ T₁ := fun P hP =>
    ⟨1, P, Q₀, y P, by simpa using hDT P hP, by simpa using hDT Q₀ hQ₀,
      by rw [hy P hP, if_neg (by decide)], by rw [hy P hP, if_pos rfl], by rw [hy P hP], rfl⟩
  have hsum : (⟨(0, D, 0), snd_mem_admissible S hD hDS⟩ : ↥(GluingData.admissible S)) =
      ∑ P ∈ D.support, D P • y P := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    have h1 : ∀ P ∈ D.support, (((D P • y P : ↥(GluingData.admissible S))) : GluingData K F S) =
        (AddMonoidHom.inr (Divisor K F) (Divisor K F × (↥S → Additive Kˣ))).comp
          (AddMonoidHom.inl (Divisor K F) (↥S → Additive Kˣ))
          (D P • (Finsupp.single P (1 : ℤ) - Finsupp.single Q₀ 1)) := fun P hP => by
      rw [AddSubgroupClass.coe_zsmul, hy P hP, map_zsmul]
      rfl
    rw [Finset.sum_congr rfl h1, ← map_sum, ← eq_sum_smul_single_sub_single hdeg D hD Q₀]
    rfl
  rw [hsum, map_sum]
  refine sum_mem fun P hP => ?_
  rw [map_zsmul]
  exact zsmul_mem (AddSubgroup.subset_closure (hygen P hP)) _

theorem mk_nodeUnit_mem_closure [HasPrincipalDivisors K F] (hdeg : ∀ v : Place K F, v.deg = 1)
    (hS : Set.InjOn Prod.snd (S : Set (Place K F × Place K F)))
    (hval : ∀ (E : Finset (Place K F)) (c : Place K F → Kˣ), ∃ g : F, ∀ e ∈ E, e.HasValue g (c e))
    (w : ↥S → Additive Kˣ) :
    GluedPic0.mk S ⟨(0, 0, w), GluingData.zero_zero_mem_admissible S w⟩ ∈ AddSubgroup.closure (gen S T₀ T₁) := by
  classical
  rcases S.eq_empty_or_nonempty with hSe | ⟨s₀, hs₀⟩
  · subst hSe
    have hw : w = 0 := funext fun s => absurd s.2 (Finset.notMem_empty _)
    subst hw
    have : (⟨((0 : Divisor K F), (0 : Divisor K F), (0 : ↥(∅ : Finset (Place K F × Place K F)) → Additive Kˣ)),
      GluingData.zero_zero_mem_admissible ∅ 0⟩ : ↥(GluingData.admissible (∅ : Finset (Place K F × Place K F)))) = 0 := rfl
    rw [this, map_zero]
    exact zero_mem _

  let c : Place K F → Kˣ := fun P =>
    if h : ∃ s : ↥S, (s : Place K F × Place K F).2 = P then (Additive.toMul (w h.choose))⁻¹ else 1
  have hc : ∀ s : ↥S, c (s : Place K F × Place K F).2 = (Additive.toMul (w s))⁻¹ := fun s => by
    have h : ∃ t : ↥S, (t : Place K F × Place K F).2 = (s : Place K F × Place K F).2 := ⟨s, rfl⟩
    simp only [c, dif_pos h]
    have : h.choose = s := Subtype.ext (hS h.choose.2 s.2 h.choose_spec)
    rw [this]
  obtain ⟨g, hg⟩ := hval (T₁ ∪ S.image Prod.snd) c
  have hg0 : g ≠ 0 :=
    (hg s₀.2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs₀))).ne_zero (c _).ne_zero
  obtain ⟨Dg, hDg, hDg0⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg0
  have hord : ∀ e ∈ T₁ ∪ S.image Prod.snd, Dg e = 0 := fun e he => by
    rw [hDg e]; exact (hg e he).ord_eq_zero (c e).ne_zero

  have hzadm : (((0 : Divisor K F), Dg, w) : GluingData K F S) ∈ GluingData.admissible S :=
    ⟨zero_mem _, Divisor.mem_degZero.2 hDg0, fun s hs =>
      ⟨rfl, hord _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs))⟩⟩
  have hz0 : GluedPic0.mk S ⟨_, hzadm⟩ = 0 := by
    rw [GluedPic0.mk_eq_zero_iff]
    refine ⟨1, g, 1, fun s => (Additive.toMul (w s))⁻¹, one_ne_zero, hg0, fun v => by simp, fun v => hDg v,
      fun s => ⟨by simpa using (s : Place K F × Place K F).1.hasValue_one, ?_⟩, ?_⟩
    · dsimp only
      rw [← hc s]
      exact hg _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ s.2))
    · funext s
      simp

  have hneg : (-Dg) ∈ Divisor.degZero (K := K) (F := F) := neg_mem (Divisor.mem_degZero.2 hDg0)
  have hnegS : ∀ s ∈ S, (-Dg) s.2 = 0 := fun s hs => by
    rw [Finsupp.neg_apply, hord _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs)), neg_zero]
  have hsplit : (⟨(0, 0, w), GluingData.zero_zero_mem_admissible S w⟩ : ↥(GluingData.admissible S)) =
      ⟨_, hzadm⟩ + ⟨(0, -Dg, 0), snd_mem_admissible S hneg hnegS⟩ := by
    apply Subtype.ext
    show ((0 : Divisor K F), (0 : Divisor K F), w) = ((0 : Divisor K F), Dg, w) + (0, -Dg, 0)
    simp
  rw [hsplit, map_add]
  refine add_mem (by rw [hz0]; exact zero_mem _) (mk_snd_mem_closure S T₀ T₁ hdeg hneg hnegS fun P hP hPT => ?_)
  rw [Finsupp.mem_support_iff, Finsupp.neg_apply, hord P (Finset.mem_union_left _ hPT), neg_zero] at hP
  exact hP rfl

theorem mk_fst_mem_closure_of_admissible [HasPrincipalDivisors K F] (hdeg : ∀ v : Place K F, v.deg = 1)
    (hrat : ∀ v : Place K F, Function.Surjective (algebraMap K v.ResidueField))
    (hS : Set.InjOn Prod.snd (S : Set (Place K F × Place K F)))
    (hval : ∀ (E : Finset (Place K F)) (c : Place K F → Kˣ), ∃ g : F, ∀ e ∈ E, e.HasValue g (c e))
    {D : Divisor K F} (hD : D ∈ Divisor.degZero (K := K) (F := F)) (hDS : ∀ s ∈ S, D s.1 = 0) :
    GluedPic0.mk S ⟨(D, 0, 0), fst_mem_admissible S hD hDS⟩ ∈ AddSubgroup.closure (gen S T₀ T₁) := by
  classical
  obtain ⟨f, hf0, hf⟩ := Place.exists_forall_ord_eq (T₀ ∪ S.image Prod.fst) (fun v => D v)
  obtain ⟨Df, hDf, hDf0⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0

  have hunit : ∀ s : ↥S, ∃ a : Kˣ, (s : Place K F × Place K F).1.HasValue f a := fun s => by
    have h0 : (s : Place K F × Place K F).1.ord f = 0 := by
      rw [hf _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ s.2)), hDS _ s.2]
    obtain ⟨hm, hu⟩ := (s : Place K F × Place K F).1.exists_isUnit_of_ord_eq_zero hf0 h0
    obtain ⟨a, ha, ha0⟩ := (s : Place K F × Place K F).1.exists_hasValue_of_surjective (hrat _) hm
    exact ⟨Units.mk0 a (ha0 hu), ha⟩
  choose a ha using hunit
  have hDfS : ∀ s ∈ S, Df s.1 = 0 := fun s hs => by
    rw [hDf, hf _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs)), hDS s hs]

  have hzadm : ((Df, 0, fun s => Additive.ofMul (a s)) : GluingData K F S) ∈ GluingData.admissible S :=
    ⟨Divisor.mem_degZero.2 hDf0, zero_mem _, fun s hs => ⟨hDfS s hs, rfl⟩⟩
  have hz0 : GluedPic0.mk S ⟨_, hzadm⟩ = 0 := by
    rw [GluedPic0.mk_eq_zero_iff]
    refine ⟨f, 1, a, 1, hf0, one_ne_zero, fun v => hDf v, fun v => by simp,
      fun s => ⟨ha s, by simpa using (s : Place K F × Place K F).2.hasValue_one⟩, ?_⟩
    funext s
    simp

  have hsub : D - Df ∈ Divisor.degZero (K := K) (F := F) := sub_mem hD (Divisor.mem_degZero.2 hDf0)
  have hsubS : ∀ s ∈ S, (D - Df) s.1 = 0 := fun s hs => by
    rw [Finsupp.sub_apply, hDS s hs, hDfS s hs, sub_zero]
  have hsplit : (⟨(D, 0, 0), fst_mem_admissible S hD hDS⟩ : ↥(GluingData.admissible S)) =
      ⟨(D - Df, 0, 0), fst_mem_admissible S hsub hsubS⟩ + ⟨_, hzadm⟩ +
        ⟨(0, 0, fun s => -Additive.ofMul (a s)), GluingData.zero_zero_mem_admissible S _⟩ := by
    apply Subtype.ext
    show (D, (0 : Divisor K F), (0 : ↥S → Additive Kˣ)) =
      (D - Df, 0, 0) + (Df, 0, fun s => Additive.ofMul (a s)) + (0, 0, fun s => -Additive.ofMul (a s))
    ext s <;> simp
  rw [hsplit, map_add, map_add]
  refine add_mem (add_mem (mk_fst_mem_closure S T₀ T₁ hdeg hsub hsubS fun P hP hPT => ?_)
    (by rw [hz0]; exact zero_mem _)) (mk_nodeUnit_mem_closure S T₀ T₁ hdeg hS hval _)
  rw [Finsupp.mem_support_iff, Finsupp.sub_apply, hDf, hf P (Finset.mem_union_left _ hPT), sub_self] at hP
  exact hP rfl

theorem mk_snd_mem_closure_of_admissible [HasPrincipalDivisors K F] (hdeg : ∀ v : Place K F, v.deg = 1)
    (hrat : ∀ v : Place K F, Function.Surjective (algebraMap K v.ResidueField))
    (hS : Set.InjOn Prod.snd (S : Set (Place K F × Place K F)))
    (hval : ∀ (E : Finset (Place K F)) (c : Place K F → Kˣ), ∃ g : F, ∀ e ∈ E, e.HasValue g (c e))
    {D : Divisor K F} (hD : D ∈ Divisor.degZero (K := K) (F := F)) (hDS : ∀ s ∈ S, D s.2 = 0) :
    GluedPic0.mk S ⟨(0, D, 0), snd_mem_admissible S hD hDS⟩ ∈ AddSubgroup.closure (gen S T₀ T₁) := by
  classical
  obtain ⟨f, hf0, hf⟩ := Place.exists_forall_ord_eq (T₁ ∪ S.image Prod.snd) (fun v => D v)
  obtain ⟨Df, hDf, hDf0⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have hunit : ∀ s : ↥S, ∃ b : Kˣ, (s : Place K F × Place K F).2.HasValue f b := fun s => by
    have h0 : (s : Place K F × Place K F).2.ord f = 0 := by
      rw [hf _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ s.2)), hDS _ s.2]
    obtain ⟨hm, hu⟩ := (s : Place K F × Place K F).2.exists_isUnit_of_ord_eq_zero hf0 h0
    obtain ⟨b, hb, hb0⟩ := (s : Place K F × Place K F).2.exists_hasValue_of_surjective (hrat _) hm
    exact ⟨Units.mk0 b (hb0 hu), hb⟩
  choose b hb using hunit
  have hDfS : ∀ s ∈ S, Df s.2 = 0 := fun s hs => by
    rw [hDf, hf _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs)), hDS s hs]
  have hzadm : ((0, Df, fun s => Additive.ofMul (1 / b s)) : GluingData K F S) ∈ GluingData.admissible S :=
    ⟨zero_mem _, Divisor.mem_degZero.2 hDf0, fun s hs => ⟨rfl, hDfS s hs⟩⟩
  have hz0 : GluedPic0.mk S ⟨_, hzadm⟩ = 0 := by
    rw [GluedPic0.mk_eq_zero_iff]
    exact ⟨1, f, 1, b, one_ne_zero, hf0, fun v => by simp, fun v => hDf v,
      fun s => ⟨by simpa using (s : Place K F × Place K F).1.hasValue_one, hb s⟩, rfl⟩
  have hsub : D - Df ∈ Divisor.degZero (K := K) (F := F) := sub_mem hD (Divisor.mem_degZero.2 hDf0)
  have hsubS : ∀ s ∈ S, (D - Df) s.2 = 0 := fun s hs => by
    rw [Finsupp.sub_apply, hDS s hs, hDfS s hs, sub_zero]
  have hsplit : (⟨(0, D, 0), snd_mem_admissible S hD hDS⟩ : ↥(GluingData.admissible S)) =
      ⟨(0, D - Df, 0), snd_mem_admissible S hsub hsubS⟩ + ⟨_, hzadm⟩ +
        ⟨(0, 0, fun s => -Additive.ofMul (1 / b s)), GluingData.zero_zero_mem_admissible S _⟩ := by
    apply Subtype.ext
    show ((0 : Divisor K F), D, (0 : ↥S → Additive Kˣ)) =
      (0, D - Df, 0) + (0, Df, fun s => Additive.ofMul (1 / b s)) + (0, 0, fun s => -Additive.ofMul (1 / b s))
    ext s <;> simp
  rw [hsplit, map_add, map_add]
  refine add_mem (add_mem (mk_snd_mem_closure S T₀ T₁ hdeg hsub hsubS fun P hP hPT => ?_)
    (by rw [hz0]; exact zero_mem _)) (mk_nodeUnit_mem_closure S T₀ T₁ hdeg hS hval _)
  rw [Finsupp.mem_support_iff, Finsupp.sub_apply, hDf, hf P (Finset.mem_union_left _ hPT), sub_self] at hP
  exact hP rfl

end GluedGenAux

open GluedGenAux in
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [AlgebraicCurve.HasPrincipalDivisors K F]
    (S : Finset (AlgebraicCurve.Place K F × AlgebraicCurve.Place K F))
    (hS : Set.InjOn Prod.snd (S : Set (AlgebraicCurve.Place K F × AlgebraicCurve.Place K F)))
    (hrat : ∀ v : AlgebraicCurve.Place K F, Function.Surjective (algebraMap K v.ResidueField))
    (hval : ∀ (E : Finset (AlgebraicCurve.Place K F)) (c : AlgebraicCurve.Place K F → Kˣ),
      ∃ g : F, ∀ e ∈ E, e.HasValue g (c e))
    (T₀ T₁ : Finset (AlgebraicCurve.Place K F)) :
    AddSubgroup.closure {ξ : AlgebraicCurve.GluedPic0 K F S |
      ∃ (i : Fin 2) (P Q : AlgebraicCurve.Place K F) (x : ↥(AlgebraicCurve.GluingData.admissible S)),
        P ∉ (if i = 0 then T₀ else T₁) ∧ Q ∉ (if i = 0 then T₀ else T₁) ∧
        (x : AlgebraicCurve.GluingData K F S).1 =
            (if i = 0 then Finsupp.single P 1 - Finsupp.single Q 1 else 0) ∧
        (x : AlgebraicCurve.GluingData K F S).2.1 =
            (if i = 1 then Finsupp.single P 1 - Finsupp.single Q 1 else 0) ∧
        (x : AlgebraicCurve.GluingData K F S).2.2 = 0 ∧
        ξ = AlgebraicCurve.GluedPic0.mk S x} = ⊤ := by
  have hdeg : ∀ v : Place K F, v.deg = 1 := fun v => deg_eq_one v (hrat v)
  change AddSubgroup.closure (gen S T₀ T₁) = ⊤
  refine eq_top_iff.2 fun ξ _ => ?_
  obtain ⟨x, rfl⟩ := GluedPic0.mk_surjective S ξ
  obtain ⟨⟨D₁, D₂, w⟩, h₁, h₂, h₃⟩ := x
  have hsplit : (⟨(D₁, D₂, w), h₁, h₂, h₃⟩ : ↥(GluingData.admissible S)) =
      ⟨(D₁, 0, 0), fst_mem_admissible S h₁ fun s hs => (h₃ s hs).1⟩ +
        ⟨(0, D₂, 0), snd_mem_admissible S h₂ fun s hs => (h₃ s hs).2⟩ +
        ⟨(0, 0, w), GluingData.zero_zero_mem_admissible S w⟩ := by
    apply Subtype.ext
    show (D₁, D₂, w) = (D₁, (0 : Divisor K F), (0 : ↥S → Additive Kˣ)) + (0, D₂, 0) + (0, 0, w)
    simp
  rw [hsplit, map_add, map_add]
  exact add_mem (add_mem
    (mk_fst_mem_closure_of_admissible S T₀ T₁ hdeg hrat hS hval h₁ fun s hs => (h₃ s hs).1)
    (mk_snd_mem_closure_of_admissible S T₀ T₁ hdeg hrat hS hval h₂ fun s hs => (h₃ s hs).2))
    (mk_nodeUnit_mem_closure S T₀ T₁ hdeg hS hval w)

end S_AlgebraicCurve_GluedPic0_closure_setOf_mk_single_sub_single_eq_top
end P2MW
export P2MW.S_AlgebraicCurve_GluedPic0_closure_setOf_mk_single_sub_single_eq_top (solution)
