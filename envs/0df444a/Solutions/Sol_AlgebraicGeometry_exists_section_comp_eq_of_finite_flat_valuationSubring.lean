-- Prove2me | solution 1 for AlgebraicGeometry.exists_section_comp_eq_of_finite_flat_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e270ad96-7517-50da-a2c1-02760d19800c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_section_comp_eq_of_finite_flat_valuationSubring

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace LiftPts

open IsLocalRing

theorem integers (L : Type*) [Field L] (O : ValuationSubring L) : O.valuation.Integers ↥O :=
  { hom_inj := Subtype.coe_injective
    map_le_one := fun x => O.valuation_le_one x
    exists_of_le_one := fun r hr => ⟨⟨r, (O.valuation_le_one_iff r).1 hr⟩, rfl⟩ }

theorem mem_of_isIntegral {L : Type*} [Field L] (O : ValuationSubring L) {x : L} (hx : IsIntegral ↥O x) : x ∈ O := by
  have := (integers L O).mem_of_integral hx
  rwa [Valuation.mem_integer_iff, O.valuation_le_one_iff] at this

theorem exists_retraction_residue_comp_eq
    {L : Type*} [Field L] [IsAlgClosed L] (O : ValuationSubring L) {B : Type*} [CommRing B]
    (φ : ↥O →+* B) (hfin : φ.Finite) (hflat : φ.Flat)
    (χ : B →+* ResidueField ↥O) (hχ : χ.comp φ = residue ↥O) :
    ∃ s : B →+* ↥O, s.comp φ = RingHom.id ↥O ∧ (residue ↥O).comp s = χ := by
  classical
  letI : Algebra ↥O B := φ.toAlgebra
  haveI : Module.Finite ↥O B := hfin
  haveI : Module.Flat ↥O B := hflat
  have hφ : ∀ a, φ a = algebraMap ↥O B a := fun _ => rfl

  haveI : Nontrivial B := ⟨⟨0, 1, fun h => zero_ne_one (by rw [← map_zero χ, ← map_one χ, h])⟩⟩

  set 𝔪 : Ideal B := RingHom.ker χ with h𝔪
  have hχsurj : Function.Surjective χ := fun x => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    exact ⟨φ a, by rw [← RingHom.comp_apply, hχ]⟩
  haveI h𝔪max : 𝔪.IsMaximal := RingHom.ker_isMaximal_of_surjective χ hχsurj
  obtain ⟨𝔭, h𝔭min, h𝔭𝔪⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal B) ≤ 𝔪)
  haveI h𝔭 : 𝔭.IsPrime := h𝔭min.1.1

  haveI : Algebra.HasGoingDown ↥O B := Algebra.HasGoingDown.of_flat
  have h𝔭O : 𝔭.comap (algebraMap ↥O B) = ⊥ := by
    by_contra hne
    haveI : (𝔭.comap (algebraMap ↥O B)).IsPrime := Ideal.comap_isPrime _ 𝔭
    haveI : 𝔭.LiesOver (𝔭.comap (algebraMap ↥O B)) := ⟨rfl⟩
    have hlt : (⊥ : Ideal ↥O) < 𝔭.comap (algebraMap ↥O B) := bot_lt_iff_ne_bot.2 hne
    obtain ⟨P, hP𝔭, hP, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt 𝔭 hlt
    exact absurd (h𝔭min.2 ⟨hP, bot_le⟩ hP𝔭.le) (not_le_of_gt hP𝔭)

  haveI : IsDomain (B ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  have hinjS : Function.Injective (algebraMap ↥O (B ⧸ 𝔭)) := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_comap_bot, IsScalarTower.algebraMap_eq ↥O B (B ⧸ 𝔭),
      ← Ideal.comap_comap, Ideal.Quotient.algebraMap_eq, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact h𝔭O
  haveI : NoZeroSMulDivisors ↥O (B ⧸ 𝔭) := ⟨fun {c x} h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp (fun h0 => hinjS (by rw [h0, map_zero])) id⟩
  haveI : Module.IsTorsionFree ↥O (B ⧸ 𝔭) := inferInstance
  haveI : Module.Finite ↥O (B ⧸ 𝔭) := inferInstance
  haveI : Algebra.IsIntegral ↥O (B ⧸ 𝔭) := inferInstance
  haveI : Algebra.IsAlgebraic ↥O (B ⧸ 𝔭) := inferInstance
  haveI : Module.IsTorsionFree ↥O L := inferInstance

  let ψ : (B ⧸ 𝔭) →ₐ[↥O] L := IsAlgClosed.lift
  have hψO : ∀ x : B ⧸ 𝔭, ψ x ∈ O := fun x =>
    mem_of_isIntegral O ((Algebra.IsIntegral.isIntegral (R := ↥O) x).map ψ)
  have hψinj : Function.Injective ψ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := ↥O)
    refine eq_bot_iff.2 fun a ha => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    have : algebraMap ↥O L a = 0 := by
      first
        | rwa [ψ.commutes] at ha
        | (rw [AlgHom.coe_toRingHom, ψ.commutes] at ha; exact ha)
    have hinjOL : Function.Injective (algebraMap ↥O L) := Subtype.coe_injective
    exact (Ideal.mem_bot).2 (hinjOL (by rw [this, map_zero]))
  let s₀ : (B ⧸ 𝔭) →+* ↥O := ψ.toRingHom.codRestrict O hψO
  have hs₀ : ∀ x, ((s₀ x : ↥O) : L) = ψ x := fun _ => rfl
  have hs₀inj : Function.Injective s₀ := fun x y h => hψinj (by rw [← hs₀, ← hs₀, h])
  have hs₀alg : ∀ a : ↥O, s₀ (algebraMap ↥O (B ⧸ 𝔭) a) = a := fun a => Subtype.ext (by rw [hs₀]; exact ψ.commutes a)

  let s : B →+* ↥O := s₀.comp (Ideal.Quotient.mk 𝔭)
  have hsφ : s.comp φ = RingHom.id ↥O := by
    apply RingHom.ext
    intro a
    change s₀ (Ideal.Quotient.mk 𝔭 (φ a)) = a
    rw [hφ, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact hs₀alg a
  have hkers : RingHom.ker s ≤ 𝔪 := by
    intro b hb
    apply h𝔭𝔪
    rw [← Ideal.mk_ker (I := 𝔭)]
    exact hs₀inj (by rw [map_zero]; exact hb)
  refine ⟨s, hsφ, ?_⟩
  ext b

  have h1 : b - φ (s b) ∈ RingHom.ker s := by
    rw [RingHom.mem_ker, map_sub, ← RingHom.comp_apply, hsφ, RingHom.id_apply, sub_self]
  have h2 := hkers h1
  rw [h𝔪, RingHom.mem_ker, map_sub, sub_eq_zero, ← RingHom.comp_apply χ φ, hχ] at h2
  exact h2.symm

end LiftPts

theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (O : ValuationSubring L)
    {Z : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of ↥O)) [IsFinite f] [Flat f]
    (zbar : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥O)) ⟶ Z)
    (hzbar : zbar ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))) :
    ∃ z : Spec (CommRingCat.of ↥O) ⟶ Z, z ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ z = zbar := by
  classical
  haveI : IsAffine Z := isAffine_of_isAffineHom f

  let B := Γ(Z, ⊤)
  let ιO := Scheme.ΓSpecIso (CommRingCat.of ↥O)
  let ιk := Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField ↥O))
  let ιB := Scheme.ΓSpecIso B
  let φ : ↥O →+* B := f.appTop.hom.comp ιO.inv.hom
  let χ : B →+* IsLocalRing.ResidueField ↥O := ιk.hom.hom.comp zbar.appTop.hom
  have hfin : φ.Finite :=
    RingHom.Finite.comp (IsFinite.finite_app f ⊤ (isAffineOpen_top _))
      (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso ιO.inv).2)
  have hflat : φ.Flat :=
    RingHom.Flat.comp (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso ιO.inv))
      (HasRingHomProperty.appTop @Flat f inferInstance)
  have hχ : χ.comp φ = IsLocalRing.residue ↥O := by
    have h1 : f.appTop ≫ zbar.appTop = (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))).appTop := by
      rw [← Scheme.Hom.comp_appTop, hzbar]
    have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (IsLocalRing.residue ↥O))

    have h3 : (ιO.inv ≫ f.appTop ≫ zbar.appTop ≫ ιk.hom) = CommRingCat.ofHom (IsLocalRing.residue ↥O) := by
      rw [← Category.assoc f.appTop, h1, h2, Iso.inv_hom_id_assoc]
    have := congrArg CommRingCat.Hom.hom h3
    simp [CommRingCat.hom_comp, RingHom.comp_assoc] at this
    exact this

  obtain ⟨s, hs1, hs2⟩ := LiftPts.exists_retraction_residue_comp_eq O φ hfin hflat χ hχ

  let z : Spec (CommRingCat.of ↥O) ⟶ Z := Spec.map (CommRingCat.ofHom s) ≫ Z.isoSpec.inv
  have hinvTop : Z.isoSpec.inv.appTop = ιB.inv := by
    have h : Z.isoSpec.hom.appTop = ιB.hom := by rw [Scheme.isoSpec_hom]; exact Scheme.toSpecΓ_appTop Z
    have h' : Z.isoSpec.hom.appTop ≫ Z.isoSpec.inv.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]
    rw [h] at h'
    rw [← Category.comp_id ιB.inv, ← h', Iso.inv_hom_id_assoc]
  have hzTop : z.appTop = CommRingCat.ofHom s ≫ ιO.inv := by
    show (Spec.map (CommRingCat.ofHom s) ≫ Z.isoSpec.inv).appTop = _
    rw [Scheme.Hom.comp_appTop, hinvTop]
    exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom s)).symm
  refine ⟨z, ext_of_isAffine ?_, ext_of_isAffine ?_⟩
  ·
    rw [Scheme.Hom.comp_appTop, hzTop, Scheme.Hom.id_appTop]
    have h4 : ιO.inv ≫ f.appTop ≫ CommRingCat.ofHom s = 𝟙 _ := by
      apply CommRingCat.hom_ext
      have := hs1
      ext a
      have h__af := (congrArg (fun g => g a) this)
      simp [CommRingCat.hom_comp] at h__af ⊢
      exact h__af
    calc f.appTop ≫ CommRingCat.ofHom s ≫ ιO.inv
        = ιO.hom ≫ (ιO.inv ≫ f.appTop ≫ CommRingCat.ofHom s) ≫ ιO.inv := by simp [Category.assoc]
      _ = 𝟙 _ := by rw [h4, Category.id_comp, Iso.hom_inv_id]
  ·
    rw [Scheme.Hom.comp_appTop, hzTop, Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, ← Category.assoc,
      ← CommRingCat.ofHom_comp, hs2]
    show CommRingCat.ofHom (ιk.hom.hom.comp zbar.appTop.hom) ≫ ιk.inv = zbar.appTop
    rw [show CommRingCat.ofHom (ιk.hom.hom.comp zbar.appTop.hom) = zbar.appTop ≫ ιk.hom from rfl, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

end S_AlgebraicGeometry_exists_section_comp_eq_of_finite_flat_valuationSubring
end P2MW
export P2MW.S_AlgebraicGeometry_exists_section_comp_eq_of_finite_flat_valuationSubring (solution)
