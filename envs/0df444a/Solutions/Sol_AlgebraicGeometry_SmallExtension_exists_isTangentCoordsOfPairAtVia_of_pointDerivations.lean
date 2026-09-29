-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAtVia_of_pointDerivations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/28a8cdc8-fd9b-5949-a04a-0856fbe1bbff

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Theorems.Thm_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective
import Theorems.Thm_AlgebraicGeometry_SmallExtension_existsUnique_comp_eq_and_isTangentOfPair_of_flat_of_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAtVia_of_pointDerivations

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover GoodReductionJacobian NeronModelInfra"

universe u

namespace ZeroSectionAux

open AlgebraicGeometry.SmallExtension

variable {T' : Type u} [CommRing T'] [IsLocalRing T']
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (C : Type u) [CommRing C] [Algebra T' C]

variable (T') in

noncomputable def aug : thickening T' V C →ₐ[ResidueField T'] ResidueField T' ⊗[T'] C :=
  Algebra.TensorProduct.lift (R := ResidueField T') (S := ResidueField T')
    (AlgHom.id (ResidueField T') (ResidueField T' ⊗[T'] C))
    ((Algebra.ofId (ResidueField T') (ResidueField T' ⊗[T'] C)).comp (TrivSqZeroExt.fstHom (ResidueField T') (ResidueField T') V))
    (fun _ _ => Commute.all _ _)

theorem aug_tmul (a : ResidueField T' ⊗[T'] C) (t : TrivSqZeroExt (ResidueField T') V) :
    aug T' V C (a ⊗ₜ t) = a * algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) t.fst := by
  simp [aug, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]

theorem zeroSection_eq_specMap_aug :
    SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C) =
      Spec.map (CommRingCat.ofHom (aug T' V C).toRingHom) := by
  apply (thickening_isPullback V C).hom_ext
  · rw [SquareZero.zeroSection_fst, thickeningFst, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id,
      ← CommRingCat.ofHom_id]
    congr 2
    refine RingHom.ext fun a => ?_
    change a = aug T' V C (a ⊗ₜ 1)
    rw [aug_tmul, TrivSqZeroExt.fst_one, map_one, mul_one]
  · rw [SquareZero.zeroSection_snd, thickeningSnd, reductionBase, SquareZero.basePoint, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun t => ?_
    change algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) t.fst = aug T' V C (1 ⊗ₜ t)
    rw [aug_tmul, one_mul]

theorem isNilpotent_of_aug_eq_zero (x : thickening T' V C) (hx : aug T' V C x = 0) : IsNilpotent x := by

  let J : Ideal (thickening T' V C) := Ideal.span (Set.range fun v : V => (1 : ResidueField T' ⊗[T'] C) ⊗ₜ[ResidueField T'] (TrivSqZeroExt.inr v))
  haveI : J.IsTwoSided := ⟨fun b ha => mul_comm b _ ▸ J.smul_mem _ ha⟩
  have hJ2 : J * J = ⊥ := by
    rw [Ideal.span_mul_span, Ideal.span_eq_bot]
    rintro z ⟨a, ⟨v, rfl⟩, b, ⟨v', rfl⟩, rfl⟩
    change ((1 : ResidueField T' ⊗[T'] C) ⊗ₜ[ResidueField T'] (TrivSqZeroExt.inr v : TrivSqZeroExt (ResidueField T') V)) *
      ((1 : ResidueField T' ⊗[T'] C) ⊗ₜ[ResidueField T'] (TrivSqZeroExt.inr v' : TrivSqZeroExt (ResidueField T') V)) = 0
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, TrivSqZeroExt.inr_mul_inr, TensorProduct.tmul_zero]

  have hmem : ∀ y : thickening T' V C, y - Algebra.TensorProduct.includeLeftRingHom (aug T' V C y) ∈ J := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a t =>
      rw [aug_tmul]
      have hincl : Algebra.TensorProduct.includeLeftRingHom (a * algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) t.fst) =
          a ⊗ₜ[ResidueField T'] (TrivSqZeroExt.inl t.fst : TrivSqZeroExt (ResidueField T') V) := by
        change (a * algebraMap (ResidueField T') (ResidueField T' ⊗[T'] C) t.fst) ⊗ₜ[ResidueField T'] (1 : TrivSqZeroExt (ResidueField T') V) = _
        rw [mul_comm, ← Algebra.smul_def, ← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul, ← Algebra.algebraMap_eq_smul_one,
          TrivSqZeroExt.algebraMap_eq_inl]
      have hsub : t - TrivSqZeroExt.inl t.fst = TrivSqZeroExt.inr t.snd := by
        rw [sub_eq_iff_eq_add, add_comm, TrivSqZeroExt.inl_fst_add_inr_snd_eq]
      rw [hincl, ← TensorProduct.tmul_sub, hsub,
        show a ⊗ₜ[ResidueField T'] (TrivSqZeroExt.inr t.snd : TrivSqZeroExt (ResidueField T') V) =
          (a ⊗ₜ[ResidueField T'] (1 : TrivSqZeroExt (ResidueField T') V)) * ((1 : ResidueField T' ⊗[T'] C) ⊗ₜ[ResidueField T'] TrivSqZeroExt.inr t.snd) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨t.snd, rfl⟩)
    | add y z hy hz =>
      rw [map_add, map_add]
      have : y + z - (Algebra.TensorProduct.includeLeftRingHom (aug T' V C y) + Algebra.TensorProduct.includeLeftRingHom (aug T' V C z)) =
          (y - Algebra.TensorProduct.includeLeftRingHom (aug T' V C y)) + (z - Algebra.TensorProduct.includeLeftRingHom (aug T' V C z)) := by
        abel
      rw [this]; exact J.add_mem hy hz
  have hxJ : x ∈ J := by simpa [hx] using hmem x
  refine ⟨2, ?_⟩
  rw [pow_two]
  have hxx : x * x ∈ J * J := Ideal.mul_mem_mul hxJ hxJ
  rw [hJ2] at hxx
  exact (Submodule.mem_bot _).mp hxx

end ZeroSectionAux

open ZeroSectionAux in
theorem solution
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T'))
    (u : Spec (CommRingCat.of C) ⟶ Y) (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (W : Ak.Opens) (aW : (W : Scheme.{u}) ⟶ Y)
    (haW : IsPullback aW (W.ι ≫ xk) qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (δ : letI := algebraOfHom xk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))) :
    letI := algebraOfHom xk Ue
    ∃ v : Spec (CommRingCat.of C) ⟶ Y,
      v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)) ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v ∧
      IsTangentCoordsOfPairAtVia I V ι C u v xk Lk W aW Ue
        (fun a => (δ : Γ(Ak, Ue) →ₗ[ResidueField T'] (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))) a) := by
  classical
  letI := algebraOfHom xk Ue

  obtain ⟨-, -, hsurj⟩ :=
    AlgebraicGeometry.SmallExtension.mem_pointDerivations_tangentCoords_and_injective_and_surjective V C xk
      (Lk.one (𝟙 _)).1 (Lk.one (𝟙 _)).2 Ue hUe e₁ he₁
  obtain ⟨w₁, hw₁k, hw₁0, hw₁c⟩ := hsurj δ

  have htoRed : ∀ t : T', (1 : ResidueField T') ⊗ₜ[T'] (algebraMap T' C t) = (residue T' t) ⊗ₜ[T'] (1 : C) := by
    intro t
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
      ResidueField.algebraMap_eq]
  let ukW : Spec (CommRingCat.of (ResidueField T' ⊗[T'] C)) ⟶ (W : Scheme.{u}) :=
    haW.lift (Spec.map (CommRingCat.ofHom (toReduction T' C)) ≫ u) (reductionBase T' C)
      (by rw [Category.assoc, hu, ← Spec.map_comp, ← CommRingCat.ofHom_comp, reductionBase, ← Spec.map_comp,
            ← CommRingCat.ofHom_comp]
          congr 2
          show (toReduction T' C).comp (algebraMap T' C) = _
          apply RingHom.ext; intro t
          show (1 : ResidueField T') ⊗ₜ[T'] (algebraMap T' C t) = (residue T' t) ⊗ₜ[T'] (1 : C)
          exact htoRed t)
  have huk1 : ukW ≫ aW = Spec.map (CommRingCat.ofHom (toReduction T' C)) ≫ u := haW.lift_fst _ _ _
  have huk2 : ukW ≫ W.ι ≫ xk = reductionBase T' C := haW.lift_snd _ _ _
  let uk : Spec (CommRingCat.of (ResidueField T' ⊗[T'] C)) ⟶ Ak := ukW ≫ W.ι
  have huk2' : uk ≫ xk = reductionBase T' C := by rw [Category.assoc]; exact huk2

  have hB : thickeningFst T' V C ≫ uk ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) := by
    rw [huk2']; exact (thickening_isPullback V C).w
  let Uk : SchemeHomOver (RelTangentPoints.base V (thickeningSnd T' V C)) xk :=
    ⟨thickeningFst T' V C ≫ uk, by rw [Category.assoc]; exact hB⟩
  let W₁ : SchemeHomOver (RelTangentPoints.base V (thickeningSnd T' V C)) xk := ⟨w₁ ≫ Ue.ι, hw₁k⟩
  let P₀ := Lk.mul (RelTangentPoints.base V (thickeningSnd T' V C)) Uk W₁

  have hzs := RelTangentPoints.zeroSection_base V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
    (thickening_isPullback V C)
  have hone : ∀ {T : Scheme.{u}} (τ : T ⟶ Spec (CommRingCat.of (ResidueField T'))),
      (Lk.one τ).1 = τ ≫ (Lk.one (𝟙 _)).1 := by
    intro T τ
    have := Lk.one_natural (𝟙 _) τ τ (Category.comp_id _)
    rw [← this, GoodReductionJacobian.schemeHomOverComp_coe]
  have hP₀zero : SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
      (thickening_isPullback V C) ≫ P₀.1 = uk := by
    have h1 := Lk.mul_natural _ _ (SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C)
      (thickeningSnd T' V C) (thickening_isPullback V C)) hzs Uk W₁
    have hU : GoodReductionJacobian.schemeHomOverComp _ hzs Uk = ⟨uk, huk2'⟩ := by
      apply Subtype.ext
      rw [GoodReductionJacobian.schemeHomOverComp_coe]
      show SquareZero.zeroSection V _ _ _ _ ≫ thickeningFst T' V C ≫ uk = uk
      rw [← Category.assoc, SquareZero.zeroSection_fst, Category.id_comp]
    have hW : GoodReductionJacobian.schemeHomOverComp _ hzs W₁ = Lk.one (reductionBase T' C) := by
      apply Subtype.ext
      rw [GoodReductionJacobian.schemeHomOverComp_coe, hone]
      exact hw₁0
    rw [hU, hW, Lk.mul_one] at h1
    have := congrArg Subtype.val h1
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
    exact this

  have hzsurj : Function.Surjective (SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
      (thickening_isPullback V C)).base := by
    rw [zeroSection_eq_specMap_aug]
    have haug : Function.Surjective (aug T' V C).toRingHom := fun y =>
      ⟨Algebra.TensorProduct.includeLeftRingHom y, by
        change aug T' V C (y ⊗ₜ 1) = y
        rw [aug_tmul, TrivSqZeroExt.fst_one, map_one, mul_one]⟩
    intro p
    have hp : p ∈ Set.range (PrimeSpectrum.comap (aug T' V C).toRingHom) := by
      rw [range_comap_of_surjective (R := thickening T' V C) (ResidueField T' ⊗[T'] C) (aug T' V C).toRingHom haug]
      exact fun x hx => nilpotent_iff_mem_prime.mp (isNilpotent_of_aug_eq_zero V C x hx) p.asIdeal p.isPrime
    obtain ⟨q, hq⟩ := hp
    exact ⟨q, hq⟩
  have hrange : Set.range P₀.1.base ⊆ Set.range W.ι.base := by
    rintro y ⟨p, rfl⟩
    obtain ⟨p', rfl⟩ := hzsurj p
    refine ⟨ukW.base p', ?_⟩
    change (ukW ≫ W.ι).base p' = (SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
      (thickening_isPullback V C) ≫ P₀.1).base p'
    rw [hP₀zero]
  let w₀ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (W : Scheme.{u}) := IsOpenImmersion.lift W.ι P₀.1 hrange
  have hw₀ι : w₀ ≫ W.ι = P₀.1 := IsOpenImmersion.lift_fac _ _ _
  have hzw₀ : SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
      (thickening_isPullback V C) ≫ w₀ = ukW := by
    rw [← cancel_mono W.ι, Category.assoc, hw₀ι, hP₀zero]

  have hw : SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
      (thickening_isPullback V C) ≫ w₀ ≫ aW = Spec.map (CommRingCat.ofHom (toReduction T' C)) ≫ u := by
    rw [← Category.assoc, hzw₀, huk1]
  have hwq : (w₀ ≫ aW) ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' (thickening T' V C))) := by
    rw [Category.assoc, haW.w, ← Category.assoc, ← Category.assoc w₀ W.ι xk, hw₀ι, P₀.2]
    show (thickeningSnd T' V C ≫ SquareZero.toBase (ResidueField T') V) ≫ _ = _
    rw [SquareZero.toBase, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun t => ?_)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes]
    simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, ResidueField.algebraMap_eq]
  obtain ⟨v, ⟨hv, huv, hpair⟩, -⟩ :=
    AlgebraicGeometry.SmallExtension.existsUnique_comp_eq_and_isTangentOfPair_of_flat_of_comp_eq I hI hsmall V ι hι hιI C
      qY u hu (w₀ ≫ aW) hw hwq
  refine ⟨v, hv, huv, ?_⟩

  have hw₀k : (w₀ ≫ W.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) := by rw [hw₀ι]; exact P₀.2
  refine ⟨w₀, hw₀k, w₁, hpair, ?_, ?_⟩
  · rw [RelTangentPoints.translate_coe]
    have hA : (⟨thickeningFst T' V C ≫ SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C)
        (thickeningSnd T' V C) (thickening_isPullback V C) ≫ w₀ ≫ W.ι, by
          rw [Category.assoc, Category.assoc, hw₀k, ← Category.assoc]
          exact RelTangentPoints.fst_zeroSection_base V (reductionBase T' C) (thickeningFst T' V C)
            (thickeningSnd T' V C) (thickening_isPullback V C)⟩ :
        SchemeHomOver (RelTangentPoints.base V (thickeningSnd T' V C)) xk) = Uk := by
      apply Subtype.ext
      show thickeningFst T' V C ≫ SquareZero.zeroSection V _ _ _ _ ≫ w₀ ≫ W.ι = thickeningFst T' V C ≫ uk
      rw [hw₀ι, hP₀zero]
    have hW : (⟨w₀ ≫ W.ι, hw₀k⟩ : SchemeHomOver (RelTangentPoints.base V (thickeningSnd T' V C)) xk) = P₀ := Subtype.ext hw₀ι
    rw [hA, hW]
    show (w₁ ≫ Ue.ι) = (Lk.mul _ (Lk.inv _ Uk) (Lk.mul _ Uk W₁)).1
    rw [← Lk.mul_assoc, Lk.inv_mul_cancel, Lk.one_mul]
  · funext a
    exact hw₁c a

end S_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAtVia_of_pointDerivations
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAtVia_of_pointDerivations (solution)
