-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAt_of_pointDerivations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/c9094fcd-d027-5b9c-8df1-786a675dc030

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
import Theorems.Thm_AlgebraicGeometry_SmallExtension_mem_pointDerivations_tangentCoords_and_injective_and_surjective
import Theorems.Thm_AlgebraicGeometry_SmallExtension_existsUnique_comp_eq_and_isTangentOfPair_of_flat_of_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAt_of_pointDerivations

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover GoodReductionJacobian NeronModelInfra"

universe u

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
    (ak : Ak ⟶ Y) (hak : IsPullback ak xk qY (Spec.map (CommRingCat.ofHom (residue T'))))
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
      IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue
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
  let uk : Spec (CommRingCat.of (ResidueField T' ⊗[T'] C)) ⟶ Ak :=
    hak.lift (Spec.map (CommRingCat.ofHom (toReduction T' C)) ≫ u) (reductionBase T' C)
      (by rw [Category.assoc, hu, ← Spec.map_comp, ← CommRingCat.ofHom_comp, reductionBase, ← Spec.map_comp,
            ← CommRingCat.ofHom_comp]
          congr 2
          show (toReduction T' C).comp (algebraMap T' C) = _
          apply RingHom.ext; intro t
          show (1 : ResidueField T') ⊗ₜ[T'] (algebraMap T' C t) = (residue T' t) ⊗ₜ[T'] (1 : C)
          exact htoRed t)
  have huk1 : uk ≫ ak = Spec.map (CommRingCat.ofHom (toReduction T' C)) ≫ u := hak.lift_fst _ _ _
  have huk2 : uk ≫ xk = reductionBase T' C := hak.lift_snd _ _ _

  have hB : thickeningFst T' V C ≫ uk ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) := by
    rw [huk2]; exact (thickening_isPullback V C).w
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
    rw [← this, schemeHomOverComp_coe]
  have hP₀zero : SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
      (thickening_isPullback V C) ≫ P₀.1 = uk := by
    have h1 := Lk.mul_natural _ _ (SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C)
      (thickeningSnd T' V C) (thickening_isPullback V C)) hzs Uk W₁
    have hU : schemeHomOverComp _ hzs Uk = ⟨uk, huk2⟩ := by
      apply Subtype.ext
      rw [schemeHomOverComp_coe]
      show SquareZero.zeroSection V _ _ _ _ ≫ thickeningFst T' V C ≫ uk = uk
      rw [← Category.assoc, SquareZero.zeroSection_fst, Category.id_comp]
    have hW : schemeHomOverComp _ hzs W₁ = Lk.one (reductionBase T' C) := by
      apply Subtype.ext
      rw [schemeHomOverComp_coe, hone]
      exact hw₁0
    rw [hU, hW, Lk.mul_one] at h1
    have := congrArg Subtype.val h1
    rw [schemeHomOverComp_coe] at this
    exact this

  have hw : SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
      (thickening_isPullback V C) ≫ P₀.1 ≫ ak = Spec.map (CommRingCat.ofHom (toReduction T' C)) ≫ u := by
    rw [← Category.assoc, hP₀zero, huk1]
  have hwq : (P₀.1 ≫ ak) ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' (thickening T' V C))) := by
    rw [Category.assoc, hak.w, ← Category.assoc, P₀.2]
    show (thickeningSnd T' V C ≫ SquareZero.toBase (ResidueField T') V) ≫ _ = _
    rw [SquareZero.toBase, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun t => ?_)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes]
    simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, ResidueField.algebraMap_eq]
  obtain ⟨v, ⟨hv, huv, hpair⟩, -⟩ :=
    AlgebraicGeometry.SmallExtension.existsUnique_comp_eq_and_isTangentOfPair_of_flat_of_comp_eq I hI hsmall V ι hι hιI C
      qY u hu (P₀.1 ≫ ak) hw hwq
  refine ⟨v, hv, huv, ?_⟩

  refine ⟨P₀.1, P₀.2, w₁, hpair, ?_, ?_⟩
  · rw [RelTangentPoints.translate_coe]
    have hA : (⟨thickeningFst T' V C ≫ SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C)
        (thickeningSnd T' V C) (thickening_isPullback V C) ≫ P₀.1, by
          rw [Category.assoc, Category.assoc, P₀.2, ← Category.assoc]
          exact RelTangentPoints.fst_zeroSection_base V (reductionBase T' C) (thickeningFst T' V C)
            (thickeningSnd T' V C) (thickening_isPullback V C)⟩ :
        SchemeHomOver (RelTangentPoints.base V (thickeningSnd T' V C)) xk) = Uk := by
      apply Subtype.ext
      show thickeningFst T' V C ≫ SquareZero.zeroSection V _ _ _ _ ≫ P₀.1 = thickeningFst T' V C ≫ uk
      rw [hP₀zero]
    have hW : (⟨P₀.1, P₀.2⟩ : SchemeHomOver (RelTangentPoints.base V (thickeningSnd T' V C)) xk) = P₀ := rfl
    rw [hA, hW]
    show (w₁ ≫ Ue.ι) = (Lk.mul _ (Lk.inv _ Uk) (Lk.mul _ Uk W₁)).1
    rw [← Lk.mul_assoc, Lk.inv_mul_cancel, Lk.one_mul]
  · funext a
    exact hw₁c a

end S_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAt_of_pointDerivations
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAt_of_pointDerivations (solution)
