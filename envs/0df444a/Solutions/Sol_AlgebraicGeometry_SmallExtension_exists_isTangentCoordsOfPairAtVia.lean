-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.exists_isTangentCoordsOfPairAtVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/51691188-7d8d-5671-a33d-0b037951c268

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAtVia
import Definitions.Def_Algebra_PointDerivations
import Theorems.Thm_AlgebraicGeometry_SmallExtension_existsUnique_isTangentOfPair_of_flat
import Theorems.Thm_AlgebraicGeometry_RelTangentPoints_existsUnique_comp_openInclusion_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAtVia

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
    (W : Ak.Opens) (aW : (W : Scheme.{u}) ⟶ Y)
    (haW : IsPullback aW (W.ι ≫ xk) qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (v : Spec (CommRingCat.of C) ⟶ Y)
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v) :
    ∃ c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)),
      IsTangentCoordsOfPairAtVia I V ι C u v xk Lk W aW Ue c := by
  classical

  obtain ⟨w, hw, -⟩ := existsUnique_isTangentOfPair_of_flat I hI hsmall V ι hι hιI C qY u hu v hv huv

  have hwq : w ≫ qY = RelTangentPoints.base V (thickeningSnd T' V C) ≫ Spec.map (CommRingCat.ofHom (residue T')) := by
    obtain ⟨ϑ, hϑ, φ, hφ₁, hφ₂, hwφ⟩ := hw
    set ψ : CommRingCat.of T' ⟶ CommRingCat.of (pairRing I C) := Spec.preimage (φ ≫ qY) with hψ
    have hψmap : Spec.map ψ = φ ≫ qY := Spec.map_preimage _
    have hψ1 : ∀ t : T', ((ψ.hom t : pairRing I C) : C × C).1 = algebraMap T' C t := by
      intro t
      have h : ψ ≫ CommRingCat.ofHom (pairFst I C) = CommRingCat.ofHom (algebraMap T' C) := by
        apply Spec.map_injective
        rw [Spec.map_comp, hψmap, ← Category.assoc, hφ₁, hu]
      exact congrArg (fun f : CommRingCat.of T' ⟶ CommRingCat.of C => f.hom t) h
    have hψ2 : ∀ t : T', ((ψ.hom t : pairRing I C) : C × C).2 = algebraMap T' C t := by
      intro t
      have h : ψ ≫ CommRingCat.ofHom (pairSnd I C) = CommRingCat.ofHom (algebraMap T' C) := by
        apply Spec.map_injective
        rw [Spec.map_comp, hψmap, ← Category.assoc, hφ₂, hv]
      exact congrArg (fun f : CommRingCat.of T' ⟶ CommRingCat.of C => f.hom t) h
    have hmem : ∀ t : T', (algebraMap T' C t, algebraMap T' C t) ∈ pairRing I C := fun t => by
      rw [mem_pairRing]
    have hψt : ∀ t : T', ψ.hom t = ⟨(algebraMap T' C t, algebraMap T' C t), hmem t⟩ := by
      intro t
      apply Subtype.ext
      exact Prod.ext (hψ1 t) (hψ2 t)
    have hring : ψ ≫ CommRingCat.ofHom ϑ
        = CommRingCat.ofHom (residue T') ≫ CommRingCat.ofHom (algebraMap (ResidueField T') (TrivSqZeroExt (ResidueField T') V)) ≫
          CommRingCat.ofHom (R := TrivSqZeroExt (ResidueField T') V) (S := thickening T' V C)
            (Algebra.TensorProduct.includeRight (R := ResidueField T') (A := ResidueField T' ⊗[T'] C)
              (B := TrivSqZeroExt (ResidueField T') V)).toRingHom := by
      apply CommRingCat.hom_ext
      ext t
      change ϑ (ψ.hom t) = Algebra.TensorProduct.includeRight (algebraMap (ResidueField T') (TrivSqZeroExt (ResidueField T') V) (residue T' t))
      rw [hψt t, hϑ.1 (algebraMap T' C t) (hmem t), Algebra.TensorProduct.includeRight_apply, toReduction]
      change (Algebra.TensorProduct.includeRight (R := T') (A := ResidueField T') (B := C)) (algebraMap T' C t) ⊗ₜ[ResidueField T'] (1 : TrivSqZeroExt (ResidueField T') V)
        = (1 : ResidueField T' ⊗[T'] C) ⊗ₜ[ResidueField T'] algebraMap (ResidueField T') (TrivSqZeroExt (ResidueField T') V) (residue T' t)
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        ← TensorProduct.smul_tmul']
      congr 1
    calc w ≫ qY = Spec.map (CommRingCat.ofHom ϑ) ≫ φ ≫ qY := by rw [hwφ, Category.assoc]
      _ = Spec.map (ψ ≫ CommRingCat.ofHom ϑ) := by rw [Spec.map_comp, hψmap]
      _ = _ := by
        rw [hring, Spec.map_comp, Spec.map_comp, Category.assoc]
        rfl

  let w₀ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (W : Scheme.{u}) :=
    haW.lift w (RelTangentPoints.base V (thickeningSnd T' V C)) hwq
  have hw₀ : (w₀ ≫ W.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) := by
    rw [Category.assoc]; exact haW.lift_snd _ _ _
  have hw₀a : w₀ ≫ aW = w := haW.lift_fst _ _ _

  let tr := RelTangentPoints.translate xk Lk V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
    (thickening_isPullback V C) (w₀ ≫ W.ι) hw₀
  obtain ⟨w₁, hw₁, -⟩ := RelTangentPoints.existsUnique_comp_openInclusion_eq xk (Lk.one (𝟙 _)).1 V
    (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C) tr Ue e₁ he₁
  exact ⟨_, w₀, hw₀, w₁, (by rw [hw₀a]; exact hw), hw₁, rfl⟩

end S_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAtVia
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAtVia (solution)
