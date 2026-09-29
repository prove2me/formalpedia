-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.eq_of_isTangentCoordsOfPairAtVia_of_isTangentCoordsOfPairAtVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/4178b1ac-f69f-5f4f-934e-fc67a9d3f383

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
import Theorems.Thm_AlgebraicGeometry_SmallExtension_IsTangentOfPair_zeroSection_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_eq_of_isTangentCoordsOfPairAtVia_of_isTangentCoordsOfPairAtVia

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover GoodReductionJacobian NeronModelInfra"

universe u

theorem DetAux.cancel {k : Type u} [Field k] {X : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k x)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (A A' W W' : SchemeHomOver t x)
    (h : L.mul t (L.inv t A) W = L.mul t (L.inv t A') W') (hA : A.1 = A'.1) : W.1 = W'.1 := by
  obtain rfl : A = A' := Subtype.ext hA
  have : W = W' := by
    calc W = L.mul t (L.one t) W := (L.one_mul t W).symm
      _ = L.mul t (L.mul t A (L.inv t A)) W := by rw [L.mul_inv_cancel]
      _ = L.mul t A (L.mul t (L.inv t A) W) := L.mul_assoc t _ _ _
      _ = L.mul t A (L.mul t (L.inv t A) W') := by rw [h]
      _ = W' := by rw [← L.mul_assoc, L.mul_inv_cancel, L.one_mul]
  exact congrArg Subtype.val this

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
    (v v' : Spec (CommRingCat.of C) ⟶ Y)
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hv' : v' ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v)
    (huv' : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v')
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (h : IsTangentCoordsOfPairAtVia I V ι C u v xk Lk W aW Ue c)
    (h' : IsTangentCoordsOfPairAtVia I V ι C u v' xk Lk W aW Ue c) :
    v = v' := by
  obtain ⟨w₀, hw₀, w₁, hT, hw₁, hc⟩ := h
  obtain ⟨w₀', hw₀', w₁', hT', hw₁', hc'⟩ := h'
  have hZ0 := AlgebraicGeometry.SmallExtension.IsTangentOfPair.zeroSection_comp_eq I V ι hιI C u v (w₀ ≫ aW) hT
  have hZ0' := AlgebraicGeometry.SmallExtension.IsTangentOfPair.zeroSection_comp_eq I V ι hιI C u v' (w₀' ≫ aW) hT'

  have key := (AlgebraicGeometry.SmallExtension.mem_pointDerivations_tangentCoords_and_injective_and_surjective V C xk
      (Lk.one (𝟙 _)).1 (Lk.one (𝟙 _)).2 Ue hUe e₁ he₁).2.1
  have hw₁eq : w₁ = w₁' := by
    refine key w₁ w₁' ?_ ?_ ?_ ?_ ?_
    · rw [hw₁]; exact (RelTangentPoints.translate xk Lk V _ _ _ _ (w₀ ≫ W.ι) hw₀).2.1
    · rw [hw₁]; exact (RelTangentPoints.translate xk Lk V _ _ _ _ (w₀ ≫ W.ι) hw₀).2.2
    · rw [hw₁']; exact (RelTangentPoints.translate xk Lk V _ _ _ _ (w₀' ≫ W.ι) hw₀').2.1
    · rw [hw₁']; exact (RelTangentPoints.translate xk Lk V _ _ _ _ (w₀' ≫ W.ι) hw₀').2.2
    · rw [← hc, ← hc']

  have hzw0 : SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C) ≫ w₀ =
      SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C) ≫ w₀' := by
    apply haW.hom_ext
    · rw [Category.assoc, Category.assoc, hZ0, hZ0']
    · rw [Category.assoc, Category.assoc, ← Category.assoc w₀, ← Category.assoc w₀', hw₀, hw₀']
  have hzw : SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C) ≫ w₀ ≫ W.ι =
      SquareZero.zeroSection V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C) ≫ w₀' ≫ W.ι := by
    rw [← Category.assoc, hzw0, Category.assoc]

  have htr : (RelTangentPoints.translate xk Lk V _ _ _ (thickening_isPullback V C) (w₀ ≫ W.ι) hw₀).1 =
      (RelTangentPoints.translate xk Lk V _ _ _ (thickening_isPullback V C) (w₀' ≫ W.ι) hw₀').1 := by
    rw [← hw₁, ← hw₁', hw₁eq]
  rw [RelTangentPoints.translate_coe, RelTangentPoints.translate_coe] at htr
  have hw₀ι : w₀ ≫ W.ι = w₀' ≫ W.ι :=
    DetAux.cancel Lk _ _ _ _ _ (Subtype.ext htr) (congrArg (fun t => thickeningFst T' V C ≫ t) hzw)
  have hw₀eq : w₀ = w₀' := by rw [← cancel_mono W.ι]; exact hw₀ι

  have hbase : RelTangentPoints.base V (thickeningSnd T' V C) ≫ Spec.map (CommRingCat.ofHom (residue T')) =
      Spec.map (CommRingCat.ofHom (algebraMap T' (thickening T' V C))) := by
    rw [RelTangentPoints.base, thickeningSnd, SquareZero.toBase, Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun t => ?_
    change Algebra.TensorProduct.includeRight (algebraMap (ResidueField T') (TrivSqZeroExt (ResidueField T') V) (residue T' t)) =
      algebraMap T' (thickening T' V C) t
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply T' (ResidueField T') (thickening T' V C)]
    rfl
  have hwq : (w₀ ≫ aW) ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' (thickening T' V C))) := by
    rw [Category.assoc, haW.w, ← Category.assoc, ← Category.assoc w₀ W.ι xk, hw₀, hbase]
  have huniq := AlgebraicGeometry.SmallExtension.existsUnique_comp_eq_and_isTangentOfPair_of_flat_of_comp_eq I hI hsmall V ι hι hιI
    C qY u hu (w₀ ≫ aW) hZ0 hwq
  exact huniq.unique ⟨hv, huv, hT⟩ ⟨hv', huv', by rw [hw₀eq]; exact hT'⟩

end S_AlgebraicGeometry_SmallExtension_eq_of_isTangentCoordsOfPairAtVia_of_isTangentCoordsOfPairAtVia
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_eq_of_isTangentCoordsOfPairAtVia_of_isTangentCoordsOfPairAtVia (solution)
