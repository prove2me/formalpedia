-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_comp_of_homOfLE_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/62608d1e-9b63-5fd0-a50c-3b8e60cbe2d3

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_homOfLE_comp_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover GoodReductionJacobian NeronModelInfra"

universe u

theorem solution
    {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (C : Type u) [CommRing C] [Algebra T' C]
    {Y Y' : Scheme.{u}} (ψ : Y ⟶ Y') (u v : Spec (CommRingCat.of C) ⟶ Y)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (W W' : Ak.Opens) (hWW : W ≤ W') (aW : (W : Scheme.{u}) ⟶ Y) (aW' : (W' : Scheme.{u}) ⟶ Y')
    (haW : Ak.homOfLE hWW ≫ aW' = aW ≫ ψ) (Ue : Ak.Opens)
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (hc : IsTangentCoordsOfPairAtVia I V ι C u v xk Lk W aW Ue c) :
    IsTangentCoordsOfPairAtVia I V ι C (u ≫ ψ) (v ≫ ψ) xk Lk W' aW' Ue c := by
  obtain ⟨w₀, hw₀, w₁, ⟨ϑ, hϑ, φ, hφ₁, hφ₂, hw⟩, hw₁, hc3⟩ := hc
  have e : (w₀ ≫ Ak.homOfLE hWW) ≫ W'.ι = w₀ ≫ W.ι := by
    rw [Category.assoc, Scheme.homOfLE_ι]
  have hw₀' : ((w₀ ≫ Ak.homOfLE hWW) ≫ W'.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) := by
    rw [e]; exact hw₀
  have htr : ∀ (w w' : Spec (CommRingCat.of (thickening T' V C)) ⟶ Ak) (h : w = w')
      (hw : w ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C))
      (hw' : w' ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C)),
      (RelTangentPoints.translate xk Lk V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
          (thickening_isPullback V C) w hw).1 =
        (RelTangentPoints.translate xk Lk V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
          (thickening_isPullback V C) w' hw').1 := by
    intro w w' h hw hw'; subst h; rfl
  refine ⟨w₀ ≫ Ak.homOfLE hWW, hw₀', w₁, ⟨ϑ, hϑ, φ ≫ ψ, ?_, ?_, ?_⟩, ?_, hc3⟩
  · rw [← Category.assoc, hφ₁]
  · rw [← Category.assoc, hφ₂]
  · rw [Category.assoc, haW, ← Category.assoc, hw, Category.assoc]
  · rw [hw₁]; exact htr _ _ e.symm hw₀ hw₀'

end S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_homOfLE_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_comp_of_homOfLE_comp_eq (solution)
