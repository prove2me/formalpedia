-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAtVia_of_isPullback_of_comp_mono
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/71bdff76-85bb-5a0b-80c0-0272f1901e7a

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
import Theorems.Thm_AlgebraicGeometry_isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_of_isPullback_of_comp_mono

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover GoodReductionJacobian NeronModelInfra"

universe u

theorem solution
    {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (C : Type u) [CommRing C] [Algebra T' C]
    {Y Y₀ : Scheme.{u}} (j : Y₀ ⟶ Y) [Mono j] (u v : Spec (CommRingCat.of C) ⟶ Y₀)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (W W₀ : Ak.Opens) (h₀ : W₀ ≤ W) (aW : (W : Scheme.{u}) ⟶ Y) (aW₀ : (W₀ : Scheme.{u}) ⟶ Y₀)
    (hsq : IsPullback (Ak.homOfLE h₀) aW₀ aW j) (Ue : Ak.Opens)
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (hc : IsTangentCoordsOfPairAtVia I V ι C (u ≫ j) (v ≫ j) xk Lk W aW Ue c) :
    IsTangentCoordsOfPairAtVia I V ι C u v xk Lk W₀ aW₀ Ue c := by
  classical
  obtain ⟨w₀, hw₀, w₁, ⟨ϑ, hϑ, φ, hφ₁, hφ₂, hw⟩, hw₁, hc3⟩ := hc

  let q : CommRingCat.of C ⟶ CommRingCat.of (C ⧸ I.map (algebraMap T' C)) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))
  have H : IsPullback (CommRingCat.ofHom (pairFst I C)) (CommRingCat.ofHom (pairSnd I C)) q q :=
    IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit q q)
  have hI2 : I ^ 2 = ⊥ := by
    rw [pow_two]
    exact le_bot_iff.mp ((Ideal.mul_mono_right hI).trans hsmall.le)
  have hnil : ∀ x ∈ RingHom.ker q.hom, IsNilpotent x := by
    intro x hx
    have hx' : x ∈ I.map (algebraMap T' C) := by
      simpa [q, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hx
    refine ⟨2, ?_⟩
    have := Ideal.pow_mem_pow hx' 2
    rwa [← Ideal.map_pow, hI2, Ideal.map_bot, Ideal.mem_bot] at this
  have hsurj : Function.Surjective q.hom := Ideal.Quotient.mk_surjective
  have HP := AlgebraicGeometry.isPushout_specMap_of_isPullback_of_surjective_of_isNilpotent H hsurj hnil

  have huv : Spec.map q ≫ u = Spec.map q ≫ v := by
    rw [← cancel_mono j, Category.assoc, Category.assoc, ← hφ₁, ← hφ₂, ← Category.assoc, ← Category.assoc,
      ← Spec.map_comp, ← Spec.map_comp, H.w]
  have h1 : Spec.map (CommRingCat.ofHom (pairFst I C)) ≫ HP.desc u v huv = u := HP.inl_desc u v huv
  have h2 : Spec.map (CommRingCat.ofHom (pairSnd I C)) ≫ HP.desc u v huv = v := HP.inr_desc u v huv
  have hφ' : HP.desc u v huv ≫ j = φ := by
    apply HP.hom_ext
    · rw [← Category.assoc, h1, hφ₁]
    · rw [← Category.assoc, h2, hφ₂]

  have hland : w₀ ≫ aW = (Spec.map (CommRingCat.ofHom ϑ) ≫ HP.desc u v huv) ≫ j := by
    rw [hw, Category.assoc, hφ']
  let w₀' : Spec (CommRingCat.of (thickening T' V C)) ⟶ (W₀ : Scheme.{u}) := hsq.lift w₀ _ hland
  have hlift₁ : w₀' ≫ Ak.homOfLE h₀ = w₀ := hsq.lift_fst _ _ _
  have hlift₂ : w₀' ≫ aW₀ = Spec.map (CommRingCat.ofHom ϑ) ≫ HP.desc u v huv := hsq.lift_snd _ _ _
  have e : w₀' ≫ W₀.ι = w₀ ≫ W.ι := by
    rw [← hlift₁, Category.assoc, Scheme.homOfLE_ι]
  have hw₀' : (w₀' ≫ W₀.ι) ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C) := by
    rw [e]; exact hw₀
  have htr : ∀ (w w' : Spec (CommRingCat.of (thickening T' V C)) ⟶ Ak) (h : w = w')
      (hw : w ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C))
      (hw' : w' ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C)),
      (RelTangentPoints.translate xk Lk V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
          (thickening_isPullback V C) w hw).1 =
        (RelTangentPoints.translate xk Lk V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
          (thickening_isPullback V C) w' hw').1 := by
    intro w w' h hw hw'; subst h; rfl
  refine ⟨w₀', hw₀', w₁, ⟨ϑ, hϑ, HP.desc u v huv, h1, h2, hlift₂⟩, ?_, hc3⟩
  rw [hw₁]; exact htr _ _ e.symm hw₀ hw₀'

end S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_of_isPullback_of_comp_mono
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAtVia_of_isPullback_of_comp_mono (solution)
