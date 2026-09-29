-- Prove2me | solution 1 for AlgebraicGeometry.RelTangentPoints.comp_translate_eq_translate_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/f4fc914c-658a-53c2-8cac-ffe4c79b19a2

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelTangentPoints_comp_translate_eq_translate_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

namespace TNAux

theorem inv_natural {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (a : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (G.inv t a) = G.inv t' (schemeHomOverComp ψ hψ a) := by
  have hprod : G.mul t' (schemeHomOverComp ψ hψ (G.inv t a)) (schemeHomOverComp ψ hψ a) = G.one t' := by
    rw [← G.mul_natural, G.inv_mul_cancel, G.one_natural]
  calc schemeHomOverComp ψ hψ (G.inv t a)
      = G.mul t' (schemeHomOverComp ψ hψ (G.inv t a)) (G.one t') := (G.mul_one t' _).symm
    _ = G.mul t' (schemeHomOverComp ψ hψ (G.inv t a))
          (G.mul t' (schemeHomOverComp ψ hψ a) (G.inv t' (schemeHomOverComp ψ hψ a))) := by rw [G.mul_inv_cancel]
    _ = G.mul t' (G.one t') (G.inv t' (schemeHomOverComp ψ hψ a)) := by rw [← G.mul_assoc, hprod]
    _ = G.inv t' (schemeHomOverComp ψ hψ a) := G.one_mul t' _

end TNAux

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k x)
    (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    (V' : Type u) [AddCommGroup V'] [Module k V'] [Module kᵐᵒᵖ V'] [IsCentralScalar k V']
    {Z₀ Z Z₀' Z' : Scheme.{u}} (f₀ : Z₀ ⟶ Spec (CommRingCat.of k)) (f₀' : Z₀' ⟶ Spec (CommRingCat.of k))
    (q₁ : Z ⟶ Z₀) (q₂ : Z ⟶ SquareZero.spec k V) (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase k V))
    (q₁' : Z' ⟶ Z₀') (q₂' : Z' ⟶ SquareZero.spec k V') (hZ' : IsPullback q₁' q₂' f₀' (SquareZero.toBase k V'))
    (g₀ : Z₀ ⟶ Z₀') (hg₀f : g₀ ≫ f₀' = f₀)
    (g : Z ⟶ Z') (hg₁ : g ≫ q₁' = q₁ ≫ g₀)
    (hg₀ : SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ g = g₀ ≫ SquareZero.zeroSection V' f₀' q₁' q₂' hZ')
    (w' : Z' ⟶ X) (hw' : w' ≫ x = RelTangentPoints.base V' q₂')
    (w : Z ⟶ X) (hw : w ≫ x = RelTangentPoints.base V q₂) (hgw : g ≫ w' = w) :
    g ≫ (RelTangentPoints.translate x L V' f₀' q₁' q₂' hZ' w' hw').1 =
      (RelTangentPoints.translate x L V f₀ q₁ q₂ hZ w hw).1 := by

  have hgb : g ≫ RelTangentPoints.base V' q₂' = RelTangentPoints.base V q₂ := by
    rw [← hw', ← Category.assoc, hgw, hw]
  show g ≫ (L.mul (RelTangentPoints.base V' q₂') (L.inv (RelTangentPoints.base V' q₂') _) ⟨w', hw'⟩).1 =
    (L.mul (RelTangentPoints.base V q₂) (L.inv (RelTangentPoints.base V q₂) _) ⟨w, hw⟩).1
  rw [← schemeHomOverComp_coe g hgb, L.mul_natural, TNAux.inv_natural]
  congr 2
  · congr 1
    apply Subtype.ext
    rw [schemeHomOverComp_coe, ← Category.assoc, hg₁, Category.assoc, ← Category.assoc g₀, ← hg₀, Category.assoc, hgw]
  · apply Subtype.ext
    rw [schemeHomOverComp_coe, hgw]

end S_AlgebraicGeometry_RelTangentPoints_comp_translate_eq_translate_comp
end P2MW
export P2MW.S_AlgebraicGeometry_RelTangentPoints_comp_translate_eq_translate_comp (solution)
