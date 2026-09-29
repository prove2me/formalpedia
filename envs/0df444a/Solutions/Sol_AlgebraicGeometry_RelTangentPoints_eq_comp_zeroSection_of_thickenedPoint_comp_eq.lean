-- Prove2me | solution 1 for AlgebraicGeometry.RelTangentPoints.eq_comp_zeroSection_of_thickenedPoint_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c4cab799-a85a-56e9-bf3c-17aaaece3cdd

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Theorems.Thm_AlgebraicGeometry_RelTangentPoints_const_bijective_of_bijective_of_compactSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelTangentPoints_eq_comp_zeroSection_of_thickenedPoint_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k x)
    (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V] [Module.Finite k V]
    {Z₀ Z : Scheme.{u}} [CompactSpace Z₀] [QuasiSeparatedSpace Z₀] (f₀ : Z₀ ⟶ Spec (CommRingCat.of k))
    (h₀ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f₀.appTop).hom)
    (q₁ : Z ⟶ Z₀) (q₂ : Z ⟶ SquareZero.spec k V) (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase k V))
    (w₀ : Z ⟶ X) (hw₀ : w₀ ≫ x = q₂ ≫ SquareZero.toBase k V)
    (y : Spec (CommRingCat.of k) ⟶ Z₀)
    (yZ : SquareZero.spec k V ⟶ Z) (hyZ₁ : yZ ≫ q₁ = SquareZero.toBase k V ≫ y) (hyZ₂ : yZ ≫ q₂ = 𝟙 _)
    (hconst : yZ ≫ w₀ = SquareZero.toBase k V ≫ y ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w₀) :
    w₀ = q₁ ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w₀ := by
  set B : Z ⟶ Spec (CommRingCat.of k) := q₂ ≫ SquareZero.toBase k V with hB
  have he : (L.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ x = 𝟙 _ := (L.one (𝟙 _)).2
  have hA : (q₁ ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w₀) ≫ x = B := by
    rw [Category.assoc, Category.assoc, hw₀, hB]
    simpa only [Category.assoc] using RelTangentPoints.fst_zeroSection_base V f₀ q₁ q₂ hZ
  set A : SchemeHomOver B x := ⟨q₁ ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w₀, hA⟩ with hAdef
  set W : SchemeHomOver B x := ⟨w₀, hw₀⟩ with hWdef

  set t := RelTangentPoints.translate x L V f₀ q₁ q₂ hZ w₀ hw₀ with htdef
  have ht1 : t.1 = (L.mul B (L.inv B A) W).1 := RelTangentPoints.translate_coe x L V f₀ q₁ q₂ hZ w₀ hw₀
  obtain ⟨t₀, ht₀⟩ :=
    (RelTangentPoints.const_bijective_of_bijective_of_compactSpace x (L.one (𝟙 _)).1 he V f₀ h₀ q₁ q₂ hZ).2 t

  have hψ : yZ ≫ B = SquareZero.toBase k V := by rw [hB, ← Category.assoc, hyZ₂, Category.id_comp]
  have hAW : schemeHomOverComp yZ hψ A = schemeHomOverComp yZ hψ W := by
    apply Subtype.ext
    rw [schemeHomOverComp_coe, schemeHomOverComp_coe]
    show yZ ≫ (q₁ ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w₀) = yZ ≫ w₀
    rw [← Category.assoc, hyZ₁, hconst, Category.assoc]
  have hrestr : schemeHomOverComp yZ hψ (L.mul B (L.inv B A) W) = L.one (SquareZero.toBase k V) := by
    rw [L.mul_natural, ← hAW, ← L.mul_natural, L.inv_mul_cancel, L.one_natural]
  have hone1 : ∀ (T : Scheme.{u}) (τ : T ⟶ Spec (CommRingCat.of k)),
      (L.one τ).1 = τ ≫ (L.one (𝟙 (Spec (CommRingCat.of k)))).1 := by
    intro T τ
    have := L.one_natural (𝟙 (Spec (CommRingCat.of k))) τ τ (Category.comp_id _)
    rw [← this, schemeHomOverComp_coe]
  have ht0 : t₀.1 = SquareZero.toBase k V ≫ (L.one (𝟙 (Spec (CommRingCat.of k)))).1 := by
    have e1 : yZ ≫ t.1 = t₀.1 := by
      rw [← ht₀, RelTangentPoints.const_coe, ← Category.assoc, hyZ₂, Category.id_comp]
    have e2 : yZ ≫ t.1 = (L.one (SquareZero.toBase k V)).1 := by
      rw [ht1, ← schemeHomOverComp_coe yZ hψ (L.mul B (L.inv B A) W), hrestr]
    rw [← e1, e2, hone1]
  have ht0' : t₀ = TangentPoints.zero x (L.one (𝟙 _)).1 he V :=
    TangentPoints.ext (by rw [ht0, TangentPoints.zero_coe])

  have hone : L.mul B (L.inv B A) W = L.one B := by
    apply Subtype.ext
    rw [← ht1, ← ht₀, RelTangentPoints.const_coe, ht0', TangentPoints.zero_coe, hone1 Z B]
    simp only [hB, Category.assoc]

  have hWA : W = A := by
    calc W = L.mul B A (L.mul B (L.inv B A) W) := by rw [← L.mul_assoc, L.mul_inv_cancel, L.one_mul]
      _ = L.mul B A (L.one B) := by rw [hone]
      _ = A := L.mul_one B A
  exact congrArg Subtype.val hWA

end S_AlgebraicGeometry_RelTangentPoints_eq_comp_zeroSection_of_thickenedPoint_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_RelTangentPoints_eq_comp_zeroSection_of_thickenedPoint_comp_eq (solution)
