-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.exists_mem_map_range_and_isFibreReading_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/a9199bcb-ed04-5e79-86fc-7d4a43ba26c8

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction

import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_exists_mem_map_range_and_isFibreReading_of_isAffineOpen

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u
open TensorProduct

theorem solution
    {B₁ : Type u} [CommRing B₁] [IsLocalRing B₁]
    (V : Type u) [AddCommGroup V] [Module (ResidueField B₁) V] [Module.Finite (ResidueField B₁) V]
    [Module B₁ V] [IsScalarTower B₁ (ResidueField B₁) V] (ι : V →ₗ[B₁] B₁)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of (ResidueField B₁))) (i : Xk ⟶ X)
    (hi : IsPullback i fk f (Spec.map (CommRingCat.ofHom (residue B₁))))
    (U : X.Opens) (hU : IsAffineOpen U) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) (hW' : i ⁻¹ᵁ U ≤ W)
    (w : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).obj W) :
    ∃ δ : Γ(X, U), (letI := algebraOfHom f U
      δ ∈ Ideal.map (algebraMap B₁ Γ(X, U)) (LinearMap.range ι)) ∧ IsFibreReading V ι f fk i U W hW δ w := by
  classical
  obtain rfl : W = i ⁻¹ᵁ U := le_antisymm hW hW'

  have hsurj : Function.Surjective (i.app U).hom := by
    have hi' : IsPullback i fk f (Spec.map (CommRingCat.ofHom (algebraMap B₁ (ResidueField B₁)))) := by
      rw [ResidueField.algebraMap_eq]; exact hi
    obtain ⟨-, hpo⟩ := Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback f fk i hi' U hU
    letI iA := f.sectionsAlgebra U
    letI iAk := fk.sectionsAlgebra (i ⁻¹ᵁ U)
    letI iT : Algebra Γ(X, U) Γ(Xk, i ⁻¹ᵁ U) := (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    letI iB : Algebra B₁ Γ(Xk, i ⁻¹ᵁ U) :=
      ((algebraMap (ResidueField B₁) Γ(Xk, i ⁻¹ᵁ U)).comp (algebraMap B₁ (ResidueField B₁))).toAlgebra
    haveI : IsScalarTower B₁ (ResidueField B₁) Γ(Xk, i ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

    have htop : (Spec.map (CommRingCat.ofHom (residue B₁))).appLE ⊤ ⊤ le_top =
        (Spec.map (CommRingCat.ofHom (residue B₁))).appTop := Scheme.Hom.appLE_eq_app _
    have hsq : ∀ b : B₁, algebraMap Γ(X, U) Γ(Xk, i ⁻¹ᵁ U) (algebraMap B₁ Γ(X, U) b) = algebraMap B₁ Γ(Xk, i ⁻¹ᵁ U) b := by
      intro b
      change (((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv ≫ f.appLE ⊤ U le_top) ≫ i.appLE U (i ⁻¹ᵁ U) le_rfl).hom b =
        ((CommRingCat.ofHom (residue B₁) ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B₁))).inv) ≫
          fk.appLE ⊤ (i ⁻¹ᵁ U) le_top).hom b
      congr 2
      rw [Category.assoc, Scheme.Hom.appLE_comp_appLE, Scheme.ΓSpecIso_inv_naturality, Category.assoc, ← htop,
        Scheme.Hom.appLE_comp_appLE]
      congr 1
      have key : ∀ {g₁ g₂ : Xk ⟶ Spec (CommRingCat.of B₁)} (h : g₁ = g₂)
          (p₁ : i ⁻¹ᵁ U ≤ g₁ ⁻¹ᵁ ⊤) (p₂ : i ⁻¹ᵁ U ≤ g₂ ⁻¹ᵁ ⊤), g₁.appLE ⊤ (i ⁻¹ᵁ U) p₁ = g₂.appLE ⊤ (i ⁻¹ᵁ U) p₂ := by
        rintro g₁ _ rfl p₁ p₂; rfl
      exact key hi.w _ _
    haveI : IsScalarTower B₁ Γ(X, U) Γ(Xk, i ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun b => (hsq b).symm)
    have hP : Algebra.IsPushout B₁ (ResidueField B₁) Γ(X, U) Γ(Xk, i ⁻¹ᵁ U) := hpo

    have key : ∀ z : ResidueField B₁ ⊗[B₁] Γ(X, U), ∃ s : Γ(X, U),
        algebraMap Γ(X, U) Γ(Xk, i ⁻¹ᵁ U) s = Algebra.IsPushout.equiv B₁ (ResidueField B₁) Γ(X, U) Γ(Xk, i ⁻¹ᵁ U) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | tmul a s =>
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
        refine ⟨algebraMap B₁ Γ(X, U) b * s, ?_⟩
        rw [Algebra.IsPushout.equiv_tmul, map_mul, hsq]
        rfl
      | add x y hx hy =>
        obtain ⟨s, hs⟩ := hx; obtain ⟨s', hs'⟩ := hy
        exact ⟨s + s', by rw [map_add, hs, hs', map_add]⟩
    intro y
    obtain ⟨s, hs⟩ := key ((Algebra.IsPushout.equiv B₁ (ResidueField B₁) Γ(X, U) Γ(Xk, i ⁻¹ᵁ U)).symm y)
    rw [AlgEquiv.apply_symm_apply] at hs
    refine ⟨s, ?_⟩
    rw [Scheme.Hom.app_eq_appLE]
    exact hs

  letI := algebraOfHom f U
  let bV := Module.finBasis (ResidueField B₁) V
  choose s hs using fun l : Fin (Module.finrank (ResidueField B₁) V) => hsurj (w (bV.dualBasis l))
  refine ⟨∑ l, algebraMap B₁ (X.presheaf.obj (Opposite.op U)) (ι (bV l)) * s l, ?_, ?_⟩
  · exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (LinearMap.mem_range.mpr ⟨bV l, rfl⟩))
  · refine ⟨_, bV, s, rfl, fun ξ => ?_⟩
    conv_lhs => rw [← bV.dualBasis.sum_repr ξ]
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, bV.dualBasis_repr ξ l, hs l, OModulePresheaf.res_refl_apply]

end S_AlgebraicGeometry_SmallExtension_exists_mem_map_range_and_isFibreReading_of_isAffineOpen
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_exists_mem_map_range_and_isFibreReading_of_isAffineOpen (solution)
