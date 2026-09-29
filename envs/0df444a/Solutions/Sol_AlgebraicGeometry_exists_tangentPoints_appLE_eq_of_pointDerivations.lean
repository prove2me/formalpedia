-- Prove2me | solution 1 for AlgebraicGeometry.exists_tangentPoints_appLE_eq_of_pointDerivations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/09dd5eee-40ce-584d-83f8-b7a14f4676ef

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_tangentPoints_appLE_eq_of_pointDerivations

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

namespace TangentFromDerivation

section Plumbing

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

theorem appLE_specMap_fromSpec {S : CommRingCat.{u}} (θ : Γ(X, U) ⟶ S)
    (h : ⊤ ≤ (Spec.map θ ≫ hU.fromSpec) ⁻¹ᵁ U) :
    (Spec.map θ ≫ hU.fromSpec).appLE U ⊤ h ≫ (Scheme.ΓSpecIso S).hom = θ := by
  have h1 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [IsAffineOpen.fromSpec_preimage_self]
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map θ) hU.fromSpec U ⊤ ⊤ h1 le_top]
  have h2 : hU.fromSpec.appLE U ⊤ h1 = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact ((Spec Γ(X, U)).presheaf.congr_map (Subsingleton.elim _ _)).trans
      ((Spec Γ(X, U)).presheaf.map_id _)
  have h3 : (Spec.map θ).appLE ⊤ ⊤ le_top = (Spec.map θ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [h2, h3, Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

theorem le_preimage_specMap_fromSpec {S : CommRingCat.{u}} (θ : Γ(X, U) ⟶ S) :
    ⊤ ≤ (Spec.map θ ≫ hU.fromSpec) ⁻¹ᵁ U := by
  rw [Scheme.Hom.comp_preimage, IsAffineOpen.fromSpec_preimage_self]
  exact le_top

end Plumbing

section RingMap

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A] (ev : A →+* K)
  (M : Type u) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
  (D : ↥(Algebra.PointDerivations K A ev M))

def θ : A →+* TrivSqZeroExt K M where
  toFun r := TrivSqZeroExt.inl (ev r) + TrivSqZeroExt.inr (D.1 r)
  map_one' := by
    apply TrivSqZeroExt.ext <;>
      simp [Algebra.PointDerivations.apply_one D.2]
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, TrivSqZeroExt.snd_mul,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, map_mul]
      rw [Algebra.PointDerivations.apply_mul D.2 a b, op_smul_eq_smul, add_comm]
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_add' a b := by
    apply TrivSqZeroExt.ext <;> simp [add_add_add_comm]

@[scoped simp] theorem θ_apply (r : A) : θ ev M D r = TrivSqZeroExt.inl (ev r) + TrivSqZeroExt.inr (D.1 r) := rfl

theorem fst_θ (r : A) : (θ ev M D r).fst = ev r := by simp

theorem fstHom_comp_θ : (TrivSqZeroExt.fstHom K K M).toRingHom.comp (θ ev M D) = ev := by
  ext r; exact fst_θ ev M D r

theorem θ_comp_algebraMap (hev : ∀ c : K, ev (algebraMap K A c) = c) :
    (θ ev M D).comp (algebraMap K A) = algebraMap K (TrivSqZeroExt K M) := by
  ext c
  · simp [hev, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [Algebra.PointDerivations.apply_algebraMap D.2, TrivSqZeroExt.algebraMap_eq_inl]

end RingMap

end TangentFromDerivation
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_tangentPoints_appLE_eq_of_pointDerivations.TangentFromDerivation"

open TangentFromDerivation in
theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    (U : X.Opens) (hU : IsAffineOpen U)
    (eP : Spec (CommRingCat.of K) ⟶ (U : Scheme.{u})) (heP : eP ≫ U.ι ≫ x = 𝟙 _)
    (M : Type u) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
    (D : letI := algebraOfHom x U
      ↥(Algebra.PointDerivations K Γ(X, U) ((U.topIso.inv ≫ eP.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom) M)) :
    ∃ (v : TangentPoints x (eP ≫ U.ι) M) (hv : ⊤ ≤ v.1 ⁻¹ᵁ U),
      ∀ r : Γ(X, U),
        (v.1.appLE U ⊤ hv ≫ (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt K M))).hom).hom r =
          TrivSqZeroExt.inl ((U.topIso.inv ≫ eP.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom r) +
            TrivSqZeroExt.inr (D.1 r) := by
  letI : Algebra K Γ(X, U) := algebraOfHom x U
  let ev : Γ(X, U) →+* K := (U.topIso.inv ≫ eP.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom

  have hfx : hU.fromSpec ≫ x = Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, U))) := by
    have := IsAffineOpen.SpecMap_appLE_fromSpec x (isAffineOpen_top _) hU (le_top : U ≤ x ⁻¹ᵁ ⊤)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at this
    exact this.symm

  have hι : ⊤ ≤ (eP ≫ U.ι) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]
    exact le_top
  have hePι : eP ≫ U.ι = Spec.map ((eP ≫ U.ι).appLE U ⊤ hι ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom) ≫ hU.fromSpec := by
    have := IsAffineOpen.SpecMap_appLE_fromSpec (eP ≫ U.ι) hU (isAffineOpen_top _) hι
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
    rw [Spec.map_comp, Category.assoc, this, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]
  have happ : (eP ≫ U.ι).appLE U ⊤ hι = U.topIso.inv ≫ eP.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE eP U.ι U ⊤ ⊤ (by rw [Scheme.Opens.ι_preimage_self]) le_top]
    congr 1
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  have hev_hom : CommRingCat.ofHom ev = (eP ≫ U.ι).appLE U ⊤ hι ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    rw [happ, Category.assoc]; rfl
  have hePι' : eP ≫ U.ι = Spec.map (CommRingCat.ofHom ev) ≫ hU.fromSpec := by rw [hev_hom]; exact hePι

  have hev : ∀ c : K, ev (algebraMap K Γ(X, U) c) = c := by
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, U)) ≫ CommRingCat.ofHom ev) = Spec.map (𝟙 _) := by
      rw [Spec.map_comp, Spec.map_id, ← hfx, ← Category.assoc, ← hePι', Category.assoc, heP]
    have h2 := Spec.map_injective h1
    intro c
    have := congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of K => f.hom c) h2
    simpa using this

  let v₀ : SquareZero.spec K M ⟶ X := Spec.map (CommRingCat.ofHom (θ ev M D)) ≫ hU.fromSpec
  have hx' : v₀ ≫ x = SquareZero.toBase K M := by
    simp only [v₀, Category.assoc]
    rw [hfx, ← Spec.map_comp, ← CommRingCat.ofHom_comp, θ_comp_algebraMap ev M D hev]
    rfl
  have hb' : SquareZero.basePoint K M ≫ v₀ = eP ≫ U.ι := by
    rw [hePι']
    simp only [v₀, SquareZero.basePoint, ← Category.assoc, ← Spec.map_comp]
    congr 2
    rw [← CommRingCat.ofHom_comp, fstHom_comp_θ]
  refine ⟨⟨v₀, hx', hb'⟩, le_preimage_specMap_fromSpec hU (CommRingCat.ofHom (θ ev M D)), fun r => ?_⟩
  have := appLE_specMap_fromSpec hU (CommRingCat.ofHom (θ ev M D))
    (le_preimage_specMap_fromSpec hU (CommRingCat.ofHom (θ ev M D)))
  change ((Spec.map (CommRingCat.ofHom (θ ev M D)) ≫ hU.fromSpec).appLE U ⊤ _ ≫
    (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt K M))).hom).hom r = _
  rw [this]
  rfl

end S_AlgebraicGeometry_exists_tangentPoints_appLE_eq_of_pointDerivations
end P2MW
export P2MW.S_AlgebraicGeometry_exists_tangentPoints_appLE_eq_of_pointDerivations (solution)
