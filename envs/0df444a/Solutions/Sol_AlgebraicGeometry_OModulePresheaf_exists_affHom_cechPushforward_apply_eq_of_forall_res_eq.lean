-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_affHom_cechPushforward_apply_eq_of_forall_res_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3f13c743-0aa1-59e6-a139-cc438f398ef9

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_apply_eq_of_forall_res_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem solution
    {A : Type u} [CommRing A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsSeparated q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsSeparated p] (K' : V'.OrderedAffineCover)
    (F : OModulePresheaf q) (F' : OModulePresheaf (p ≫ q))
    (η : ∀ (U : P.affineOpens) (V : V'.affineOpens), V.1 ≤ p ⁻¹ᵁ U.1 → (F.obj U.1 →ₗ[A] F'.obj V.1))
    (hηs : ∀ (U : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ p ⁻¹ᵁ U.1) (a : Γ(P, U.1)) (x : F.obj U.1),
      η U V h (a • x) = (p.appLE U.1 V.1 h).hom a • η U V h x)
    (hηV : ∀ (U : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ p ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p ⁻¹ᵁ U.1)
      (hV : V₁.1 ≤ V₂.1) (x : F.obj U.1), F'.res hV (η U V₂ h₂ x) = η U V₁ h₁ x)
    (hηU : ∀ (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ p ⁻¹ᵁ U₁.1) (h₂ : V.1 ≤ p ⁻¹ᵁ U₂.1)
      (hU : U₁.1 ≤ U₂.1) (x : F.obj U₂.1), η U₂ V h₂ x = η U₁ V h₁ (F.res hU x)) :
    ∃ v : OModulePresheaf.AffHom F (OModulePresheaf.cechPushforward p q K' F'),
      ∀ (U : P.affineOpens) (x : F.obj U.1) (j : K'.ι),
        (v.app U x).1 j = η U (OModulePresheaf.AffHom.affineChart p q K' U j)
          (OModulePresheaf.cechPushforward.chart_le_preimage p K' U.1 j) x := by
  classical

  have hij : ∀ (U : P.affineOpens) (i j : K'.ι),
      IsAffineOpen (OModulePresheaf.cechPushforward.chart p K' U.1 i ⊓ OModulePresheaf.cechPushforward.chart p K' U.1 j) :=
    fun U i j =>
      haveI : IsSeparated (p ≫ q) := inferInstance
      Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated (p ≫ q)
        (OModulePresheaf.AffHom.affineChart p q K' U i).2 (OModulePresheaf.AffHom.affineChart p q K' U j).2
  refine ⟨
    { app := fun U =>
        { toFun := fun x => ⟨fun j => η U (OModulePresheaf.AffHom.affineChart p q K' U j)
              (OModulePresheaf.cechPushforward.chart_le_preimage p K' U.1 j) x, ?_⟩,
          map_add' := fun x y => Subtype.ext (funext fun j => map_add _ x y),
          map_smul' := fun r x => Subtype.ext (funext fun j => LinearMap.map_smul _ r x) },
      app_smul := fun U a x => Subtype.ext (funext fun j => ?_),
      naturality := fun {U} {U'} h => LinearMap.ext fun x => Subtype.ext (funext fun j => ?_) },
    fun U x j => rfl⟩
  ·
    rw [OModulePresheaf.cechPushforward.mem_cocycles_iff]
    intro i j
    have h₁ : (OModulePresheaf.cechPushforward.chart p K' U.1 i ⊓ OModulePresheaf.cechPushforward.chart p K' U.1 j) ≤ p ⁻¹ᵁ U.1 :=
      inf_le_left.trans (OModulePresheaf.cechPushforward.chart_le_preimage p K' U.1 i)
    rw [hηV U ⟨_, hij U i j⟩ (OModulePresheaf.AffHom.affineChart p q K' U i) h₁ _ inf_le_left x,
      hηV U ⟨_, hij U i j⟩ (OModulePresheaf.AffHom.affineChart p q K' U j) h₁ _ inf_le_right x]
  ·
    show η U (OModulePresheaf.AffHom.affineChart p q K' U j) (OModulePresheaf.cechPushforward.chart_le_preimage p K' U.1 j) (a • x) =
      (OModulePresheaf.cechPushforward.toChart p K' U.1 j).hom a •
        η U (OModulePresheaf.AffHom.affineChart p q K' U j) (OModulePresheaf.cechPushforward.chart_le_preimage p K' U.1 j) x
    exact hηs U _ _ a x
  ·
    show η U (OModulePresheaf.AffHom.affineChart p q K' U j) _ (F.res h x) =
      F'.res (OModulePresheaf.cechPushforward.chart_mono p K' h j)
        (η U' (OModulePresheaf.AffHom.affineChart p q K' U' j) _ x)
    have h₁ : (OModulePresheaf.AffHom.affineChart p q K' U j).1 ≤ p ⁻¹ᵁ U'.1 :=
      (OModulePresheaf.cechPushforward.chart_mono p K' h j).trans (OModulePresheaf.cechPushforward.chart_le_preimage p K' U'.1 j)
    rw [hηV U' (OModulePresheaf.AffHom.affineChart p q K' U j) (OModulePresheaf.AffHom.affineChart p q K' U' j) h₁ _
        (OModulePresheaf.cechPushforward.chart_mono p K' h j) x,
      hηU U U' (OModulePresheaf.AffHom.affineChart p q K' U j) _ h₁ h x]

end S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_apply_eq_of_forall_res_eq
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affHom_cechPushforward_apply_eq_of_forall_res_eq (solution)
