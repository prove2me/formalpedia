-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.isPicObstructionCocycle_dual_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/408c4f2c-6406-5282-95c8-54d3093d7391

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_SheafOfModules_MonoidalV2

import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_dual_forall_transition_mul_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_isPicObstructionCocycle_dual_neg
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

theorem solution
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    {X₀ : Scheme.{u}} (g : X₀ ⟶ X) [IsAffineHom g]
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X) [IsAffineHom i]
    (𝒰 : X.OrderedAffineCover)
    (hJ : ∀ v w : V, ι v * ι w = 0)
    (𝓛₀ : X₀.Modules) (c : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 2)
    (hc : IsPicObstructionCocycle V ι f fk i g 𝒰 𝓛₀ c) :
    IsPicObstructionCocycle V ι f fk i g 𝒰 (Scheme.Modules.dual 𝓛₀) (-c) := by
  classical
  obtain ⟨τ, u, u', hu, huu', hδ⟩ := hc
  obtain ⟨σ, hσ⟩ :=
    AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_dual_forall_transition_mul_eq_one (𝒰.comap g) 𝓛₀ τ
  refine ⟨σ, u', u, ?_, ?_, ?_⟩
  · intro s

    have h1 : (X₀.presheaf.map (homOfLE (𝒰.comap_inter_le g s)).op).hom ((g.app (𝒰.inter s)).hom (u s)) *
        (X₀.presheaf.map (homOfLE (𝒰.comap_inter_le g s)).op).hom ((g.app (𝒰.inter s)).hom (u' s)) = 1 := by
      rw [← map_mul, ← map_mul, huu', map_one, map_one]
    rw [hu s] at h1
    calc (X₀.presheaf.map (homOfLE (𝒰.comap_inter_le g s)).op).hom ((g.app (𝒰.inter s)).hom (u' s))
        = (σ.transition s * τ.transition s) *
            (X₀.presheaf.map (homOfLE (𝒰.comap_inter_le g s)).op).hom ((g.app (𝒰.inter s)).hom (u' s)) := by
          rw [hσ s, one_mul]
      _ = σ.transition s * (τ.transition s *
            (X₀.presheaf.map (homOfLE (𝒰.comap_inter_le g s)).op).hom ((g.app (𝒰.inter s)).hom (u' s))) := by ring
      _ = σ.transition s := by rw [h1, mul_one]
  · intro s
    rw [mul_comm, huu']
  · intro r
    obtain ⟨n, v, s, h₁, hw₁⟩ := hδ r
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f (𝒰.inter r)
    refine ⟨n, v, fun j => - s j, ?_, ?_⟩
    ·
      have hz : (∑ j, algebraMap B₁ (X.presheaf.obj (Opposite.op (𝒰.inter r))) (ι (v j)) * s j) *
          (∑ j, algebraMap B₁ (X.presheaf.obj (Opposite.op (𝒰.inter r))) (ι (v j)) * s j) = 0 := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => ?_
        rw [mul_mul_mul_comm, ← map_mul, hJ, map_zero, zero_mul]
      have hAA : ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (u (𝒰.face r 2)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (u (𝒰.face r 0)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (u' (𝒰.face r 1))) *
          ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (u' (𝒰.face r 2)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (u' (𝒰.face r 0)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (u (𝒰.face r 1))) = 1 := by
        have e2 : (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (u (𝒰.face r 2)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (u' (𝒰.face r 2)) = 1 := by rw [← map_mul, huu', map_one]
        have e0 : (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (u (𝒰.face r 0)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (u' (𝒰.face r 0)) = 1 := by rw [← map_mul, huu', map_one]
        have e1 : (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (u' (𝒰.face r 1)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (u (𝒰.face r 1)) = 1 := by rw [← map_mul, mul_comm, huu', map_one]
        linear_combination ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (u (𝒰.face r 0)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (u' (𝒰.face r 0)) * ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (u' (𝒰.face r 1)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (u (𝒰.face r 1)))) * e2 + ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (u' (𝒰.face r 1)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (u (𝒰.face r 1))) * e0 + e1
      rw [h₁] at hz
      simp only [mul_neg, Finset.sum_neg_distrib]
      rw [h₁]
      linear_combination (-((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (u' (𝒰.face r 2)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (u' (𝒰.face r 0)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (u (𝒰.face r 1)))) * hz - (2 - ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (u (𝒰.face r 2)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (u (𝒰.face r 0)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (u' (𝒰.face r 1)))) * hAA
    · intro ξ
      have e₁ := hw₁ ξ
      simp only [LinearMap.comp_apply, LinearMap.proj_apply] at e₁
      rw [LinearMap.comp_apply, LinearMap.proj_apply]
      have hneg : (-c) ξ r = -(c ξ r) := rfl
      refine hneg.trans ((congrArg Neg.neg e₁).trans ?_)
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp only
      rw [map_neg, ← smul_neg]
      congr 1
      exact (LinearMap.map_neg _ _).symm

end S_AlgebraicGeometry_SmallExtension_isPicObstructionCocycle_dual_neg
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_isPicObstructionCocycle_dual_neg (solution)
