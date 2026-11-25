-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_TateTransport
-- name    : GroundTheory_TateCohomology_TateTransport
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:43:41.034971+00:00
-- url     : https://prove2.me/theorems/4c66f703-4acb-4b3a-8128-8528cd79d59d
-- title:
--   Tate Transport
-- statement:
--   Definitions and structural lemmas for Tate Transport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateTransport.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_GroundTheory_GroupCoh_norm_res_of_bijective
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.indSES_obj_g
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupCohomology groupHomology
universe u
variable {k H K : Type u} [CommRing k] [Group H] [Group K]
section Complex
variable (e : H ≃* K)
noncomputable def transportChainsMor (B : Rep.{u} k K) :
    B ⟶ res (e.symm : K →* H) (res (e : H →* K) B) :=
  Rep.ofHom ⟨LinearMap.id, fun x => by
    ext b
    simp⟩
@[simp]
lemma transportChainsMor_hom_apply (B : Rep.{u} k K) (b : B) :
    (transportChainsMor e B).hom b = b := rfl
variable [Fintype H] [Fintype K]
lemma transport_comm_zero (B : Rep.{u} k K) :
    (chainsMap (e.symm : K →* H) (transportChainsMor e B)).f 0 ≫
        (tateComplexConnectData (res (e : H →* K) B)).d₀ =
      (tateComplexConnectData B).d₀ ≫ (cochainsMap (e : H →* K) (𝟙 _)).f 0 := by
  refine ModuleCat.hom_ext (Finsupp.lhom_ext fun v b => ?_)
  refine funext fun w => ?_
  have e1 : ((tateComplexConnectData B).d₀).hom (Finsupp.single v b) = fun _ => B.ρ.norm b := by
    simp [Rep.tateNorm_eq]
    rfl
  have e2 : ((tateComplexConnectData (res (e : H →* K) B)).d₀).hom
      (((chainsMap (e.symm : K →* H) (transportChainsMor e B)).f 0).hom (Finsupp.single v b)) =
      fun _ => (res (e : H →* K) B).ρ.norm b := by
    rw [chainsMap_f_single]
    simp [Rep.tateNorm_eq]
    rfl
  change ((tateComplexConnectData (res (e : H →* K) B)).d₀).hom
      (((chainsMap (e.symm : K →* H) (transportChainsMor e B)).f 0).hom (Finsupp.single v b)) w =
    ((cochainsMap (e : H →* K) (𝟙 _)).f 0).hom
      (((tateComplexConnectData B).d₀).hom (Finsupp.single v b)) w
  rw [e1, e2, norm_res_of_bijective (e : H →* K) e.bijective]
  rfl
noncomputable def tateTransportComplex (B : Rep.{u} k K) :
    tateComplex B ⟶ tateComplex (res (e : H →* K) B) :=
  CochainComplex.ConnectData.map _ _ (chainsMap (e.symm : K →* H) (transportChainsMor e B))
    (cochainsMap (e : H →* K) (𝟙 _)) (transport_comm_zero e B)
lemma tateTransportComplex_naturality {B B' : Rep.{u} k K} (φ : B ⟶ B') :
    tateTransportComplex e B ≫ tateComplex.map ((resFunctor (e : H →* K)).map φ) =
      tateComplex.map φ ≫ tateTransportComplex e B' := by
  ext (m | m) : 1
  · rfl
  · change (chainsMap (e.symm : K →* H) (transportChainsMor e B) ≫ chainsMap (MonoidHom.id H)
      ((resFunctor (e : H →* K)).map φ)).f m = (chainsMap (MonoidHom.id K) φ ≫
        chainsMap (e.symm : K →* H) (transportChainsMor e B')).f m
    rw [← chainsMap_comp, ← chainsMap_comp]
    congr 1
@[simps]
noncomputable def tateTransportComplexNatTrans :
    tateComplexFunctor k K ⟶ resFunctor (e : H →* K) ⋙ tateComplexFunctor k H where
  app := tateTransportComplex e
  naturality _ _ φ := (tateTransportComplex_naturality e φ).symm
end Complex
section Cohomology
variable [Fintype H] [Fintype K] (e : H ≃* K)
noncomputable def tateTransport (n : ℤ) :
    tateCohomologyFunctor (R := k) (G := K) n ⟶
      resFunctor (e : H →* K) ⋙ tateCohomologyFunctor (R := k) (G := H) n :=
  Functor.whiskerRight (tateTransportComplexNatTrans e) (HomologicalComplex.homologyFunctor _ _ n)
@[simps]
noncomputable def tateTransportShortComplex (X : ShortComplex (Rep.{u} k K)) :
    X.map (tateComplexFunctor k K) ⟶
      (X.map (resFunctor (e : H →* K))).map (tateComplexFunctor k H) where
  τ₁ := tateTransportComplex e X.X₁
  τ₂ := tateTransportComplex e X.X₂
  τ₃ := tateTransportComplex e X.X₃
  comm₁₂ := tateTransportComplex_naturality e X.f
  comm₂₃ := tateTransportComplex_naturality e X.g
omit [Fintype H] [Fintype K] in

lemma shortExact_map_resFunctor_equiv {X : ShortComplex (Rep.{u} k K)} (hX : X.ShortExact) :
    (X.map (resFunctor (e : H →* K))).ShortExact :=
  (Rep.shortExact_res (e : H →* K)).2 hX
omit [Fintype H] [Fintype K] in

def invariantsTransport {B : Rep.{u} k K} (x : B.ρ.invariants) :
    (res (e : H →* K) B).ρ.invariants :=
  ⟨x, fun h => x.2 (e h)⟩
end Cohomology
end GroundTheory.GroupCoh


