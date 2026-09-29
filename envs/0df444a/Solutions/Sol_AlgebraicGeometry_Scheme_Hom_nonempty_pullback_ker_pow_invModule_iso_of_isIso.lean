-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/2368a9c5-d1da-5172-afd6-fc7e9fbbb811

import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.IdealSheafData.one_eq_top Scheme.IdealSheafData.le_map_comap Scheme.Modules.pullback Scheme.Hom Scheme.IdealSheafData.map_ker Scheme.IdealSheafData.map_id Scheme Scheme.IdealSheafData.comap_top IsClosedImmersion Scheme.IdealSheafData.map_comp Scheme.IdealSheafData.map_mono Scheme.Modules Scheme.IdealSheafData.comap_map_le Scheme.IdealSheafData Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.comap_mul Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison"
namespace BCKerGlue
p2m_open "AlgebraicGeometry"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem comap_eq_map_inv {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (J : X.IdealSheafData) :
    J.comap f = J.map (inv f) := by
  apply le_antisymm
  · have h : ((J.map (inv f)).map f).comap f ≤ J.map (inv f) :=
      Scheme.IdealSheafData.comap_map_le (J.map (inv f)) f
    rwa [← Scheme.IdealSheafData.map_comp, IsIso.inv_hom_id, Scheme.IdealSheafData.map_id] at h
  · have h : J.map (inv f) ≤ ((J.comap f).map f).map (inv f) :=
      Scheme.IdealSheafData.map_mono (inv f) (Scheme.IdealSheafData.le_map_comap J f)
    rwa [← Scheme.IdealSheafData.map_comp, IsIso.hom_inv_id, Scheme.IdealSheafData.map_id] at h

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem ker_comap_eq_ker {X Y T : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (p : T ⟶ X) (p' : T ⟶ Y)
    (hp : p' ≫ f = p) : p.ker.comap f = p'.ker := by
  rw [comap_eq_map_inv, Scheme.IdealSheafData.map_ker, ← hp, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem comap_pow {X Y : Scheme.{u}} (f : Y ⟶ X) (I : X.IdealSheafData) (n : ℕ) :
    (I ^ n).comap f = (I.comap f) ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.one_eq_top,
        Scheme.IdealSheafData.comap_top]
  | succ n ih =>
      rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

end AlgebraicGeometry.BCKerGlue

open AlgebraicGeometry.BCKerGlue in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {X Y T : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (p : T ⟶ X) [IsClosedImmersion p] (p' : T ⟶ Y)
    (hp : p' ≫ f = p) (hI : p.ker.IsInvertible) (hI' : p'.ker.IsInvertible) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback f).obj ((p.ker ^ n).invModule) ≅ ((p'.ker) ^ n).invModule) ∧
      Nonempty ((Scheme.Modules.pullback f).obj ((p.ker ^ n).module) ≅ ((p'.ker) ^ n).module) := by

  have hk : (p.ker ^ n).comap f = p'.ker ^ n := by
    rw [comap_pow, ker_comap_eq_ker f p p' hp]
  have hIn : (p.ker ^ n).IsInvertible := hI.pow n
  have hIn' : ((p.ker ^ n).comap f).IsInvertible := by
    rw [hk]
    exact hI'.pow n
  refine ⟨?_, ?_⟩
  · obtain ⟨e⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso f hIn hIn'
    exact ⟨e ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule hk)⟩
  · have h := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison f hIn hIn'
    exact ⟨@asIso _ _ _ _ ((p.ker ^ n).pullbackModuleComparison f) h ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module hk)⟩

end S_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso (solution)
