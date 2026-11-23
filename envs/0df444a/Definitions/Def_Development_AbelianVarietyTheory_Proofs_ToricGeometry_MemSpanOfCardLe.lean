-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemSpanOfCardLe
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemSpanOfCardLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:30.332169+00:00
-- url     : https://prove2.me/theorems/4eef4952-7a50-43ac-b1c9-e1750326952f
-- title:
--   Mem Span Of Card Le
-- statement:
--   Definitions and structural lemmas for Mem Span Of Card Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MemSpanOfCardLe.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
namespace GlobalTheory.ThetaOnto
theorem res_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a := by
  unfold constFn
  rw [← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_map]
def secComb {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} {K : Type}
    [Fintype K] (a : K → R) (s : K → L.Sec) : L.Sec where
  f j := ∑ i, constFn p _ (a i) * (s i).f j
  compat j k := by
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, res_constFn, res_constFn, (s i).compat j k]
    ring
def secConst {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (L : LB X) (a : R) :
    (lbPow L 0).Sec where
  f j := constFn p _ a
  compat j k := by
    have : (lbPow L 0).g j k = 1 := by
      unfold lbPow LB.LinComb
      dsimp only
      exact Finset.prod_eq_one fun _ _ => zpow_zero _
    rw [res_constFn, res_constFn, this, Units.val_one, _root_.one_mul]
end GlobalTheory.ThetaOnto


