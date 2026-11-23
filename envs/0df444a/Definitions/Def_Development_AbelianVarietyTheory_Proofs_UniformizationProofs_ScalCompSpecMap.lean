-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ScalCompSpecMap
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ScalCompSpecMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:23.684946+00:00
-- url     : https://prove2.me/theorems/43cb8233-7f72-4ea3-9900-ad5c48ef3e74
-- title:
--   Scal Comp Spec Map
-- statement:
--   Definitions and structural lemmas for Scal Comp Spec Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ScalCompSpecMap.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtIffStalks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace ExpandsLinear
def scalOn {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens) :
    R →+* Γ(Y, W) :=
  (Y.presheaf.map (homOfLE le_top).op).hom.comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
def secComb {Y : Scheme.{0}} {L : LB Y} {n : ℕ} (a : Fin n → Γ(Y, ⊤)) (s : Fin n → LB.Sec L) : LB.Sec L where
  f := fun j => ∑ i, resTop _ (a i) * (s i).f j
  compat := fun j j' => by
    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (a i) (s i)).compat j j'
end ExpandsLinear
end GlobalTheory


