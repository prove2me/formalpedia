-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFourthSide
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFourthSide
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:04:23.064239+00:00
-- url     : https://prove2.me/theorems/af06620d-1f0a-42b8-a282-f308936e1da8
-- title:
--   Exists Fourth Side
-- statement:
--   Definitions and structural lemmas for Exists Fourth Side, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsFourthSide.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.FourthSide
variable {B B' G G' Ge Ge' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB G} {L' : LB G'}
  {Φ : B' ⟶ B} {Ψ : G' ⟶ G} {pG : Ge ⟶ B} {pG' : Ge' ⟶ B'} {fG : Ge ⟶ G} {fG' : Ge' ⟶ G'} {h : Ge' ⟶ Ge}
def germ (pG' : Ge' ⟶ B') (fG' : Ge' ⟶ G') (h : Ge' ⟶ Ge) (w : LB.Iso M' (M.pull Φ)) (wL : LB.Iso L' (L.pull Ψ))
    (we : LB.Iso (L.pull fG) (M.pull pG)) {Z : Scheme.{0}} (r : Z ⟶ Ge') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι)
    (jL' : L'.ι) : (Z.presheaf.stalk z)ˣ :=
  (gw w (r ≫ pG') z jM jM')⁻¹ * (gw we (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ fG') z jL jL')
end GlobalTheory.FourthSide


