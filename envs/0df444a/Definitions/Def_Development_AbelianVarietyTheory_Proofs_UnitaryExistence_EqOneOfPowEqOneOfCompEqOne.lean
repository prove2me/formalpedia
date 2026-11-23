-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:36.300804+00:00
-- url     : https://prove2.me/theorems/4e5ef415-d1b1-4440-9f0a-f712dad5d919
-- title:
--   Eq One Of Pow Eq One Of Comp Eq One
-- statement:
--   Definitions and structural lemmas for Eq One Of Pow Eq One Of Comp Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/EqOneOfPowEqOneOfCompEqOne.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.KernelNoTorsion
theorem comp_mulN {S : Scheme.{0}} {Y G : Over S} [GrpObj G] (x : Y ⟶ G) (n : ℕ) :
    x ≫ mulN G n = x ^ n := by
  induction n with
  | zero => rw [pow_zero, mulN, Hom.one_def, comp_toUnit_assoc]
  | succ n ih => rw [pow_succ, mulN, Hom.mul_def, comp_lift_assoc, ih, Category.comp_id]
noncomputable def torsionLift {S : Scheme.{0}} {Y G : Over S} [GrpObj G] {n : ℕ} (x : Y ⟶ G)
    (hx : x ^ n = 1) : Y ⟶ torsion G n :=
  pullback.lift x (toUnit Y) (by rw [comp_mulN, hx, Hom.one_def])
end GlobalTheory.KernelNoTorsion


