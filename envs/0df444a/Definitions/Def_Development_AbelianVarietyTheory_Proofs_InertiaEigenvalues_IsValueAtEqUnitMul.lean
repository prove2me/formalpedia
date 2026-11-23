-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsValueAtEqUnitMul
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsValueAtEqUnitMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:10.824621+00:00
-- url     : https://prove2.me/theorems/2b23017a-6950-44a2-ba64-9de8b2f1d1e7
-- title:
--   Is Value At Eq Unit Mul
-- statement:
--   Definitions and structural lemmas for Is Value At Eq Unit Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsValueAtEqUnitMul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IntegralSec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ModelMetric
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ValueTwoGen
def genSec {Y : Scheme.{0}} {M : LB Y} (t : LB.Gen M) (ht : t.IsGen) : LB.Sec M where
  f := fun j => (t.s j).val
  compat := fun i j => congrArg Units.val (ht i j)
end GlobalTheory.ValueTwoGen


