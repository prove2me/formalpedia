-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:06.675796+00:00
-- url     : https://prove2.me/theorems/3cdc8d45-df5e-4e76-abe2-ef2e1532c515
-- title:
--   Is Unit Iff Mem
-- statement:
--   Definitions and structural lemmas for Is Unit Iff Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
theorem le_pre {Y Z : Scheme.{0}} (D : Y.Opens) (g : Z ⟶ D.toScheme) : ⊤ ≤ (g ≫ D.ι) ⁻¹ᵁ D :=
  fun z _ => (g z).2
section
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
end
end GlobalTheory.VeryAmplePow


