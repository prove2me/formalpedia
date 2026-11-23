-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankTotalDegreeImageGrowth
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankTotalDegreeImageGrowth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:28.607934+00:00
-- url     : https://prove2.me/theorems/228f69c8-8567-4c33-9a3c-3803677f9584
-- title:
--   Finrank Total Degree Image Growth
-- statement:
--   Definitions and structural lemmas for Finrank Total Degree Image Growth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankTotalDegreeImageGrowth.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
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
namespace GlobalTheory
namespace DegreeGrowth
variable {K B : Type} [Field K] [CommRing B] [Algebra K B]
def boxSpan (K : Type) {B : Type} [Field K] [CommRing B] [Algebra K B] {s n : ℕ}
    (y : Fin s → B) (b : Fin n → B) (D : ℕ) : Submodule K B :=
  Submodule.span K (Set.range fun al : (Fin s → Fin (D + 1)) × Fin n =>
    (∏ i, y i ^ (al.1 i : ℕ)) * b al.2)
instance finite_boxSpan {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D : ℕ) :
    Module.Finite K (boxSpan K y b D) :=
  Module.Finite.span_of_finite K (Set.finite_range _)
end DegreeGrowth
end GlobalTheory


