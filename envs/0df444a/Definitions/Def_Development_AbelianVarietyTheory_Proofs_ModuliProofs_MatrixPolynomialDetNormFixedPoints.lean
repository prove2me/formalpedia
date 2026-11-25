-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MatrixPolynomialDetNormFixedPoints
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_MatrixPolynomialDetNormFixedPoints
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T16:57:24.409136+00:00
-- url     : https://prove2.me/theorems/a698833d-392b-4caf-a2d4-22df7c15dfc3
-- title:
--   Matrix Polynomial Det Norm Fixed Points
-- statement:
--   Definitions and structural lemmas for Matrix Polynomial Det Norm Fixed Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MatrixPolynomialDetNormFixedPoints.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NormCardQuotientSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
namespace TorsionMatrix
section
open Matrix
section ev
variable {Q κ : Type} [AddCommGroup Q] [Fintype κ] {N : ℕ} [NeZero N]
theorem val_add_smul {x : Q} (hx : N • x = 0) (a b : ZMod N) :
    (a + b).val • x = a.val • x + b.val • x := by
  rw [ZMod.val_add, ← nsmul_eq_mod_nsmul _ hx, add_smul]
def ev (pt : κ → Q) (h : ∀ i, N • pt i = 0) : (κ → ZMod N) →+ Q :=
  AddMonoidHom.mk' (fun t => ∑ i, (t i).val • pt i) fun a b => by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => val_add_smul (h i) _ _
end ev
end
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
end TorsionMatrix
end GlobalTheory


