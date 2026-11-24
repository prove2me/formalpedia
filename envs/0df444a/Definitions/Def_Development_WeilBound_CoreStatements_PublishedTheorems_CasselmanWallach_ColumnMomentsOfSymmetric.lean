-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_ColumnMomentsOfSymmetric
-- name    : Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_ColumnMomentsOfSymmetric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:31.532812+00:00
-- url     : https://prove2.me/theorems/b5d906bb-b437-4754-b95d-c78e637bfcaf
-- title:
--   Column Moments Of Symmetric
-- statement:
--   Definitions and structural lemmas for Column Moments Of Symmetric, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/ColumnMomentsOfSymmetric.lean

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
namespace PositivityTheory.CW
namespace MatrixActionSingle
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
def act (A : Matrix (Fin n) (Fin n) (Module.End ℂ V)) : Module.End ℂ (PiLp 2 fun _ : Fin n => V) where
  toFun u := WithLp.toLp 2 (fun a => ∑ b, A a b (u b))
  map_add' u w := by ext a; simp [Finset.sum_add_distrib]
  map_smul' c u := by ext a; simp [Finset.smul_sum]
end MatrixActionSingle
end PositivityTheory.CW
end


