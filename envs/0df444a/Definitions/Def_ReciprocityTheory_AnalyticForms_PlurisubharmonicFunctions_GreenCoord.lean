-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenCoord
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:40.488226+00:00
-- url     : https://prove2.me/theorems/ac84b0ce-51e6-4976-a250-e1567a56d053
-- title:
--   Green Coord
-- statement:
--   Definitions and structural lemmas for Green Coord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/GreenCoord.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Laplacian Pointwise
namespace ReciprocityTheory.AnForm.A
noncomputable section
def uPair {D : ℕ} (j : Fin (D + 1)) (u : (Fin (D + 1) → ℂ) → ℝ) (q : ℂ × (Fin D → ℂ)) : ℝ :=
  u (Fin.insertNth j q.1 q.2)
end
end ReciprocityTheory.AnForm.A


