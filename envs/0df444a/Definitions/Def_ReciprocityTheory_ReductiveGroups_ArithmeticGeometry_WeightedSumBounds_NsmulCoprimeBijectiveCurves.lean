-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_NsmulCoprimeBijectiveCurves
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_NsmulCoprimeBijectiveCurves
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:37:41.247035+00:00
-- url     : https://prove2.me/theorems/4a0a3279-d8ef-44b3-9dc4-bab05e66e68f
-- title:
--   Nsmul Coprime Bijective Curves
-- statement:
--   Definitions and structural lemmas for Nsmul Coprime Bijective Curves, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/NsmulCoprimeBijectiveCurves.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
def ptNs (G : LogFGL v d) : ℕ → Fin d → MvPowerSeries (Fin d) C
  | 0 => 0
  | n + 1 => fun a => subst (Sum.elim (fun b => X b) (ptNs G n)) (G.F a)
end
end ReciprocityTheory.ChartRestriction.G.Sh


