-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_EvalZeroReplicateAppend
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_EvalZeroReplicateAppend
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:33:26.938908+00:00
-- url     : https://prove2.me/theorems/2b920c52-b332-4355-93b6-980ff04fcd66
-- title:
--   Eval Zero Replicate Append
-- statement:
--   Definitions and structural lemmas for Eval Zero Replicate Append, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/EvalZeroReplicateAppend.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CcTMulQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {ι : Type}
def ev0 (b : List ι) : k := if b = [] then 1 else 0
def ev1 (g : ι → k) : List ι → k
  | [y] => g y
  | _ => 0
def word (Ls : List ι) (m : ι →₀ ℕ) : List ι := Ls.flatMap (fun l => List.replicate (m l) l)
end ReciprocityTheory.ChartRestriction.G.TB.G2


