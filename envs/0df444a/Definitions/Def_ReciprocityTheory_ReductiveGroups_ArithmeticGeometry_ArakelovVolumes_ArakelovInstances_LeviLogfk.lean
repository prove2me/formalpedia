-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviLogfk
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviLogfk
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:25:29.769724+00:00
-- url     : https://prove2.me/theorems/634b2519-c28b-4f3c-b554-472b572fc3d7
-- title:
--   Levi Logfk
-- statement:
--   Definitions and structural lemmas for Levi Logfk, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/LeviLogfk.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviFinsetSum
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
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates ReciprocityTheory.AnForm Filter Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {x0 b : Frame X.Ψ r} {z u : V (nd X)}
def Ck (X : Data E r) (b : Frame X.Ψ r) (z u : V (nd X)) (τ : X.Ψ) (k : Fin (r + 1)) : ℝ :=
  ∑ a : Fin k, (Dsg X (Fin.castLE (Nat.le_of_lt_succ k.isLt) a))⁻¹ *
    Sa (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) a
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf


