-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviFinsetSum
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviFinsetSum
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:18:58.891176+00:00
-- url     : https://prove2.me/theorems/ea354ff7-2951-4f84-b45d-734f3a2e20c4
-- title:
--   Levi Finset Sum
-- statement:
--   Definitions and structural lemmas for Levi Finset Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/LeviFinsetSum.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetSubMapConj
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
section Line
variable (x0 b : Frame X.Ψ r) (z u : V (nd X))
def fk (τ : X.Ψ) (k : Fin (r + 1)) : (Fin 1 → ℂ) → ℝ :=
  fY (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ)
def cB (τ : X.Ψ) (k : Fin (r + 1)) : ℝ :=
  Real.log (‖((mat b τ)⁻¹.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
    (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det‖ ^ 2)
variable {X x0 b z u}
end Line
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf


