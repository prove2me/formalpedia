-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OmFConnPf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OmFConnPf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:44.018658+00:00
-- url     : https://prove2.me/theorems/1067ae46-43a1-4d4a-95bd-fb73fa4b0e18
-- title:
--   Om FConn Pf
-- statement:
--   Definitions and structural lemmas for Om FConn Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/OmFConnPf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OFC
open NumberField Complex Matrix Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def isW (i : Fin (nd X)) : Prop :=
  X.p0 ≤ (((Fintype.equivFin (Ent X)).symm i).2.1.1 : ℕ) ∧ (((Fintype.equivFin (Ent X)).symm i).2.1.2 : ℕ) < X.p0
instance (i : Fin (nd X)) : Decidable (isW X i) := by unfold isW; infer_instance
def S1 (t : ℝ) (z : V (nd X)) : V (nd X) := WithLp.toLp 2 fun i => if isW X i then (t : ℂ) * z i else z i
def S2 (t : ℝ) (z : V (nd X)) : V (nd X) := WithLp.toLp 2 fun i => if isW X i then 0 else (t : ℂ) * z i
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.OFC
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField
end ReciprocityTheory.ChartRestriction.G.AR.Up


