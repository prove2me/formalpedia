-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralImageLeConst
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralImageLeConst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:52.14265+00:00
-- url     : https://prove2.me/theorems/2d7361b0-3af4-4263-be3a-b3621e103408
-- title:
--   Lintegral Image Le Const
-- statement:
--   Definitions and structural lemmas for Lintegral Image Le Const, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LintegralImageLeConst.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.FrameLoc
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
  MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def lowPart (y : Frame X.Ψ r) : V (nd X) :=
  WithLp.toLp 2 fun j => y ((Fintype.equivFin (Ent X)).symm j).1
    ((Fintype.equivFin (Ent X)).symm j).2.1.1 ((Fintype.equivFin (Ent X)).symm j).2.1.2
def upPart (y : Frame X.Ψ r) : Frame X.Ψ r := fun τ a c => if c < a then 0 else y τ a c
def glue (z : V (nd X)) (b : Frame X.Ψ r) : Frame X.Ψ r := fun τ a c =>
  if h : c < a then z ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩) else b τ a c
def theta (x1 y : Frame X.Ψ r) : Frame X.Ψ r := rmul (cpt X x1 (lowPart X y)) (upPart X y)
end
end GlobalTheory.FrameLoc
namespace GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
  MeasureTheory Topology GlobalTheory.FrameLoc
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory


