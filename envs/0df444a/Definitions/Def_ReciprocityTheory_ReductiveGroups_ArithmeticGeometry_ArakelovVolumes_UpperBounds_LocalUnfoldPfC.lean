-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfC
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfC
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:06.796245+00:00
-- url     : https://prove2.me/theorems/9bc757da-b4c5-4cee-ab95-39d3610111a3
-- title:
--   Local Unfold Pf C
-- statement:
--   Definitions and structural lemmas for Local Unfold Pf C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/LocalUnfoldPfC.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LocalUnfoldPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')
def uL (x1' b1 x : Frame X.Ψ r) : Frame X.Ψ r := fun τ =>
  (mat x1' τ * (mat b1 τ)⁻¹ * (mat x1' τ)⁻¹ * mat x τ : Matrix (Fin r) (Fin r) ℂ)
def vL (x1' b1 x : Frame X.Ψ r) : Frame X.Ψ r := fun τ =>
  (mat x1' τ * mat b1 τ * (mat x1' τ)⁻¹ * mat x τ : Matrix (Fin r) (Fin r) ℂ)
variable {X b1}
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB


