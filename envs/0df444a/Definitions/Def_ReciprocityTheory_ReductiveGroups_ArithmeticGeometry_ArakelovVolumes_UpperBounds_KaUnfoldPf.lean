-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:56.970236+00:00
-- url     : https://prove2.me/theorems/d8a3a944-dab2-456f-8358-feb7e255bdb6
-- title:
--   Ka Unfold Pf
-- statement:
--   Definitions and structural lemmas for Ka Unfold Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def Hg (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) (bb : ℝ) (φ : Frame X.Ψ r → ℝ≥0∞)
    (γ : GL (Fin r) E) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  (lact γ⁻¹ ⁻¹' Sset X x0 FF).indicator (fun y => ENNReal.ofReal (kap X x0 bb y) * φ y) x
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
end ReciprocityTheory.ChartRestriction.G.AR.Up


