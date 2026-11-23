-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_FarRight
-- name    : Development_WeilBound_ThetaLifts_LatticeBasics_FarRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:27.184594+00:00
-- url     : https://prove2.me/theorems/4dde7cff-387f-4bfb-b725-4fbfc1084583
-- title:
--   Far Right
-- statement:
--   Definitions and structural lemmas for Far Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/FarRight.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThK.Dbl.An
open MeasureTheory Filter Topology
def BC {X : Type} [TopologicalSpace X] (f : X → ℂ) : Prop := Continuous f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C
section
variable {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] {f g : X → ℂ}
theorem BC.star (h : BC f) : BC fun x => star (f x) := ⟨h.1.star, h.2.imp fun _ h x => (norm_star _).trans_le (h x)⟩
end
variable {G H : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (ν : Measure G) [IsFiniteMeasure ν] (ρ : Measure H) [IsFiniteMeasure ρ] {φ : G → ℂ}
end GlobalTheory.ThK.Dbl.An
end


