-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
-- name    : Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:16.917244+00:00
-- url     : https://prove2.me/theorems/9854c0ac-9969-41a6-8c02-25aeba2a4c12
-- title:
--   Has Deriv At Schwartz To L2
-- statement:
--   Definitions and structural lemmas for Has Deriv At Schwartz To L2, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/HasDerivAtSchwartzToL2.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real
namespace PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]
def LD (U : ℝ → Sch l →L[ℂ] Sch l) (Q : Sch l → Sch l) (t₀ : ℝ) : Prop :=
  ∀ f, HasDerivAt (fun t => schwartzToL2 l (U t f)) (schwartzToL2 l (Q f)) t₀
variable [DecidableEq l]
end PositivityTheory.ThKR.LL


