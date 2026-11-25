-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_HasFDerivAtOrb
-- name    : Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_HasFDerivAtOrb
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T12:31:17.334352+00:00
-- url     : https://prove2.me/theorems/0521b2aa-d98d-4f7b-862b-ca9eeb654bd6
-- title:
--   Has FDeriv At Orb
-- statement:
--   Definitions and structural lemmas for Has FDeriv At Orb, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/MetaplecticDerivatives/HasFDerivAtOrb.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MpFOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real ContDiff
namespace PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
def orb {k : ℕ} (γ : (Fin k → ℝ) → G l) (f : Sch l) (t : Fin k → ℝ) : L2 l := om (γ t) (schwartzToL2 l f)
def dm {k : ℕ} (γ : (Fin k → ℝ) → G l) (t : Fin k → ℝ) (a b : l ⊕ l) : (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ c, ((pr (γ t))⁻¹ : Sp l).1 a c • fderiv ℝ (fun t => (pr (γ t) : Mat l) c b) t
end PositivityTheory.ThKR.Mp


