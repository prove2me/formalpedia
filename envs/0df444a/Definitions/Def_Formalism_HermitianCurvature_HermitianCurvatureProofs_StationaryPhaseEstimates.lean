-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:26:16.429511+00:00
-- url     : https://prove2.me/theorems/7fc3bd58-ce51-4b84-9b3f-905ad9a02cbf
-- title:
--   Stationary Phase Estimates
-- statement:
--   Definitions and structural lemmas for Stationary Phase Estimates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section
instance sigmaFinite_mu (β : ℂ) : SigmaFinite (mu β) := by unfold mu; infer_instance
instance sigmaFinite_muPi (β : ℂ) (ι : Type) [Fintype ι] : SigmaFinite (muPi β ι) := by
  unfold muPi; infer_instance
instance sigmaFinite_muXY (β : ℂ) (m : ℕ) : SigmaFinite (muXY β m) := by
  unfold muXY; infer_instance
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
def diagPt (s : ℕ) (a : ℂ) : Mat (s + 2) := Matrix.diagonal (fun i : Fin (s + 2) => if i = 0 then a else 1)
variable [CompleteSpace V]
end
def ns_Om (m : ℕ) (D' : ℂ) (r d : ℝ) : Set (Fin (m + 1) → ℂ) :=
  {x | (∀ k, r < ‖x k‖) ∧ ∀ z ∈ rootSet (m + 2) D', d < ‖x - fun _ => z‖}
def ns_Fs (m : ℕ) (D' : ℂ) (R r d : ℝ) : Set (Fin (m + 1) → ℂ) :=
  {x | (∀ k, ‖x k‖ ≤ R ∧ r ≤ ‖x k‖) ∧ ∀ z ∈ rootSet (m + 2) D', d ≤ ‖x - fun _ => z‖}
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
end
end
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite


