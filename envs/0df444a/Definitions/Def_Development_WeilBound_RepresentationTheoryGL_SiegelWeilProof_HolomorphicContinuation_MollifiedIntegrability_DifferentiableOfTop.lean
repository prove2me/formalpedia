-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DifferentiableOfTop
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DifferentiableOfTop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:27.202872+00:00
-- url     : https://prove2.me/theorems/1b3abd1f-9cd8-4dd0-8e1e-84c9224ee23c
-- title:
--   Differentiable Of Top
-- statement:
--   Definitions and structural lemmas for Differentiable Of Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DifferentiableOfTop.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
namespace PositivityTheory.Rg.Sw.WR.T
open PositivityTheory.Rg.Sw
variable {n : ℕ}
def FD (L : List (Fin n × Fin n)) (f : E n → ℂ) : E n → ℂ := L.foldr (fun kl g => Dkl kl.1 kl.2 g) f
def Ls (σ : Equiv.Perm (Fin n)) : List (Fin n × Fin n) := (List.finRange n).map fun k => (k, σ k)
def Good (f : E n → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧ ∀ L : List (Fin n × Fin n), ∃ h : E n → ℝ, Integrable h ∧ ∀ y, ‖FD L f y‖ ≤ h y
end PositivityTheory.Rg.Sw.WR.T


