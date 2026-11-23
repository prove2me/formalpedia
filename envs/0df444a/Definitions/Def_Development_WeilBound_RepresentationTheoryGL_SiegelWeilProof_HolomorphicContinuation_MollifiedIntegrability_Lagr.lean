-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:18:27.723146+00:00
-- url     : https://prove2.me/theorems/409604a7-7f17-4243-ae81-1148dd7062d3
-- title:
--   Lagr
-- statement:
--   Definitions and structural lemmas for Lagr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/Lagr.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
def Twist : Prop :=
  ∀ (n : ℕ) (H : E n → ℂ), ContDiff ℝ (⊤ : ℕ∞) H → ∀ N : ℕ, ∃ G : ℕ → E n → ℂ,
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (G j)) ∧ ∀ (z : ℂ) (y : E n),
      (Delta^[N] (fun y => ((dP y : ℝ) : ℂ) ^ (-z) * H y)) y =
        ((dP y : ℝ) : ℂ) ^ (-z) * ∑ j ∈ Finset.range (n * N + 1), z ^ j * G j y
def Lagr : Prop :=
  ∀ D : ℕ, ∃ C : ℝ, ∀ (c : ℕ → ℂ) (B : ℝ), (∀ i ≤ D, ‖∑ j ∈ Finset.range (D + 1), ((i : ℕ) : ℂ) ^ j * c j‖ ≤ B) →
    ∀ j ≤ D, ‖c j‖ ≤ C * B
end PositivityTheory.Rg.Sw.WR.K.GB


