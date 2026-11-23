-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_GaussScalar
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_GaussScalar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:21.385483+00:00
-- url     : https://prove2.me/theorems/32756075-d026-4dcd-a648-17c4e39e24d5
-- title:
--   Gauss Scalar
-- statement:
--   Definitions and structural lemmas for Gauss Scalar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/GaussScalar.lean

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
open Complex MeasureTheory
namespace PositivityTheory.Rg.Sw.Glob.VacS
def DG {m n : ℕ} (K : ℂ) (γ : Fin m → Fin n → ℂ) (v : Fin m → Fin n → ℂ) : ℂ :=
  K * ∏ a, ∏ j, cexp (-γ a j * ((‖v a j‖ ^ 2 : ℝ) : ℂ))
def ftG {m n : ℕ} (σ : Fin m → ℝ) (s : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  ∫ y : Fin m → Fin n → ℂ, f y *
    cexp (I * ((2 * s : ℝ) : ℂ) * ((∑ a, ∑ j, σ a * ((starRingEnd ℂ (u a j)) * y a j).re : ℝ) : ℂ))
end PositivityTheory.Rg.Sw.Glob.VacS


