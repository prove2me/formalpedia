-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PowerBoundNonzeroCoefficient
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PowerBoundNonzeroCoefficient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:55.852919+00:00
-- url     : https://prove2.me/theorems/4a18b595-c167-478e-8e0a-03f8e3490177
-- title:
--   Power Bound Nonzero Coefficient
-- statement:
--   Definitions and structural lemmas for Power Bound Nonzero Coefficient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/PowerBoundNonzeroCoefficient.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_FibreFactorHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace PositivityTheory.Rg.BcB.F
def PowerBoundNonzeroCoefficient : Prop := ∀ (B : Type) [CommRing B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
  (ι : Type) [Fintype ι] [Nonempty ι] (H : ι → Type) [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] (R : ∀ s, B →⋆ₐ[ℂ] (H s →L[ℂ] H s)) (J : Type) [Fintype J] (c : J → ℂ) (q : J → (B →ₐ[ℂ] ℂ)),
  (∀ b, ∃ (C : ℝ) (N : ℕ), ∀ᶠ k : ℕ in Filter.atTop,
    ‖∑ j, c j * q j b ^ k‖ ≤ C * (1 + k) ^ N * (Finset.univ.sup' Finset.univ_nonempty fun s => ‖R s b‖) ^ k) →
  ∀ p : B →⋆ₐ[ℂ] ℂ, ∑ j with q j = (p : B →ₐ[ℂ] ℂ), c j ≠ 0 → ∃ s, ∀ b, ‖p b‖ ≤ ‖R s b‖
end PositivityTheory.Rg.BcB.F
end


