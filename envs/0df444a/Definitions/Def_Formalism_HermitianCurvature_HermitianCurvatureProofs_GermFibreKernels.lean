-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermFibreKernels
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_GermFibreKernels
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T04:28:35.355802+00:00
-- url     : https://prove2.me/theorems/447439f9-85b5-44af-8692-4b952a7b609a
-- title:
--   Germ Fibre Kernels
-- statement:
--   Definitions and structural lemmas for Germ Fibre Kernels, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermFibreKernels.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
section propG
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
structure GermBlockL2 {ι : Type} (μ : Measure ℂ) (Y : Finset ι) (U A : ι × ℂ → ℂ → H) (N : ℂ → ι → ι → ℂ) : Prop where
  memU : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (U (h, x)) 2 μ
  memA : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (A (h, x)) 2 μ
  sup : ∃ B : ℝ, ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → ∫ D, ‖U (h, x) D‖ ^ 2 ∂μ ≤ B
  dom : ∀ h ∈ Y, ∃ ab : ℂ → ℝ, MemLp ab 2 μ ∧ ∀ x : ℂ, x ≠ 0 → ∀ᵐ D ∂μ, ‖A (h, x) D‖ ≤ ab D
  germ : ∀ h ∈ Y, ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 →
    ∀ᵐ D ∂μ, D ∈ K → ‖U (h, x) D - A (h, x) D‖ ≤ C * ‖x‖⁻¹
  lim : ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
    Tendsto (fun x => ∫ D, ⟪A (h, x) D, A (h', x + σ) D⟫_ℂ ∂μ) (cocompact ℂ) (𝓝 (N σ h h'))
variable {ι : Type} {μ : Measure ℂ} {Y : Finset ι} {U A : ι × ℂ → ℂ → H} {N : ℂ → ι → ι → ℂ}
end propG
end
end Formalism.FourierDecayAlt.P.PBK


