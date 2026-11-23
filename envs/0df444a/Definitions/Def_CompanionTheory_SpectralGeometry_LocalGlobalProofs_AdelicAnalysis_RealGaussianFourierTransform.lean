-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RealGaussianFourierTransform
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RealGaussianFourierTransform
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:26.215805+00:00
-- url     : https://prove2.me/theorems/87367f8f-2be0-4a08-a3cd-78e2f6f14a10
-- title:
--   Real Gaussian Fourier Transform
-- statement:
--   Definitions and structural lemmas for Real Gaussian Fourier Transform, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/RealGaussianFourierTransform.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SimultaneousNormalFormMajorant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
namespace GlobalTheory.CompanionTheory.SW.GaussOne
noncomputable def beta (τ : ℂ) (e : ℝ) : ℂ :=
  (τ.im : ℂ) - Complex.I * (τ.re : ℂ) * (e : ℂ)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end GlobalTheory.CompanionTheory.SW.GaussOne


