-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGaussianFourier
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGaussianFourier
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:41.916484+00:00
-- url     : https://prove2.me/theorems/482a3c15-0a1f-4240-a543-964ddaf81c28
-- title:
--   Archimedean Gaussian Fourier
-- statement:
--   Definitions and structural lemmas for Archimedean Gaussian Fourier, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanGaussianFourier.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RealGaussianFourierTransformStatement
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
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.GaussFou
def g1 {ι : Type} [Fintype ι] (S P : Matrix ι ι ℝ) (τ : ℂ) (x : ι → ℝ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * (τ.re : ℂ) * ((x ⬝ᵥ (S *ᵥ x) : ℝ) : ℂ) -
    (Real.pi : ℂ) * (τ.im : ℂ) * ((x ⬝ᵥ (P *ᵥ x) : ℝ) : ℂ))
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
end GlobalTheory.CompanionTheory.SW.GaussFou


