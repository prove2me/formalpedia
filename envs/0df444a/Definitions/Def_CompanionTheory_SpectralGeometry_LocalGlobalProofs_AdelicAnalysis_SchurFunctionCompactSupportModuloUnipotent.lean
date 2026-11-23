-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotent
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:19.505709+00:00
-- url     : https://prove2.me/theorems/4083206b-12d8-4833-9ef5-f4ff0ac73c77
-- title:
--   Schur Function Compact Support Modulo Unipotent
-- statement:
--   Definitions and structural lemmas for Schur Function Compact Support Modulo Unipotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SchurFunctionCompactSupportModuloUnipotent.lean

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
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
namespace GlobalTheory.CompanionTheory.SW.CharDensity
open scoped FourierTransform
open Filter
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
noncomputable def phi (μ : Measure V) (x : V) : ℂ :=
  ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ z x : ℝ) : ℂ)) ∂μ
noncomputable def ker (b : ℝ) (w : V) : ℝ :=
  (Real.pi / b) ^ ((Module.finrank ℝ V : ℝ) / 2) * Real.exp (-(Real.pi ^ 2 / b) * ‖w‖ ^ 2)
noncomputable def dens (μ : Measure V) (y : V) : ℂ :=
  ∫ x, phi μ x * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ y x : ℝ) : ℂ))
noncomputable def bn (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
end GlobalTheory.CompanionTheory.SW.CharDensity


