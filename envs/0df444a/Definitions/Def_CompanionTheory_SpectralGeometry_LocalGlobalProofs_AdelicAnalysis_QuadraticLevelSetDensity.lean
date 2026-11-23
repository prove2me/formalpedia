-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuadraticLevelSetDensity
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuadraticLevelSetDensity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:11:38.99229+00:00
-- url     : https://prove2.me/theorems/8b713ab4-f849-491f-93a7-267cc031f7a7
-- title:
--   Quadratic Level Set Density
-- statement:
--   Definitions and structural lemmas for Quadratic Level Set Density, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/QuadraticLevelSetDensity.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGaussianFourierStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotentStatement
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
namespace GlobalTheory.CompanionTheory.SW.Core.Dens
def qMap {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (x : InfinitePlace F → ι → ℝ) : InfinitePlace F → ℝ :=
  fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))
def gW {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (P : InfinitePlace F → Matrix ι ι ℝ) (x : InfinitePlace F → ι → ℝ) : ℝ :=
  Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (P w *ᵥ x w))
section
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
end
end GlobalTheory.CompanionTheory.SW.Core.Dens


