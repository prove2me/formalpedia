-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianSumOfCounting
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianSumOfCounting
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:29.043794+00:00
-- url     : https://prove2.me/theorems/e9909e3e-935d-489c-82c8-28030e5975c4
-- title:
--   Gaussian Sum Of Counting
-- statement:
--   Definitions and structural lemmas for Gaussian Sum Of Counting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianSumOfCounting.lean

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
namespace GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
noncomputable def wt (c : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 1 else Real.exp (-(c * 4 ^ j / 4))
end GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic


