-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsCuspReductionBound
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsCuspReductionBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:26.574553+00:00
-- url     : https://prove2.me/theorems/ca65093f-3275-40ca-8955-76ab42d871ce
-- title:
--   Exists Cusp Reduction Bound
-- statement:
--   Definitions and structural lemmas for Exists Cusp Reduction Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsCuspReductionBound.lean

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
namespace GlobalTheory.CompanionTheory.SW.SmallPair
noncomputable def block (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![√τ.im, 0; τ.re / √τ.im, 1 / √τ.im]
noncomputable def bigM {ι : Type} [Fintype ι] [DecidableEq ι] (τ : ι → ℂ) :
    Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ :=
  blockDiagonal fun w => block (τ w)
end GlobalTheory.CompanionTheory.SW.SmallPair


