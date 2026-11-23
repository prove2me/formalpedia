-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:14.100806+00:00
-- url     : https://prove2.me/theorems/621bcea8-a1a2-4f7f-b06e-c7063a4a7b1f
-- title:
--   Finsum Out Translate
-- statement:
--   Definitions and structural lemmas for Finsum Out Translate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FinsumOutTranslate.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2 Pointwise
namespace GlobalTheory.CompanionTheory.HeckeMul
section Generic
variable {G : Type} [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G]
end Generic
section Hecke
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
end Hecke
end GlobalTheory.CompanionTheory.HeckeMul


