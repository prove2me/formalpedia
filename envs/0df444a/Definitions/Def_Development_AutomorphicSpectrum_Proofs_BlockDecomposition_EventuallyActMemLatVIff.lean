-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EventuallyActMemLatVIff
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EventuallyActMemLatVIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:32.608965+00:00
-- url     : https://prove2.me/theorems/9071e4b6-fe82-4580-a61a-fdd25ca250de
-- title:
--   Eventually Act Mem Lat VIff
-- statement:
--   Definitions and structural lemmas for Eventually Act Mem Lat VIff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/EventuallyActMemLatVIff.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Mass HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.LatFix
section Gen
variable {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
end Gen
section Adelic
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
end Adelic
end GlobalTheory.CompanionTheory.SW.LatFix


