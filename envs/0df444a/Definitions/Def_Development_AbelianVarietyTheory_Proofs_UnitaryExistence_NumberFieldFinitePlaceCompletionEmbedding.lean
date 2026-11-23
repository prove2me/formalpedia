-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NumberFieldFinitePlaceCompletionEmbedding
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NumberFieldFinitePlaceCompletionEmbedding
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:30.9478+00:00
-- url     : https://prove2.me/theorems/861346df-0ed6-4931-9bc2-89d3949e8772
-- title:
--   Number Field Finite Place Completion Embedding
-- statement:
--   Definitions and structural lemmas for Number Field Finite Place Completion Embedding, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/NumberFieldFinitePlaceCompletionEmbedding.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory
open Formalism.L2.Pj Formalism.L2.PjFree
open IsDedekindDomain NumberField HeightOneSpectrum Filter
open scoped WithZero Topology
namespace AdicCompl
section Compl
variable {R : Type} [CommRing R] [IsDedekindDomain R] {L : Type} [Field L] [Algebra R L]
  [IsFractionRing R L] (w : HeightOneSpectrum R)
local notation "Lw" => adicCompletion L w
local notation "Ow" => adicCompletionIntegers L w
def kMap : L →+* FractionRing Ow :=
  ((FractionRing.algEquiv Ow Lw).symm : Lw →+* FractionRing Ow).comp (algebraMap L Lw)
end Compl
end AdicCompl
end GlobalTheory


