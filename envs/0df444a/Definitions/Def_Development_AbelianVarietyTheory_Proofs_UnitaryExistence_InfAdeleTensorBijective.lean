-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:35.734617+00:00
-- url     : https://prove2.me/theorems/15d99ccf-54d5-43d1-8bfd-83ded0a18461
-- title:
--   Inf Adele Tensor Bijective
-- statement:
--   Definitions and structural lemmas for Inf Adele Tensor Bijective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/InfAdeleTensorBijective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
namespace GlobalTheory.InfAdeleCM
variable {F : Type} [Field F] [NumberField F]
def ext (σ : F →+* ℂ) : InfiniteAdeleRing F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk σ)).comp
    (Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) (InfinitePlace.mk σ))
variable {E : Type} [Field E] [NumberField E] [Algebra F E]
end GlobalTheory.InfAdeleCM


