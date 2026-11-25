-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_AbstractUnique
-- name    : GroundTheory_GlobalFields_NormResidueSymbol_AbstractUnique
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:38:09.656624+00:00
-- url     : https://prove2.me/theorems/bcad6846-3176-419a-9c0a-bfee249da670
-- title:
--   Abstract Unique
-- statement:
--   Definitions and structural lemmas for Abstract Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/AbstractUnique.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_Abstract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open Filter Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing
noncomputable section
namespace IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
def localEmbeddingSubgroup : Subgroup (IdeleGroup K) :=
  (⨆ v : HeightOneSpectrum (𝓞 K), (finiteEmbedding v).range) ⊔
    ⨆ w : InfinitePlace K, (infiniteEmbedding w).range
variable {K}
end IdeleGroup
namespace IdeleMap
open IdeleGroup
variable {K : Type*} [Field K] [NumberField K] {G : Type*} [CommGroup G]
  [TopologicalSpace G] [DiscreteTopology G]
  (φ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* G)
  (φinf : ∀ w : InfinitePlace K, (w.Completion)ˣ →* G)
  (hφ : ∀ᶠ v in cofinite,
    (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)
end IdeleMap
end
end GroundTheory.Global


