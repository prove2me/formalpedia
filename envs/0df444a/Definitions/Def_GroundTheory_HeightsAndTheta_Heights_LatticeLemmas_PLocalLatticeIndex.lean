-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalLatticeIndex
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalLatticeIndex
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:17.354577+00:00
-- url     : https://prove2.me/theorems/929afa91-e9e6-5e65-9e0b-be0a3e431bd8
-- title:
--   PLocal Lattice Index
-- statement:
--   Definitions and structural lemmas for PLocal Lattice Index, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PLocalLatticeIndex.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocalLatticeIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField IsDedekindDomain TensorProduct Module
noncomputable section
section Card
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
end Card
section General
variable {K : Type*} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
  {E : Type*} [AddCommGroup E] [Module (v.adicCompletion K) E]
  [Module (v.adicCompletionIntegers K) E]
  [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) E]
end General
end
end GroundTheory.Heights₂.Heights.LatticeLemmas


