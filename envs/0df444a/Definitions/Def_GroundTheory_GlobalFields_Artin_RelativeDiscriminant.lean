-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
-- name    : GroundTheory_GlobalFields_Artin_RelativeDiscriminant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:47.713804+00:00
-- url     : https://prove2.me/theorems/81989038-f869-4866-8463-0884d9b39bc0
-- title:
--   Relative Discriminant
-- statement:
--   Definitions and structural lemmas for Relative Discriminant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminant.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IsDedekindDomain NumberField Module
namespace GroundTheory.Global
section Def
variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
def relDiscr : Ideal (𝓞 K) :=
  Ideal.relNorm (𝓞 K) (differentIdeal (𝓞 K) (𝓞 M))
end Def
section Multiplicity
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
variable (v : HeightOneSpectrum (𝓞 K))
end Multiplicity
section Tower
variable (K M N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [Field N] [NumberField N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]
end Tower
section Rat
variable (M : Type*) [Field M] [NumberField M]
end Rat
end GroundTheory.Global


