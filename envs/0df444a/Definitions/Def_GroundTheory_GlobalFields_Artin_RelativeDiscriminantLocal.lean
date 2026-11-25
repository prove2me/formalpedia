-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminantLocal
-- name    : GroundTheory_GlobalFields_Artin_RelativeDiscriminantLocal
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:05:16.945752+00:00
-- url     : https://prove2.me/theorems/a71743b9-6182-4aa7-87fc-3f2e585a0145
-- title:
--   Relative Discriminant Local
-- statement:
--   Definitions and structural lemmas for Relative Discriminant Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminantLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_LocalFields_Different
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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.LocalField
open scoped WithZero
namespace GroundTheory.Global
section Local
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion M)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion M)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion M)]
end Local
section Global
variable {M : Type*} [Field M] [NumberField M]
end Global
section Comparison
open SemiLocal
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal]
end Comparison
section Main
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
end Main
end GroundTheory.Global


