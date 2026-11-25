-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PIntegralPointOfAlgebraicDomain
-- name    : GroundTheory_HeightsAndTheta_Heights_LocalDensities_PIntegralPointOfAlgebraicDomain
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:38:37.617343+00:00
-- url     : https://prove2.me/theorems/69f1b33f-1a37-52c6-9a67-bc23db4e6fe6
-- title:
--   PIntegral Point Of Algebraic Domain
-- statement:
--   Definitions and structural lemmas for PIntegral Point Of Algebraic Domain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PIntegralPointOfAlgebraicDomain.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsIntegralPointAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_NormLeOneIffIsIntegralElemOfEquiv
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FourB
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
noncomputable section
namespace IntegralPointOfAlgebraicDomain
section FractionField
variable {F : Type*} [Field F] [NumberField F] {S : Type*} [CommRing S]
  [Algebra (𝓞 F) S] {K : Type*} [Field K] [Algebra S K] [IsFractionRing S K] [Algebra F K]
end FractionField
section Place
variable {K : Type*} [Field K] {S : Type*} [CommRing S]
  [Algebra S K] [IsFractionRing S K] (M : Ideal S) [M.IsMaximal]
end Place
section Completion
open GroundTheory.Global GroundTheory.Global.AdicLiesOver
variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver v.asIdeal]
end Completion
end IntegralPointOfAlgebraicDomain
end
end GroundTheory.Heights₂.Heights.FourB


