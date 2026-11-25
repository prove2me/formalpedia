-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_HermiteFinitelyManyUnramifiedExtensions
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_HermiteFinitelyManyUnramifiedExtensions
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T02:20:42.088775+00:00
-- url     : https://prove2.me/theorems/0edfe6f7-edd2-44a4-b2d7-40e84b3143b9
-- title:
--   Hermite Finitely Many Unramified Extensions
-- statement:
--   Definitions and structural lemmas for Hermite Finitely Many Unramified Extensions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/HermiteFinitelyManyUnramifiedExtensions.lean

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DifferentDvdRamifiedPrimePowerStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RamifiedPrimeContainsDiscriminantStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
namespace GlobalTheory.CompanionTheory.HermiteMinkowski
noncomputable def bound {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ℕ :=
  (discr F).natAbs * ∏ v ∈ S, v.asIdeal.absNorm
end GlobalTheory.CompanionTheory.HermiteMinkowski


