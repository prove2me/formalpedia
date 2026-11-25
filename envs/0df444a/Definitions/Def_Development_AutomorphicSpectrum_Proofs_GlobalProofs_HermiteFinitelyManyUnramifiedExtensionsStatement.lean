-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_HermiteFinitelyManyUnramifiedExtensionsStatement
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_HermiteFinitelyManyUnramifiedExtensionsStatement
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:26:12.869108+00:00
-- url     : https://prove2.me/theorems/03728ba7-a58e-59f6-8bad-516e7dac3243
-- title:
--   Hermite Finitely Many Unramified Extensions Statement
-- statement:
--   Definitions and structural lemmas for Hermite Finitely Many Unramified Extensions Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/HermiteFinitelyManyUnramifiedExtensionsStatement.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_HermiteFinitelyManyUnramifiedExtensions
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual


