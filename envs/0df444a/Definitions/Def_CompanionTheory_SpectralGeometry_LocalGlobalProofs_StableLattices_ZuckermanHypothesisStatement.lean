-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZuckermanHypothesisStatement
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZuckermanHypothesisStatement
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T05:03:43.45045+00:00
-- url     : https://prove2.me/theorems/ce27ffc2-3e23-4bf8-a513-95a414a814d1
-- title:
--   Zuckerman Hypothesis Statement
-- statement:
--   Definitions and structural lemmas for Zuckerman Hypothesis Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZuckermanHypothesisStatement.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZuckermanHypothesis
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_BetaAtInfinityZero
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker


