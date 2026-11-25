-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZuckermanHypothesis
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZuckermanHypothesis
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T04:25:14.638812+00:00
-- url     : https://prove2.me/theorems/9691c2bf-4007-5226-bd6c-3a77b431d632
-- title:
--   Zuckerman Hypothesis
-- statement:
--   Definitions and structural lemmas for Zuckerman Hypothesis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ZuckermanHypothesis.lean

import Mathlib
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
noncomputable section
namespace GlobalTheory.CompanionTheory.ZuckTransport
open PI.UpqRep CompanionTheory.LimBd.SchurHpk
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
end GlobalTheory.CompanionTheory.ZuckTransport
end


