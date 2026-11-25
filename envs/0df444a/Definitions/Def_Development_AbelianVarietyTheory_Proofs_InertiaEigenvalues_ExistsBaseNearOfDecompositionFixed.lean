-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBaseNearOfDecompositionFixed
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBaseNearOfDecompositionFixed
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:32:07.276675+00:00
-- url     : https://prove2.me/theorems/74e6888e-3af1-559e-b913-7e4ef50bdf1d
-- title:
--   Exists Base Near Of Decomposition Fixed
-- statement:
--   Definitions and structural lemmas for Exists Base Near Of Decomposition Fixed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsBaseNearOfDecompositionFixed.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAlgebraMapSubEqSumConjugatesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjPlacesOfSamePrimeBelowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CrtApproxIntegralStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped Pointwise
namespace GlobalTheory
end GlobalTheory


