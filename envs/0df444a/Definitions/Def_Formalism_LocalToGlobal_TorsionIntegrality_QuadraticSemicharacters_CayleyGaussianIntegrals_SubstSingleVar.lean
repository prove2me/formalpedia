-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_SubstSingleVar
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_SubstSingleVar
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:39:33.832831+00:00
-- url     : https://prove2.me/theorems/af86a2ae-0c0d-44f6-b73e-fd8525f2481f
-- title:
--   Subst Single Var
-- statement:
--   Definitions and structural lemmas for Subst Single Var, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/SubstSingleVar.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.H
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.C (IsLogPair)
open Formalism.L2.Th1.E (tensor4 matCoord thetaProd)
namespace FormalGroupLawNegation
section Formal
variable {K : Type} [Field K] {n : Type} [Fintype n]
end Formal
section Map
variable {K₀ K : Type} [Field K₀] [Field K] (ι : K₀ →+* K) {n : Type} [Fintype n]
end Map
end FormalGroupLawNegation
end Formalism.L2.Th1.H


