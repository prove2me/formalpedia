-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:27:33.145875+00:00
-- url     : https://prove2.me/theorems/77e49de8-2302-49c6-b17d-26327201cd9d
-- title:
--   General Integrality
-- statement:
--   Definitions and structural lemmas for General Integrality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/NonsingularJetNorms/GeneralIntegrality.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_inj

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
namespace Formalism.L2.Th1.E
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1 Simeq)
open Formalism.L2.Th1.C (IntMv IntPS IsPt IsLogPair)
open CompatibleChartOperations
namespace GeneratorMatrix
def blk (n : Type) (a : Fin 4) : n ↪ Fin 4 × n := ⟨fun i => (a, i), fun _ _ h => (Prod.mk.inj h).2⟩
section Field
variable {K : Type} [Field K] {n : Type}
end Field
section Lin
variable {K : Type} [Field K] {O m : Type} [CommRing O] [Fintype m] {l linv : PowerSeries K}
end Lin
section Exp
variable {K : Type} [NormedField K] [CharZero K] {n : Type} [Fintype n]
end Exp
end GeneratorMatrix
open GeneratorMatrix
end Formalism.L2.Th1.E


