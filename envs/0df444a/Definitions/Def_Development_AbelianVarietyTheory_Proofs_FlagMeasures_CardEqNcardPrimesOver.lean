-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqNcardPrimesOver
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqNcardPrimesOver
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:45.572788+00:00
-- url     : https://prove2.me/theorems/bc003662-312a-454b-b493-c04471c50bbd
-- title:
--   Card Eq Ncard Primes Over
-- statement:
--   Definitions and structural lemmas for Card Eq Ncard Primes Over, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardEqNcardPrimesOver.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_HermitianPerpSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_ColumnDimensionRational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MulVecMemHatSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped TensorProduct ENNReal Pointwise
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ColCmp
namespace GlobalTheory.SplitResidue
end GlobalTheory.SplitResidue


