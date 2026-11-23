-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NumberFieldPrimeZetaSumAddLogIsBigO
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NumberFieldPrimeZetaSumAddLogIsBigO
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:59:15.132639+00:00
-- url     : https://prove2.me/theorems/10fd1402-eba4-4ddf-867b-fd052816fee0
-- title:
--   Number Field Prime Zeta Sum Add Log Is Big O
-- statement:
--   Definitions and structural lemmas for Number Field Prime Zeta Sum Add Log Is Big O, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NumberFieldPrimeZetaSumAddLogIsBigO.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NotInjectiveTwoPrimesEqualNormCofinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
namespace GlobalTheory.ChebCyc
end GlobalTheory.ChebCyc


