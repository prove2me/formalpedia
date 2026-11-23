-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMemCyclotomicLayerPrimeRpow
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMemCyclotomicLayerPrimeRpow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:57.706969+00:00
-- url     : https://prove2.me/theorems/87877985-836b-4010-b60a-0eff3bbb2bc4
-- title:
--   Norm Mem Cyclotomic Layer Prime Rpow
-- statement:
--   Definitions and structural lemmas for Norm Mem Cyclotomic Layer Prime Rpow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormMemCyclotomicLayerPrimeRpow.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Cyc
open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open scoped IntermediateField
variable {l : ℕ} [Fact l.Prime]
end GlobalTheory.Cyc


