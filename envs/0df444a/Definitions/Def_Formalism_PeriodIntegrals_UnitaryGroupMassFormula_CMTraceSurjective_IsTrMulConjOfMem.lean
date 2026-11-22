-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMTraceSurjective_IsTrMulConjOfMem
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMTraceSurjective_IsTrMulConjOfMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:49.117773+00:00
-- url     : https://prove2.me/theorems/bf53c05e-a04e-462a-a0f9-565b91330de4
-- title:
--   Is Tr Mul Conj Of Mem
-- statement:
--   Definitions and structural lemmas for Is Tr Mul Conj Of Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMTraceSurjective/IsTrMulConjOfMem.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CMTraceOnto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.CMT
open NumberField
variable {K : Type*} [Field K] [StarRing K]
def conj : 𝓞 K →+* 𝓞 K := RingOfIntegers.mapRingHom (starRingEnd K)
def IsTr (s : 𝓞 K) : Prop := ∃ x : 𝓞 K, x + conj x = s
def trIdeal (K : Type*) [Field K] [StarRing K] : Ideal (𝓞 K) := Ideal.span {s | IsTr s}
end PI.CMT
end


