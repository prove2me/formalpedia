-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_SmulMemSpanSmul
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_SmulMemSpanSmul
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T09:34:46.054926+00:00
-- url     : https://prove2.me/theorems/3c499ea8-0858-5198-af18-94b3067c6500
-- title:
--   Smul Mem Span Smul
-- statement:
--   Definitions and structural lemmas for Smul Mem Span Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IndexCalculation/SmulMemSpanSmul.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.IdxW
open NumberField IsDedekindDomain Module
section Gen
variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
end Gen
variable {K : Type} [Field K] [NumberField K]
instance instIsPrimeW (w : HeightOneSpectrum (𝓞 K)) : w.asIdeal.IsPrime := w.isPrime
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end PI.Dv.IdxW


