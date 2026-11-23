-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmBound
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_AsmBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:05:38.382815+00:00
-- url     : https://prove2.me/theorems/080a948c-f9f2-4294-b225-632c9e33d157
-- title:
--   Asm Bound
-- statement:
--   Definitions and structural lemmas for Asm Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionRows/AsmBound.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv
section Gen
variable {K : Type} [Field K] [NumberField K]
def hosEquiv : HeightOneSpectrum (𝓞 K) ≃ {p : Ideal (𝓞 K) // p.IsMaximal} where
  toFun w := ⟨w.asIdeal, w.isMaximal⟩
  invFun p := ⟨p.1, p.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField K)⟩
  left_inv w := by cases w; rfl
  right_inv p := rfl
end Gen
section Deg
variable {K : Type} [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
end Deg
end PI.DvRows


