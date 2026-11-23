-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulMain
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulMain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:36.826262+00:00
-- url     : https://prove2.me/theorems/aadf41d8-3d7a-47b0-9c8c-19e52ff1a01c
-- title:
--   Mul Main
-- statement:
--   Definitions and structural lemmas for Mul Main, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/MulMain.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpOnto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.GalTorsConj.W
open Formalism.L2.Th1.F
def Cj1 (M₁ : IntermediateField ℚ ℂ) (ρ₁ : M₁ →ₐ[ℚ] ℂ) (x x' : ℂ) : Prop :=
  ∃ hx : x ∈ M₁, ρ₁ ⟨x, hx⟩ = x'
section cj1
variable {M₁ : IntermediateField ℚ ℂ} {ρ₁ : M₁ →ₐ[ℚ] ℂ}
end cj1
end PI.GalTorsConj.W
end


