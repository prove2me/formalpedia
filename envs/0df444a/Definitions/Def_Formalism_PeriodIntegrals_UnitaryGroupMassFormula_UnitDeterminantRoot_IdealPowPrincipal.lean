-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:54:51.88581+00:00
-- url     : https://prove2.me/theorems/55b1f8a7-ff7a-4855-8ba1-4698f5504b51
-- title:
--   Ideal Pow Principal
-- statement:
--   Definitions and structural lemmas for Ideal Pow Principal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitDeterminantRoot/IdealPowPrincipal.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_DetMemOfEntries
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NormLeOneOfRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField nonZeroDivisors
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
open PI Submodule NumberField
def volSet {m : Type} [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) : Set ℂ :=
  {z | ∃ v : m → m → ℂ, (∀ j, v j ∈ Λ) ∧ z = (Matrix.of v).det}
def vol (F : IntermediateField ℚ ℂ) {m : Type} [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)) :
    Submodule (𝓞 F) ℂ :=
  Submodule.span (𝓞 F) (volSet Λ)
section Princ
variable (F : IntermediateField ℚ ℂ)
variable [NumberField F]
abbrev hF : ℕ := Fintype.card (ClassGroup (𝓞 F))
end Princ
end PI.UnitaryGroupMassFormula.UnitDetRoot


