-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaSeriesExistence
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaSeriesExistence
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T13:14:12.048083+00:00
-- url     : https://prove2.me/theorems/b7d55ef6-760d-4918-8c8b-43f4559b9857
-- title:
--   Theta Series Existence
-- statement:
--   Definitions and structural lemmas for Theta Series Existence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/ThetaSeriesExistence.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
namespace PI.ScRefExists.TH
variable (I : Formalism.MainNotions.S.AutInst)
theorem spanG_ne (g : ℕ) (hg : 1 ≤ g) : Ideal.span {(g : 𝓞 I.E)} ≠ 0 := by
  have hg0 : (g : 𝓞 I.E) ≠ 0 := by
    intro h
    have h2 := congrArg (fun x : 𝓞 I.E => (x : I.E)) h
    have h3 : (g : I.E) = 0 := by simpa using h2
    have h4 : g = 0 := by exact_mod_cast h3
    omega
  rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact hg0
def primesG (g : ℕ) (hg : 1 ≤ g) : Finset (HeightOneSpectrum (𝓞 I.E)) :=
  (Ideal.finite_factors (spanG_ne I g hg)).toFinset
end PI.ScRefExists.TH


