-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T12:56:44.749327+00:00
-- url     : https://prove2.me/theorems/aba9512d-aefc-41ea-a074-6d9bea6e48b0
-- title:
--   Theta A
-- statement:
--   Definitions and structural lemmas for Theta A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/ThetaA.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
namespace PI.ScRefExists.TH
variable (I : Formalism.MainNotions.S.AutInst)
def sg : 𝓞 I.E →+* 𝓞 I.E := NumberField.RingOfIntegers.mapRingHom (starRingEnd I.E)
theorem sg_coe (x : 𝓞 I.E) : ((sg I x : 𝓞 I.E) : I.E) = star (x : I.E) := rfl
theorem sg_sg (x : 𝓞 I.E) : sg I (sg I x) = x := by
  apply NumberField.RingOfIntegers.ext
  rw [sg_coe, sg_coe, star_star]
def cj (P : HeightOneSpectrum (𝓞 I.E)) : HeightOneSpectrum (𝓞 I.E) where
  asIdeal := P.asIdeal.comap (sg I)
  isPrime := Ideal.IsPrime.comap _
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    intro h
    have : sg I x ∈ P.asIdeal.comap (sg I) := by
      rw [Ideal.mem_comap, sg_sg]; exact hx
    rw [h, Ideal.mem_bot] at this
    apply hx0
    rw [← sg_sg I x, this, map_zero]
end PI.ScRefExists.TH


