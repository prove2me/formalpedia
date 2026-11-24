-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_LatticeIdealNonzero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_LatticeIdealNonzero
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T10:22:27.657494+00:00
-- url     : https://prove2.me/theorems/73a33e49-7e79-46b5-aeb1-9fffd3617392
-- title:
--   Lattice Ideal Nonzero
-- statement:
--   Definitions and structural lemmas for Lattice Ideal Nonzero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdeleClassFiniteness/LatticeIdealNonzero.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_ExistsNeZeroMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdeleClassFiniteness_BorelGL
import Theorems.Thm_PIW_ClassFinD_Icf_exists_ne_zero_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PIW.ClassFinD.Icf
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]
def IsIntU (b : (FiniteAdeleRing (𝓞 F) F)ˣ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 F), Valued.v ((b : FiniteAdeleRing (𝓞 F) F) w) ≤ 1
theorem latI_ne_bot (b : (FiniteAdeleRing (𝓞 F) F)ˣ) : latI b ≠ ⊥ := by
  obtain ⟨r, hr, hmem⟩ := exists_ne_zero_mem b
  intro h
  rw [h, Ideal.mem_bot] at hmem
  exact hr hmem
def latticeIdealNonzero (b : (FiniteAdeleRing (𝓞 F) F)ˣ) : nonZeroDivisors (Ideal (𝓞 F)) :=
  ⟨latI b, mem_nonZeroDivisors_of_ne_zero (latI_ne_bot b)⟩
def cls (b : (FiniteAdeleRing (𝓞 F) F)ˣ) : ClassGroup (𝓞 F) := ClassGroup.mk0 (latticeIdealNonzero b)
end PIW.ClassFinD.Icf
namespace PIW.ClassFinD
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Icf
end PIW.ClassFinD
end


