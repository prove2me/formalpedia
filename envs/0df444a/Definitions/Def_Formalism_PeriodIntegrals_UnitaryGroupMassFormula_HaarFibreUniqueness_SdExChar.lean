-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExChar
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExChar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:19:11.615807+00:00
-- url     : https://prove2.me/theorems/906ba5d6-7400-4d69-bdc7-267ae2766116
-- title:
--   Sd Ex Char
-- statement:
--   Definitions and structural lemmas for Sd Ex Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExChar.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExistsUnifFv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DetAdmA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.OmFibreUniq.W.SdChar
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  (ψ0 : Fv F v → ℂ) (hψc : Continuous ψ0) (hψa : ∀ r s, ψ0 (r + s) = ψ0 r * ψ0 s)
  (hψn : ∀ r, ‖ψ0 r‖ = 1)
def Aset : Set (Fv F v) := {t | ∀ c ∈ v.adicCompletionIntegers F, ψ0 (c * t) = 1}
end PI.OmFibreUniq.W.SdChar


