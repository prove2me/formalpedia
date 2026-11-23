-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSectionIntegralFiniteIdeleUpToUnits
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSectionIntegralFiniteIdeleUpToUnits
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:02:04.778336+00:00
-- url     : https://prove2.me/theorems/2eab8f9a-5ff0-4dec-905b-c7b8fc382d97
-- title:
--   Exists Ideal Section Integral Finite Idele Up To Units
-- statement:
--   Definitions and structural lemmas for Exists Ideal Section Integral Finite Idele Up To Units, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealSectionIntegralFiniteIdeleUpToUnits.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open scoped nonZeroDivisors
namespace GlobalTheory.CMVal.IdeleIdeal
variable {E : Type} [Field E] [NumberField E]
def ordAt (y : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) : ℕ := (-WithZero.log (Valued.v ((y : Af E) w))).toNat
def idealOf (y : (Af E)ˣ) : Ideal (𝓞 E) := ∏ᶠ w : HeightOneSpectrum (𝓞 E), w.asIdeal ^ ordAt y w
end GlobalTheory.CMVal.IdeleIdeal


