-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:50.07463+00:00
-- url     : https://prove2.me/theorems/f996590e-8fcb-492f-951e-63965ebe2831
-- title:
--   Exists Valued Hecke Char Ramified
-- statement:
--   Definitions and structural lemmas for Exists Valued Hecke Char Ramified, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
namespace GlobalTheory.CMVal.Model
section General
variable {E : Type} [Field E] [NumberField E]
end General
section Integrality
end Integrality
section Symmetry
variable {E : Type} [Field E] [NumberField E]
end Symmetry
section Twist
variable {E : Type} [Field E] [NumberField E]
end Twist
section CM
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
local notation "cj" => IsCMField.ringOfIntegersComplexConj E
end CM
section Cyclotomic
abbrev K : Type := CyclotomicField 21 ℚ
instance : IsCyclotomicExtension {21} ℚ K := CyclotomicField.isCyclotomicExtension 21 ℚ
instance : IsCMField K := IsCyclotomicExtension.Rat.isCMField K (S := {21}) ⟨21, rfl, by norm_num⟩
end Cyclotomic
end GlobalTheory.CMVal.Model


