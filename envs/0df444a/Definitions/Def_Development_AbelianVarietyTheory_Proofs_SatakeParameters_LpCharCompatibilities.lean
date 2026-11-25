-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LpCharCompatibilities
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_LpCharCompatibilities
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T16:58:35.590101+00:00
-- url     : https://prove2.me/theorems/f481127c-ad5c-4f66-9070-ad85193c367c
-- title:
--   Lp Char Compatibilities
-- statement:
--   Definitions and structural lemmas for Lp Char Compatibilities, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/LpCharCompatibilities.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
namespace GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' V'' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup V''] [Module ℂ V''] [FiniteDimensional ℂ V'']
namespace WDRep
end WDRep
namespace WD
end WD
end GlobalTheory.WeilDeligne


