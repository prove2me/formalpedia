-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_CharpolyEqOfIsNilpotentSub
-- name    : Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_CharpolyEqOfIsNilpotentSub
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T18:11:01.152059+00:00
-- url     : https://prove2.me/theorems/cfa004d4-8dd3-4570-bd3f-3057af02b027
-- title:
--   Charpoly Eq Of Is Nilpotent Sub
-- statement:
--   Definitions and structural lemmas for Charpoly Eq Of Is Nilpotent Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/CharpolyEqOfIsNilpotentSub.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFrobeniusSemisimplification
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNilpotentZpowSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAevalEqSmulOnEigenspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
namespace GlobalTheory.WeilDeligne
section Exp
open IsNilpotent
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]
end Exp
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
def IsFrobSS (ρ : Weil h → End ℂ V) (N : End ℂ V) (a : WDRep h V) : Prop :=
  a.N = N ∧ ∀ g, Commute (a.ρ g) (ρ g) ∧ IsNilpotent (ρ g - a.ρ g)
end GlobalTheory.WeilDeligne


