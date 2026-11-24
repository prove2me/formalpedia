-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_AdelicCharacterRationalDualImports
-- name    : Development_AutomorphicSpectrum_Proofs_MembershipProofs_AdelicCharacterRationalDualImports
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:38.542432+00:00
-- url     : https://prove2.me/theorems/26f491f3-f321-4a9b-8fae-338d276f3ffc
-- title:
--   Adelic Character Rational Dual Imports
-- statement:
--   Definitions and structural lemmas for Adelic Character Rational Dual Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/AdelicCharacterRationalDualImports.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
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
namespace GlobalTheory.CompanionTheory.ThetaUniq
def cosetInd (F : Type) [Field F] [NumberField F] {κ : Type} (N : ℕ) (d : κ → F) :
    (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  Set.indicator {x | ∀ i, ∃ u : FiniteAdeleRing (𝓞 F) F, (∀ v, u v ∈ v.adicCompletionIntegers F) ∧
    x i = algebraMap F (FiniteAdeleRing (𝓞 F) F) (d i) + N • u} 1
end GlobalTheory.CompanionTheory.ThetaUniq
end


