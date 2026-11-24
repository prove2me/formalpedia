-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimesInProgressionsRelativeOfTzRat
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimesInProgressionsRelativeOfTzRat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:26.179865+00:00
-- url     : https://prove2.me/theorems/328d4861-09c7-42fc-b038-1565f56a16cd
-- title:
--   Primes In Progressions Relative Of Tz Rat
-- statement:
--   Definitions and structural lemmas for Primes In Progressions Relative Of Tz Rat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/PrimesInProgressionsRelativeOfTzRat.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__IsExcRat_5b5b692fee064c30
import Definitions.Def_Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_PrimesInProgressionsRelative
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZeroFreePrincipal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset DirichletCharacter
open scoped Classical
noncomputable section
namespace GlobalTheory.CompanionTheory.PrimesAP
def fibre {N M : ℕ} [NeZero M] (h : N ∣ M) (a : (ZMod N)ˣ) : Finset (ZMod M)ˣ :=
  Finset.univ.filter (fun u => ZMod.unitsMap h u = a)
end GlobalTheory.CompanionTheory.PrimesAP


