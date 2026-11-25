-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyEqOfTracePowers
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyEqOfTracePowers
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T16:55:14.164741+00:00
-- url     : https://prove2.me/theorems/499f457b-0d4b-4102-a71c-21842263c362
-- title:
--   Charpoly Eq Of Trace Powers
-- statement:
--   Definitions and structural lemmas for Charpoly Eq Of Trace Powers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyEqOfTracePowers.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
namespace GlobalTheory.TracePowCharpoly
open Polynomial Finset
end GlobalTheory.TracePowCharpoly
namespace GlobalTheory.TracePowCharpoly
open Polynomial
end GlobalTheory.TracePowCharpoly


