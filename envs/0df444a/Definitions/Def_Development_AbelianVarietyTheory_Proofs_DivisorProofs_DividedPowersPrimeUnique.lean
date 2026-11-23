-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DividedPowersPrimeUnique
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_DividedPowersPrimeUnique
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:59.677577+00:00
-- url     : https://prove2.me/theorems/af7de7b4-ec06-4b5b-b977-ff980779bff2
-- title:
--   Divided Powers Prime Unique
-- statement:
--   Definitions and structural lemmas for Divided Powers Prime Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DividedPowersPrimeUnique.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
namespace GlobalTheory.DivPowLPrime
def factPrimePart (l m : ℕ) : ℕ := ordCompl[l] m.factorial
def qExp (l m : ℕ) : ℕ := lPrimeExp l * m - padicValNat l m.factorial
def qCoef (O : Type) [CommRing O] (l m : ℕ) : O :=
  (l : O) ^ qExp l m * Ring.inverse (factPrimePart l m : O)
section Lemmas
variable {O : Type} [CommRing O] [IsLocalRing O] {l : ℕ}
end Lemmas
end GlobalTheory.DivPowLPrime


