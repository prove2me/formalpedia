-- Prove2me | Definitions.Def_MazurTransfer_OriginalNineteenRootsCyclotomicPowerData20261020
-- name    : MazurTransfer_OriginalNineteenRootsCyclotomicPowerData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T18:47:38.890227+00:00
-- url     : https://prove2.me/theorems/74666151-0036-4e08-b1ed-66d51d6d865b
-- title:
--   Original natural cyclotomic exponent on literal nineteenth roots
-- statement:
--   Retain the original natural representative of the modular nineteenth cyclotomic character, with both original prime and literal-roots module providers. Its complete original type and whole value, both provider types and the whole module value, and original literal-roots, fixed representation and thirteenth-character contexts are independently checked. Root-power, representation and twist identities remain separate theorem interfaces. Named downstream consumer: cyclotomic Hopf classification and descent for the same selected arithmetic character quotients at nineteen.
-- source:
--   MazurTheorem NineteenRootsCyclotomicPower by Vas and contributors; same literal roots, fixed representations and natural exponent, Apache-2.0.

import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Definitions.Def_MazurTransfer_Order13ActualOrderedCharacterContinuousH1OriginalChosenQuotientsAndKummerDataFixedKernelActionsAndContinuousNamespacesV320261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the SAME natural exponent acts on every literal nineteenth
root in the field and on the PREVIOUSLY FIXED rootsRepresentation.
The actual inverse-character twist has this action on the character kernel.
Named downstream consumer: cyclotomic Hopf classification of the selected
pi quotient, and descent for the selected conjugate-pi quotient at nineteen.
-/

noncomputable section
namespace MazurTransfer.NineteenRootsCyclotomicPower
open NineteenRootsGaloisRepresentation RepresentationCharacterTwist
variable (K : Type) [Field K] [CharZero K]
local instance instFactPrimeOfNatNat_nineteenRootsCyclotomicPower : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_nineteenRootsCyclotomicPower : Module (ZMod 19) (Additive (Roots K)) := rootsZModModule K

def exponent (σ : K ≃ₐ[ℚ] K) : ℕ :=
  (modularCyclotomicCharacter.toFun 19 σ.toRingEquiv).val









variable [IsGalois ℚ K] [IsAlgClosed K]
open Order13ActualOrderedCharacterContinuousH1 Order13ActualCyclotomicThirteenKernelCharacter



end MazurTransfer.NineteenRootsCyclotomicPower
#print axioms MazurTransfer.NineteenRootsCyclotomicPower.exponent
#print axioms MazurTransfer.NineteenRootsCyclotomicPower.instFactPrimeOfNatNat_nineteenRootsCyclotomicPower
#print axioms MazurTransfer.NineteenRootsCyclotomicPower.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_nineteenRootsCyclotomicPower


