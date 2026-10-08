-- Prove2me | Definitions.Def_MazurTransfer_Order18CompositumField
-- name    : MazurTransfer_Order18CompositumField
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-06T18:02:23.472082+00:00
-- url     : https://prove2.me/theorems/342191d8-d292-46cf-9c55-f4608b5797a4
-- title:
--   Order-18 compositum field from certified relative irreducibility
-- statement:
--   Let $K=\mathbb Q[T]/(T^3-3T-1)$ and let $M=K[S]/(S^3-3S-10)$. This interface equips the original relative algebra $M$ with its field and number-field structures, using only the separately proved irreducibility of $S^3-3S-10$ over $K$ and Mathlib’s finite-extension constructor. It includes no class-number, unit, Selmer or torsion assertion. The named downstream consumers are the principal-ring certificate and the original order-18 global Selmer descent.
-- source:
--   User MazurTheorem WIP, commit 54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact source AST declarations with Apache-2.0 headers retained. Original constructor types are unchanged; constructor values refer solely to the accepted public relative irreducibility result and standard finite-extension laws.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
import Definitions.Def_MazurTransfer_Order18RelativeAlgebra
import Theorems.Thm_MazurTransfer_order18_relative_two_division_irreducible

noncomputable section
open Polynomial
open MazurTorsion.XOneEighteenTwoDivisionArithmetic

namespace MazurTorsion.XOneEighteenTwoDivisionClassNumber

instance relativePolynomial_irreducibleFact :
    Fact (Irreducible relativePolynomial) :=
  ⟨MazurTransfer.order18_relative_two_division_irreducible⟩


/-- The now-field-valued relative algebra is a number field. -/
instance compositumNumberField : NumberField M :=
  letI : Module.Finite Q.K M :=
    (AdjoinRoot.powerBasis MazurTransfer.order18_relative_two_division_irreducible.ne_zero).finite
  NumberField.of_module_finite Q.K M


end MazurTorsion.XOneEighteenTwoDivisionClassNumber
end


