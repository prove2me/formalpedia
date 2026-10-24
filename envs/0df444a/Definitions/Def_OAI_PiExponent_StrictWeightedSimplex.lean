-- Prove2me | Definitions.Def_OAI_PiExponent_StrictWeightedSimplex
-- name    : OAI_PiExponent_StrictWeightedSimplex
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-24T04:40:14.800741+00:00
-- url     : https://prove2.me/theorems/43d098eb-6fe6-4790-a6af-89b4df505e17
-- title:
--   Strict weighted exponent simplex and its cardinality
-- statement:
--   Define nonnegative integer exponent vectors whose weighted sum is strictly below T, and their natural cardinality. The volume child explicitly establishes finiteness under positive weights.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite

open scoped BigOperators

namespace OAI.PiExponent.FormalInterpolation

/-- Nonnegative integer exponent vectors of weight strictly below the cutoff. -/
def strictWeightedSimplex {ι : Type*} [Fintype ι]
    (v : ι → Rat) (T : Real) : Type _ :=
  {a : ι → Nat // (∑ i, (v i : Real) * (a i : Real)) < T}

/-- The natural cardinality of a strict weighted simplex. Positivity of the
weights implies that the simplex is finite. -/
noncomputable def strictWeightedSimplexCard {ι : Type*} [Fintype ι]
    (v : ι → Rat) (T : Real) : Nat :=
  Nat.card (strictWeightedSimplex v T)

end OAI.PiExponent.FormalInterpolation


