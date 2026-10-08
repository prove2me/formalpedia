-- Prove2me | Definitions.Def_LittleFinitistic
-- name    : LittleFinitistic
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:17.542555+00:00
-- url     : https://prove2.me/theorems/5de66e6b-9415-4cfc-9149-e39f1a85aaca
-- statement:
--   For a ring A in universe u, littleFinitisticDimension(A) is defined as an element of WithBot ℕ∞ (the natural numbers with infinity, plus a bottom element): the supremum of projectiveDimension(M) over all (left) A-modules M in ModuleCat A that are finitely generated and whose projective dimension is strictly less than ⊤, that is, finite. This is the little finitistic dimension of A, the largest finite projective dimension attained by a finitely generated module. The zero module, whose projective dimension is the bottom element, is included in the range, so the supremum is never over an empty family. The block only gives this definition and states no theorem about its value, and no assumptions such as commutativity, Noetherianity or finite-dimensionality are imposed on A.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/LittleFinitistic.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/LittleFinitistic.lean; bytes 239..540
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Finiteness.Defs

namespace OAI

noncomputable section

open CategoryTheory

namespace LittleFinitistic

universe u

def littleFinitisticDimension (A : Type u) [Ring A] : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{u} A) (_ : Module.Finite A M) (_ : projectiveDimension M < ⊤),
    projectiveDimension M

namespace Main



end Main
end LittleFinitistic
end
end OAI


