-- Prove2me | Definitions.Def_FinitisticAsymmetry
-- name    : FinitisticAsymmetry
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:11.570968+00:00
-- url     : https://prove2.me/theorems/003dcb80-90eb-49d2-8f5e-7a283392f097
-- statement:
--   For a ring A and universe level u, littleFinitisticDimension(A) is the supremum, in WithBot ℕ∞, of the projective dimensions of all finitely generated A-modules M (in ModuleCat A) whose projective dimension is finite (below ⊤); bigFinitisticDimension(A) is the analogous supremum over all A-modules of finite projective dimension, with no finite generation requirement. These are the little and big finitistic dimensions of A, and the definitions do not assert that either is finite. InjectivesGenerate(A) is a defined proposition, not an established theorem, formulated in the derived category of A-modules with its standard derived-category structure. It says that for every property P of objects of the derived category that is closed under isomorphisms, triangulated, and closed under colimits indexed by every discrete family of objects indexed by a type I in universe u (arbitrary coproducts), if P holds for every injective A-module regarded as a complex concentrated in degree 0, then P holds for every object X of the derived category. In other words, the injective modules generate the derived category as a triangulated category closed under coproducts.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FinitisticAsymmetry.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FinitisticAsymmetry.lean; bytes 16..913
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open CategoryTheory

namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]

attribute [-instance] CompletePartialOrder.toSupSet in
def littleFinitisticDimension : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{u} A) (_ : Module.Finite A M) (_ : projectiveDimension M < ⊤),
    projectiveDimension M

def bigFinitisticDimension : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{u} A) (_ : projectiveDimension M < ⊤), projectiveDimension M

def InjectivesGenerate : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} A)
  ∀ (P : ObjectProperty (DerivedCategory (ModuleCat.{u} A))),
    P.IsClosedUnderIsomorphisms → P.IsTriangulated →
    (∀ I : Type u, P.IsClosedUnderColimitsOfShape (Discrete I)) →
    (∀ (M : ModuleCat.{u} A), Injective M →
      P ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) →
    ∀ X, P X



end LittleFinitistic
end
end OAI


