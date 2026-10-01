-- Prove2me | Definitions.Def_LocalConjugacy_Proof_CocycleProducts
-- name    : LocalConjugacy_Proof_CocycleProducts
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T15:20:55.347478+00:00
-- url     : https://prove2.me/theorems/7e493ab3-045a-46ec-8288-b7ba14a8d5cd
-- title:
--   Products and coefficient maps of cocycles
-- statement:
--   Projection to a component, formation of a product cocycle, and transport along equivariant coefficient homomorphisms.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization interface.

import Mathlib
import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
import Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
import Definitions.Def_LocalConjugacy_Targets
import Definitions.Def_LocalConjugacy_Proof_Compactness
import Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
import Definitions.Def_LocalConjugacy_Proof_StructuralImages
import Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
import Definitions.Def_LocalConjugacy_Proof_AbelianComplement
import Definitions.Def_LocalConjugacy_Proof_QuotientReduction
import Definitions.Def_LocalConjugacy_Proof_Cohomology
import Definitions.Def_LocalConjugacy_Proof_InvariantRestriction
import Definitions.Def_LocalConjugacy_Proof_CocycleActions
import Definitions.Def_LocalConjugacy_Proof_CoprimeCohomology
import Definitions.Def_LocalConjugacy_Proof_CocycleDescent

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Products
variable {J : Type*} [Group J] [TopologicalSpace J]
  {ι : Type*} {N : ι → Type*} [∀ i, Group (N i)] [∀ i, TopologicalSpace (N i)]
  [∀ i, MulDistribMulAction J (N i)]

namespace Cocycle

def component {K : Subgroup J} (f : Cocycle (N := ∀ i, N i) K) (i : ι) :
    Cocycle (N := N i) K where
  toFun x := f.toFun x i
  continuous_toFun := (continuous_apply i).comp f.continuous_toFun
  map_mul x y := congrFun (f.map_mul x y) i

def pi {K : Subgroup J} (f : ∀ i, Cocycle (N := N i) K) :
    Cocycle (N := ∀ i, N i) K where
  toFun x i := (f i).toFun x
  continuous_toFun := continuous_pi fun i => (f i).continuous_toFun
  map_mul x y := funext fun i => (f i).map_mul x y

end Cocycle







end Products

section Coefficients
variable {J N M : Type*} [Group J] [Group N] [Group M]
  [TopologicalSpace J] [TopologicalSpace N] [TopologicalSpace M]
  [MulDistribMulAction J N] [MulDistribMulAction J M]

namespace Cocycle

def mapCoefficient {K : Subgroup J} (f : Cocycle (N := N) K)
    (e : N →* M) (he : Continuous e) (ha : ∀ (j : J) (n : N), e (j • n) = j • e n) :
    Cocycle (N := M) K where
  toFun x := e (f.toFun x)
  continuous_toFun := he.comp f.continuous_toFun
  map_mul x y := by rw [f.map_mul, e.map_mul, ha]

end Cocycle







end Coefficients
end LocalConjugacy

end LocalConjugacy.Proof

end


