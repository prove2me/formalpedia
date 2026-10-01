-- Prove2me | Definitions.Def_LocalConjugacy_Proof_HallCohomology
-- name    : LocalConjugacy_Proof_HallCohomology
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T15:31:54.64193+00:00
-- url     : https://prove2.me/theorems/8faea444-f028-4570-aec5-9d6064c1d6bd
-- title:
--   Prime support of profinite quotients
-- statement:
--   The predicate that every finite continuous quotient has order supported on a specified set of primes, used to express complementary prime conditions in Hall cohomology.
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
import Definitions.Def_LocalConjugacy_Proof_CocycleZorn
import Definitions.Def_LocalConjugacy_Proof_FiniteHall
import Definitions.Def_LocalConjugacy_Proof_SupersolvableStructure
import Definitions.Def_LocalConjugacy_Proof_ProfiniteHall

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

/-- Every finite continuous quotient has all its prime divisors in `π`. -/
def HasProPrimes (π : Set ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : OpenNormalSubgroup G, HasPrimes π (G ⧸ U.toSubgroup)

















section Cocycles
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [IsTopologicalGroup N]
  [MulDistribMulAction J N] [ContinuousSMul J N]





end Cocycles
end LocalConjugacy

end LocalConjugacy.Proof

end


