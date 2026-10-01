-- Prove2me | Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
-- name    : LocalConjugacy_Proof_FiniteAbelianCohomology
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T14:18:44.054081+00:00
-- url     : https://prove2.me/theorems/dd911967-431b-460a-a954-60f8a3c6cf8c
-- title:
--   The coboundary homomorphism
-- statement:
--   For an action on an abelian coefficient group and a fixed cocycle, the homomorphism whose range describes the relevant coboundaries in the finite cohomology argument.
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

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
namespace FiniteAbelianCohomology

variable {J A : Type*} [Group J] [CommGroup A]

/-- Coboundaries form a subgroup when the coefficient group is abelian. -/
def coboundaryHom (a : J →* MulAut A) : A →* (J → A) where
  toFun n x := n⁻¹ * a x n
  map_one' := by ext x; simp
  map_mul' n m := by
    ext x
    simp only [mul_inv_rev, map_mul, Pi.mul_apply]
    ac_rfl





end FiniteAbelianCohomology
end LocalConjugacy

end LocalConjugacy.Proof

end


