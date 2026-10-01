-- Prove2me | Definitions.Def_LocalConjugacy_Proof_CoprimeCohomology
-- name    : LocalConjugacy_Proof_CoprimeCohomology
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T14:45:10.135091+00:00
-- url     : https://prove2.me/theorems/2e5c42dd-2e22-4896-b91c-0bf9fcf9b67d
-- title:
--   The affine action of a cocycle
-- statement:
--   A cocycle defines an affine action on the coefficient group by $x\cdot_f n=f(x)(x\cdot n)$. Fixed points of this action express triviality of the cocycle class.
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

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N] [TopologicalSpace J]
  [TopologicalSpace N] [MulDistribMulAction J N]

/-- The affine action attached to a nonabelian cocycle. -/
@[instance_reducible] def cocycleAffineAction {K : Subgroup J}
    (f : Cocycle (N := N) K) : MulAction K N where
  smul x n := f.toFun x * ((x : J) • n)
  one_smul n := by
    change f.toFun 1 * (((1 : K) : J) • n) = n
    simp only [cocycle_one, Subgroup.coe_one, one_smul, one_mul]
  mul_smul x y n := by
    change f.toFun (x * y) * (((x * y : K) : J) • n) =
      f.toFun x * ((x : J) • (f.toFun y * ((y : J) • n)))
    simp only [f.map_mul, Subgroup.coe_mul, mul_smul, smul_mul', mul_assoc]



end LocalConjugacy

end LocalConjugacy.Proof

end


