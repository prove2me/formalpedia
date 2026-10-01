-- Prove2me | Definitions.Def_LocalConjugacy_Proof_CocycleInjectivity
-- name    : LocalConjugacy_Proof_CocycleInjectivity
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T15:21:20.964634+00:00
-- url     : https://prove2.me/theorems/c7140080-a009-4dd6-8f4a-6bb64ef09b22
-- title:
--   Intertwining actions and cocycle centralizers
-- statement:
--   The action comparing two cocycles, and the subgroup of coefficient elements centralizing a cocycle. These encode the existence and ambiguity of a coboundary.
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

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

/-- The action whose fixed points are the intertwiners between two cocycles. -/
@[instance_reducible] def intertwiningAction
    (f g : Cocycle (N := N) (⊤ : Subgroup J)) : MulAction J N where
  smul j n := f.toFun ⟨j, trivial⟩ * (j • n) * (g.toFun ⟨j, trivial⟩)⁻¹
  one_smul n := by
    change f.toFun 1 * ((1 : J) • n) * (g.toFun 1)⁻¹ = n
    simp [cocycle_one]
  mul_smul j k n := by
    change f.toFun (⟨j, trivial⟩ * ⟨k, trivial⟩) * ((j * k) • n) *
        (g.toFun (⟨j, trivial⟩ * ⟨k, trivial⟩))⁻¹ =
      f.toFun ⟨j, trivial⟩ *
        (j • (f.toFun ⟨k, trivial⟩ * (k • n) * (g.toFun ⟨k, trivial⟩)⁻¹)) *
        (g.toFun ⟨j, trivial⟩)⁻¹
    simp only [f.map_mul, g.map_mul, Subgroup.coe_mk, mul_smul, mul_inv_rev,
      smul_mul', smul_inv']
    group

/-- The group of automorphisms of one cocycle, regarded as a subgroup of the
coefficient group. Its order is a power of `p` when the coefficients form a
finite `p`-group. -/
def cocycleCentralizer (K : Subgroup J) (f : Cocycle (N := N) (⊤ : Subgroup J)) :
    Subgroup N :=
  ⨅ x : K, ((MulAut.conj (f.toFun ⟨x, trivial⟩) *
    MulDistribMulAction.toMulAut J N x).toMonoidHom).eqLocus (MonoidHom.id N)







end LocalConjugacy

end LocalConjugacy.Proof

end


