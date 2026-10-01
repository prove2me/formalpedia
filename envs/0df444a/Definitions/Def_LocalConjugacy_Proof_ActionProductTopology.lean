-- Prove2me | Definitions.Def_LocalConjugacy_Proof_ActionProductTopology
-- name    : LocalConjugacy_Proof_ActionProductTopology
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T15:21:19.112128+00:00
-- url     : https://prove2.me/theorems/b54c3dee-05df-4ded-8d88-df614ca73de8
-- title:
--   The topology of an action semidirect product
-- statement:
--   The homeomorphism from the action semidirect product to the product space, continuity of both coordinate maps, and the induced topological-group and profinite instances.
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

/-- The declared semidirect-product topology is the ordinary product topology. -/
def actionProductHomeomorph : ActionProduct J N ≃ₜ N × J where
  toEquiv := SemidirectProduct.equivProd
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

theorem actionProduct_continuous_left : Continuous (fun x : ActionProduct J N => x.left) :=
  continuous_fst.comp actionProductHomeomorph.continuous_toFun

theorem actionProduct_continuous_right : Continuous (fun x : ActionProduct J N => x.right) :=
  continuous_snd.comp actionProductHomeomorph.continuous_toFun





instance actionProduct_topologicalGroup [IsTopologicalGroup J] [IsTopologicalGroup N]
    [ContinuousSMul J N] : IsTopologicalGroup (ActionProduct J N) where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    exact ((actionProduct_continuous_left.comp continuous_fst).mul
      ((actionProduct_continuous_right.comp continuous_fst).smul
        (actionProduct_continuous_left.comp continuous_snd))).prodMk
      ((actionProduct_continuous_right.comp continuous_fst).mul
        (actionProduct_continuous_right.comp continuous_snd))
  continuous_inv := by
    apply continuous_induced_rng.mpr
    exact (actionProduct_continuous_right.inv.smul actionProduct_continuous_left.inv).prodMk
      actionProduct_continuous_right.inv

instance actionProduct_profinite [Profinite J] [DiscreteTopology N] [Finite N]
    [ContinuousSMul J N] : Profinite (ActionProduct J N) where
  toIsTopologicalGroup := inferInstance
  toCompactSpace := actionProductHomeomorph.symm.compactSpace
  toT2Space := actionProductHomeomorph.symm.t2Space
  toTotallyDisconnectedSpace := actionProductHomeomorph.symm.totallyDisconnectedSpace

end LocalConjugacy

end LocalConjugacy.Proof

end


