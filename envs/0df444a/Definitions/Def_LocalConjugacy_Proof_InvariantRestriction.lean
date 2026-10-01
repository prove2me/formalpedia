-- Prove2me | Definitions.Def_LocalConjugacy_Proof_InvariantRestriction
-- name    : LocalConjugacy_Proof_InvariantRestriction
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T14:33:47.127398+00:00
-- url     : https://prove2.me/theorems/16763fb0-bf7b-45a8-a2e6-c5ad829e6621
-- title:
--   Twisting and conjugating cocycles
-- statement:
--   Conjugation of subgroup domains and the associated twisted cocycle, together with compatibility of twisting with the coboundary equivalence relation.
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

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section General

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [IsTopologicalGroup J] [TopologicalSpace N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

/-- Conjugation by `j⁻¹` on a normal subgroup, kept in the ambient group. -/
def conjugateDomain (K : Subgroup J) [K.Normal] (j : J) : K →* K where
  toFun x := ⟨j⁻¹ * x * j, by
    simpa using (inferInstance : K.Normal).conj_mem x x.property j⁻¹⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp [mul_assoc]

/-- Conjugation action on cocycles on a normal subgroup. -/
def twistCocycle {K : Subgroup J} [K.Normal] (f : Cocycle (N := N) K) (j : J) :
    Cocycle (N := N) K where
  toFun x := j • f.toFun (conjugateDomain K j x)
  continuous_toFun := by
    apply Continuous.const_smul
    apply f.continuous_toFun.comp
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  map_mul x y := by
    rw [(conjugateDomain K j).map_mul, f.map_mul, smul_mul', smul_smul, smul_smul]
    congr 1
    change (j * (j⁻¹ * (x : J) * j)) • _ = ((x : J) * j) • _
    simp [mul_assoc]



theorem twist_cohomologous {K : Subgroup J} [K.Normal]
    {f g : Cocycle (N := N) K} (h : Cohomologous f g) (j : J) :
    Cohomologous (twistCocycle f j) (twistCocycle g j) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨j • n, fun x => ?_⟩
  change j • g.toFun (conjugateDomain K j x) =
    (j • n)⁻¹ * (j • f.toFun (conjugateDomain K j x)) * ((x : J) • (j • n))
  rw [hn]
  simp only [smul_mul', smul_inv', smul_smul]
  congr 1
  change (j * (j⁻¹ * (x : J) * j)) • n = ((x : J) * j) • n
  simp [mul_assoc]





end General

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

set_option linter.unusedVariables false



end LocalConjugacy

end LocalConjugacy.Proof

end


