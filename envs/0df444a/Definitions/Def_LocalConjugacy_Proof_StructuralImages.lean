-- Prove2me | Definitions.Def_LocalConjugacy_Proof_StructuralImages
-- name    : LocalConjugacy_Proof_StructuralImages
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-30T14:16:08.139577+00:00
-- url     : https://prove2.me/theorems/004dd3cf-c7bd-43f9-833f-823fe36accad
-- title:
--   Supersolvability under surjective homomorphisms
-- statement:
--   Transport of a normal cyclic-factor series through a surjective group homomorphism. This structural proof is needed in the finite-quotient constructions.
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

/-! Supporting definitions and the structural proofs required by their types and values. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Algebra
variable {G F : Type*} [Group G] [Group F]

theorem supersolvable_of_surjective (hG : Supersolvable G) (f : G →* F)
    (hs : Function.Surjective f) : Supersolvable F := by
  obtain ⟨n, s, h0, hn, hm, hnorm, hstep⟩ := hG
  refine ⟨n, fun i => (s i).map f, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [h0, Subgroup.map_bot]
  · dsimp only
    rw [hn, Subgroup.map_top_of_surjective f hs]
  · exact fun i j hij => Subgroup.map_mono (hm hij)
  · intro i
    letI := hnorm i
    exact (hnorm i).map f hs
  · intro i hi
    obtain ⟨x, hx⟩ := hstep i hi
    refine ⟨f x, ?_⟩
    dsimp only
    rw [hx, Subgroup.map_sup, MonoidHom.map_zpowers]



end Algebra

section Topology
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [TopologicalSpace F] [DiscreteTopology F]







end Topology

section Discrete
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]





end Discrete
end LocalConjugacy

end LocalConjugacy.Proof

end


