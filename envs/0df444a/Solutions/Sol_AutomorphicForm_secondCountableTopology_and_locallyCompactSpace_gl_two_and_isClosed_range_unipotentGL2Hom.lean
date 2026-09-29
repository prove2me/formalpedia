-- Prove2me | solution 1 for AutomorphicForm.secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/68f43cbc-db5d-5b30-9c5b-b3feae9a9496

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory Topology

theorem solution
    (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) ∧
    LocallyCompactSpace (GL (Fin 2) (v.adicCompletion K)) ∧
    IsClosed ((unipotentGL2Hom (R := v.adicCompletion K)).range : Set (GL (Fin 2) (v.adicCompletion K))) ∧
    (∀ {_m : MeasurableSpace ↥(unipotentGL2Hom (R := v.adicCompletion K)).range}
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion K)).range) [μN.IsMulLeftInvariant],
      μN.IsMulRightInvariant) := by
  haveI i1 : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    show SecondCountableTopology (Fin 2 → Fin 2 → v.adicCompletion K) from inferInstance
  haveI i2 : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    show LocallyCompactSpace (Fin 2 → Fin 2 → v.adicCompletion K) from inferInstance
  haveI i3 : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI i4 : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Units.isEmbedding_embedProduct (M := Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).isInducing.secondCountableTopology
  · exact (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).locallyCompactSpace
  · have hset : ((unipotentGL2Hom (R := v.adicCompletion K)).range : Set (GL (Fin 2) (v.adicCompletion K))) =
        {g : GL (Fin 2) (v.adicCompletion K) |
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 = 1 ∧
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = 1 ∧
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_setOf_eq]
      constructor
      · rintro ⟨x, rfl⟩
        simp [unipotentGL2Hom, unipotentGL2]
      · rintro ⟨h00, h11, h10⟩
        refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1), ?_⟩
        apply Units.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [unipotentGL2Hom, unipotentGL2, h00, h11, h10]
    rw [hset]
    have hc : Continuous (fun g : GL (Fin 2) (v.adicCompletion K) => (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) :=
      Units.continuous_val
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · exact isClosed_eq ((continuous_apply_apply 0 0).comp hc) continuous_const
    · exact isClosed_eq ((continuous_apply_apply 1 1).comp hc) continuous_const
    · exact isClosed_eq ((continuous_apply_apply 1 0).comp hc) continuous_const
  · intro _m μN _
    have hcomm : ∀ a b : ↥(unipotentGL2Hom (R := v.adicCompletion K)).range, a * b = b * a := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp ha
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hb
      apply Subtype.ext
      simp only [Subgroup.coe_mul, ← map_mul, mul_comm x y]
    refine ⟨fun g => ?_⟩
    have hfun : (fun x : ↥(unipotentGL2Hom (R := v.adicCompletion K)).range => x * g) = (fun x => g * x) :=
      funext (fun x => hcomm x g)
    rw [hfun]
    exact MeasureTheory.map_mul_left_eq_self μN g

end S_AutomorphicForm_secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom
end P2MW
export P2MW.S_AutomorphicForm_secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom (solution)
