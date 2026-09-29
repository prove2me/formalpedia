-- Prove2me | solution 1 for AddMonoidAlgebra.exists_addMonoidHom_forall_bialgHom_single_eq_single
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/604c869f-bc89-59fa-a193-da9de07e1310

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddMonoidAlgebra_exists_addMonoidHom_forall_bialgHom_single_eq_single

set_option autoImplicit false

theorem solution
    {S : Type} [CommRing S] [IsDomain S] (G : Type) [AddCommGroup G]
    (f : AddMonoidAlgebra S G →ₐc[S] AddMonoidAlgebra S G) :
    ∃ M : G →+ G, ∀ g : G, f (AddMonoidAlgebra.single g 1) = AddMonoidAlgebra.single (M g) 1 := by
  classical

  have hgl1 : ∀ g : G, IsGroupLikeElem S (AddMonoidAlgebra.single g (1 : S) : AddMonoidAlgebra S G) := by
    intro g
    refine ⟨?_, ?_⟩
    · rw [AddMonoidAlgebra.counit_single, CommSemiring.counit_apply]
    · rw [AddMonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul]
      rfl
  have hgl : ∀ g : G, IsGroupLikeElem S (f (AddMonoidAlgebra.single g 1)) := fun g => (hgl1 g).map f

  have key : ∀ y : AddMonoidAlgebra S G, IsGroupLikeElem S y → ∃ h, y = AddMonoidAlgebra.single h 1 := by
    intro y hy
    by_contra hne
    push_neg at hne
    have hli := linearIndepOn_isGroupLikeElem (R := S) (A := AddMonoidAlgebra S G)

    have hB : Set.range (fun h : G => (AddMonoidAlgebra.single h (1 : S) : AddMonoidAlgebra S G)) ⊆
        {a | IsGroupLikeElem S a} := by
      rintro _ ⟨h, rfl⟩; exact hgl1 h
    have hyB : y ∉ Set.range (fun h : G => (AddMonoidAlgebra.single h (1 : S) : AddMonoidAlgebra S G)) := by
      rintro ⟨h, rfl⟩; exact hne h rfl
    have hspan : y ∈ Submodule.span S (Set.range (fun h : G =>
        (AddMonoidAlgebra.single h (1 : S) : AddMonoidAlgebra S G))) := by
      refine Submodule.span_mono ?_ (AddMonoidAlgebra.mem_span_support y)
      rintro _ ⟨h, -, rfl⟩
      exact ⟨h, rfl⟩
    have hnot := hli.notMem_span hy
    apply hnot
    refine Submodule.span_mono ?_ hspan
    rintro _ ⟨h, rfl⟩
    refine ⟨AddMonoidAlgebra.single h 1, ⟨hgl1 h, ?_⟩, rfl⟩
    intro heq
    exact hne h (Set.mem_singleton_iff.mp heq).symm
  choose M hM using fun g => key _ (hgl g)
  refine ⟨⟨⟨M, ?_⟩, ?_⟩, hM⟩
  ·
    have h1 : f (AddMonoidAlgebra.single 0 1) = AddMonoidAlgebra.single 0 1 := by
      rw [show (AddMonoidAlgebra.single (0 : G) (1 : S)) = 1 from rfl, map_one]
    have := (hM 0).symm.trans h1
    exact (AddMonoidAlgebra.single_left_injective one_ne_zero this)
  · intro g g'
    have hmul : f (AddMonoidAlgebra.single (g + g') 1) = f (AddMonoidAlgebra.single g 1) * f (AddMonoidAlgebra.single g' 1) := by
      rw [← map_mul, AddMonoidAlgebra.single_mul_single, mul_one]
    rw [hM, hM, hM, AddMonoidAlgebra.single_mul_single, mul_one] at hmul
    exact AddMonoidAlgebra.single_left_injective one_ne_zero hmul

end S_AddMonoidAlgebra_exists_addMonoidHom_forall_bialgHom_single_eq_single
end P2MW
export P2MW.S_AddMonoidAlgebra_exists_addMonoidHom_forall_bialgHom_single_eq_single (solution)
