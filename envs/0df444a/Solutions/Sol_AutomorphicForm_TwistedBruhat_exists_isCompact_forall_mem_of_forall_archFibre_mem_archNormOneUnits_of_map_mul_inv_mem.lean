-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.exists_isCompact_forall_mem_of_forall_archFibre_mem_archNormOneUnits_of_map_mul_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f1aa4171-0d20-5459-b2c2-a24bf76b7acd

import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_M4aHerbrand_ArchSemilocal
import Theorems.Thm_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_mem_of_mem_archNormOneUnits_of_placeEquivAlg_congr_mul_inv_mem
import Theorems.Thm_NumberField_InfiniteAdeleRing_exists_continuousMulEquiv_units_pi_forall_apply_eq_archFibre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_mem_of_forall_archFibre_mem_archNormOneUnits_of_map_mul_inv_mem

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : InfiniteAdeleRing L ≃+* InfiniteAdeleRing L)
    (hA : ∀ (v : InfinitePlace K) (t : (InfiniteAdeleRing L)ˣ),
      ((AutomorphicForm.TransversalMeasure.archFibre K L v (Units.map A.toRingHom.toMonoidHom t) :
          ((w : v.Extension L) → w.1.Completion)ˣ) : (w : v.Extension L) → w.1.Completion) =
        M4aHerbrand.ArchSemilocal.placeEquivAlg (K := K) (L := L) v
          ((Algebra.TensorProduct.congr (AlgEquiv.refl : v.Completion ≃ₐ[v.Completion] v.Completion) σ)
            ((M4aHerbrand.ArchSemilocal.placeEquivAlg (K := K) (L := L) v).symm
              ((AutomorphicForm.TransversalMeasure.archFibre K L v t : ((w : v.Extension L) → w.1.Completion)ˣ) :
                (w : v.Extension L) → w.1.Completion))))
    (C : Set (InfiniteAdeleRing L)ˣ) (hC : IsCompact C) :
    ∃ Ct : Set (InfiniteAdeleRing L)ˣ, IsCompact Ct ∧
      ∀ t : (InfiniteAdeleRing L)ˣ,
        (∀ v : InfinitePlace K, AutomorphicForm.TransversalMeasure.archFibre K L v t ∈
            AutomorphicForm.TransversalMeasure.archNormOneUnits K L v) →
        Units.map A.toRingHom.toMonoidHom t * t⁻¹ ∈ C → t ∈ Ct := by
  classical
  obtain ⟨E, hE⟩ := NumberField.InfiniteAdeleRing.exists_continuousMulEquiv_units_pi_forall_apply_eq_archFibre K L

  have hcont : ∀ v : InfinitePlace K, Continuous (AutomorphicForm.TransversalMeasure.archFibre K L v) := by
    intro v
    have : (AutomorphicForm.TransversalMeasure.archFibre K L v : (InfiniteAdeleRing L)ˣ → _) = fun y => E y v :=
      funext fun y => (hE y v).symm
    rw [this]
    exact (continuous_apply v).comp (map_continuous E)

  have hloc := fun v : InfinitePlace K =>
    AutomorphicForm.TwistedBruhat.exists_isCompact_forall_mem_of_mem_archNormOneUnits_of_placeEquivAlg_congr_mul_inv_mem
      K L σ hgen v (AutomorphicForm.TransversalMeasure.archFibre K L v '' C) (hC.image (hcont v))
  choose B hB hspec using hloc
  refine ⟨E.symm '' Set.pi Set.univ B, (isCompact_univ_pi hB).image (map_continuous E.symm), fun t ht hC' => ?_⟩
  refine ⟨E t, fun v _ => ?_, ContinuousMulEquiv.symm_apply_apply E t⟩
  rw [hE t v]
  apply hspec v _ (ht v)
  rw [← hA v t]
  refine ⟨AutomorphicForm.TransversalMeasure.archFibre K L v (Units.map A.toRingHom.toMonoidHom t * t⁻¹),
    ⟨_, hC', rfl⟩, ?_⟩
  rw [map_mul, map_inv, Units.val_mul]

end S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_mem_of_forall_archFibre_mem_archNormOneUnits_of_map_mul_inv_mem
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_mem_of_forall_archFibre_mem_archNormOneUnits_of_map_mul_inv_mem (solution)
