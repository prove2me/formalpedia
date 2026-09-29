-- Prove2me | solution 1 for AutomorphicForm.exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/9d264323-2d74-5722-bb08-02a2fe8a135f

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul

set_option autoImplicit false

open NumberField Topology
open scoped TensorProduct TensorProduct.RightActions

namespace S30PlacesL

variable (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]

open scoped Classical in

noncomputable def tensorPlaces :
    (L ⊗[K] InfiniteAdeleRing K) ≃+* ∀ v : InfinitePlace K, L ⊗[K] v.Completion :=
  (Algebra.TensorProduct.piRight K K L fun v : InfinitePlace K => v.Completion).toRingEquiv

theorem tensorPlaces_tmul (l : L) (x : InfiniteAdeleRing K) (v : InfinitePlace K) :
    tensorPlaces K L (l ⊗ₜ[K] x) v = l ⊗ₜ[K] x v :=
  rfl

omit [NumberField K] in
theorem secondCountableTopology_completion (v : InfinitePlace K) : SecondCountableTopology v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology

theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI := secondCountableTopology_completion K
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace K) → v.Completion))

variable [NumberField L]

theorem continuous_tensorPlaces : Continuous (tensorPlaces K L) := by
  haveI : ∀ v : InfinitePlace K, IsTopologicalRing (L ⊗[K] v.Completion) := fun v =>
    AutomorphicForm.isTopologicalRing_tensor K L v.Completion
  refine IsModuleTopology.continuous_of_ringHom (R := InfiniteAdeleRing K) (tensorPlaces K L).toRingHom ?_
  have h : ⇑((tensorPlaces K L).toRingHom.comp (algebraMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)))
      = fun x : InfiniteAdeleRing K => fun v : InfinitePlace K =>
          algebraMap v.Completion (L ⊗[K] v.Completion) (x v) :=
    rfl
  rw [h]
  exact continuous_pi fun v => (continuous_algebraMap v.Completion (L ⊗[K] v.Completion)).comp (continuous_apply v)

theorem secondCountableTopology_tensor : SecondCountableTopology (L ⊗[K] InfiniteAdeleRing K) := by
  haveI := secondCountableTopology_infiniteAdeleRing K
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  have hq : IsOpenQuotientMap f := IsModuleTopology.isOpenQuotientMap_of_surjective hf
  exact hq.isQuotientMap.secondCountableTopology hq.isOpenMap

theorem continuous_tensorPlaces_symm : Continuous (tensorPlaces K L).symm := by
  haveI : IsTopologicalRing (L ⊗[K] InfiniteAdeleRing K) :=
    AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  haveI : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K) :=
    AutomorphicForm.locallyCompactSpace_tensor K L (InfiniteAdeleRing K)
  haveI := secondCountableTopology_tensor K L
  haveI : SigmaCompactSpace (L ⊗[K] InfiniteAdeleRing K) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : ∀ v : InfinitePlace K, IsTopologicalRing (L ⊗[K] v.Completion) := fun v =>
    AutomorphicForm.isTopologicalRing_tensor K L v.Completion
  haveI : ∀ v : InfinitePlace K, T2Space (L ⊗[K] v.Completion) := fun v =>
    AutomorphicForm.t2Space_tensor K L v.Completion
  haveI : ∀ v : InfinitePlace K, LocallyCompactSpace (L ⊗[K] v.Completion) := fun v =>
    AutomorphicForm.locallyCompactSpace_tensor K L v.Completion
  haveI : T2Space (∀ v : InfinitePlace K, L ⊗[K] v.Completion) := Pi.t2Space
  haveI : R1Space (∀ v : InfinitePlace K, L ⊗[K] v.Completion) := T2Space.r1Space
  haveI : LocallyCompactSpace (∀ v : InfinitePlace K, L ⊗[K] v.Completion) := Pi.locallyCompactSpace_of_finite
  haveI : BaireSpace (∀ v : InfinitePlace K, L ⊗[K] v.Completion) := BaireSpace.of_t2Space_locallyCompactSpace
  have hopen : IsOpenMap (tensorPlaces K L) :=
    (tensorPlaces K L).toAddMonoidHom.isOpenMap_of_sigmaCompact (tensorPlaces K L).surjective
      (continuous_tensorPlaces K L)
  exact ((tensorPlaces K L).toEquiv.toHomeomorphOfContinuousOpen (continuous_tensorPlaces K L)
    hopen).symm.continuous

end S30PlacesL

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    ∃ Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((v : InfinitePlace K) → L ⊗[K] v.Completion),
      Continuous Ξ ∧ Continuous Ξ.symm ∧
      ∀ (x : L) (a : InfiniteAdeleRing K) (v : InfinitePlace K), Ξ (x ⊗ₜ a) v = x ⊗ₜ (a v) :=
  ⟨S30PlacesL.tensorPlaces K L, S30PlacesL.continuous_tensorPlaces K L, S30PlacesL.continuous_tensorPlaces_symm K L,
    fun x a v => S30PlacesL.tensorPlaces_tmul K L x a v⟩

end S_AutomorphicForm_exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul
end P2MW
export P2MW.S_AutomorphicForm_exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul (solution)
