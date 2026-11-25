-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_T2SpaceTensorProductFiniteExtension
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_T2SpaceTensorProductFiniteExtension
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T08:00:54.519289+00:00
-- url     : https://prove2.me/theorems/90d30b15-d2cf-428f-bcbf-1736938efbec
-- title:
--   T2 Space Tensor Product Finite Extension
-- statement:
--   Definitions and structural lemmas for T2 Space Tensor Product Finite Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/T2SpaceTensorProductFiniteExtension.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.AprimeInfT
open scoped TensorProduct
open NumberField MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
section Gen
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
instance isModuleTopology_tens : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
instance isTopologicalRing_tens : IsTopologicalRing (R ⊗[F] E) :=
  IsModuleTopology.isTopologicalRing R (R ⊗[F] E)
theorem exists_homeomorph_tens :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (R ⊗[F] E ≃ₜ (ι → R)) := by
  classical
  let b := Module.Free.chooseBasis R (R ⊗[F] E)
  let e : (R ⊗[F] E) ≃ₗ[R] (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) := b.equivFun
  refine ⟨Module.Free.ChooseBasisIndex R (R ⊗[F] E), inferInstance, ⟨?_⟩⟩
  exact
    { toEquiv := e.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
variable [LocallyCompactSpace R] [T2Space R]
instance locallyCompactSpace_tens : LocallyCompactSpace (R ⊗[F] E) := by
  obtain ⟨ι, _, ⟨h⟩⟩ := exists_homeomorph_tens (F := F) (E := E) R
  exact h.isClosedEmbedding.locallyCompactSpace
instance t2Space_tensorProduct_finiteExtension : T2Space (R ⊗[F] E) := by
  obtain ⟨ι, _, ⟨h⟩⟩ := exists_homeomorph_tens (F := F) (E := E) R
  exact h.isEmbedding.t2Space
theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  have h : ∀ x : R ⊗[F] E, sigR R σ x = (σ.toLinearMap.baseChange R) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have : (sigR R σ : R ⊗[F] E → R ⊗[F] E) = (σ.toLinearMap.baseChange R) := funext h
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap _
variable {M : ℕ}
instance locallyCompactSpace_mat : LocallyCompactSpace (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
  inferInstanceAs (LocallyCompactSpace (Fin M → Fin M → R ⊗[F] E))
instance t2Space_matrix_tensor : T2Space (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
  inferInstanceAs (T2Space (Fin M → Fin M → R ⊗[F] E))
theorem isClosed_HR (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    IsClosed (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))) := by
  have hset : (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))) =
      {g : GL (Fin M) (R ⊗[F] E) | Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
        (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J} := rfl
  rw [hset]
  have hv : Continuous (fun g : GL (Fin M) (R ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))) :=
    Units.continuous_val
  refine isClosed_eq ?_ continuous_const
  refine Continuous.matrix_mul (Continuous.matrix_mul ?_ continuous_const) hv
  unfold Formalism.UG.cT
  exact (hv.matrix_map (continuous_sigR R σ)).matrix_transpose
instance locallyCompactSpace_HR (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    LocallyCompactSpace (HR R σ J) :=
  (isClosed_HR R σ J).isClosedEmbedding_subtypeVal.locallyCompactSpace
instance isTopologicalGroup_HA (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    IsTopologicalGroup (HA R σ J) :=
  inferInstanceAs (IsTopologicalGroup (HR R σ J))
instance locallyCompactSpace_HA (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    LocallyCompactSpace (HA R σ J) :=
  inferInstanceAs (LocallyCompactSpace (HR R σ J))
instance t2Space_unitaryGroup (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) : T2Space (HA R σ J) :=
  inferInstanceAs (T2Space (HR R σ J))
instance borelSpace_HA (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    BorelSpace (HA R σ J) := ⟨rfl⟩
end Gen
section Inf
variable (F : Type) [Field F] [NumberField F]
instance t2Space_infiniteAdeleRing : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
instance secondCountable_completion (v : InfinitePlace F) : SecondCountableTopology v.Completion := by
  exact (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
instance secondCountable_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing F) :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))
example : LocallyCompactSpace (InfiniteAdeleRing F) := inferInstance
example : IsTopologicalRing (InfiniteAdeleRing F) := inferInstance
end Inf
end PI.AprimeInfT


