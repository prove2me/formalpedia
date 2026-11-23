-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:03:28.092249+00:00
-- url     : https://prove2.me/theorems/1f2c704a-dedf-4374-aeec-04b7b26ac792
-- title:
--   T2 Space Tensor Product Finite Extension
-- statement:
--   Definitions and structural lemmas for T2 Space Tensor Product Finite Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicLocalCompactness/T2SpaceTensorProductFiniteExtension.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GaugeGap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.AdicCompletionValuation
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
section Gen
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
instance isModuleTopology_tens : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
instance isTopologicalRing_tens : IsTopologicalRing (R ⊗[F] E) :=
  IsModuleTopology.isTopologicalRing R (R ⊗[F] E)
theorem exists_homeomorph_tens :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (R ⊗[F] E ≃ₜ (ι → R)) := by
  let b := Module.finBasis F E
  let e : R ⊗[F] E ≃ₗ[R] (Fin (Module.finrank F E) → R) := (Algebra.TensorProduct.basis R b).equivFun
  exact ⟨Fin (Module.finrank F E), inferInstance, ⟨{ e.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }⟩⟩
variable [LocallyCompactSpace R] [T2Space R]
instance locallyCompactSpace_tens : LocallyCompactSpace (R ⊗[F] E) := by
  obtain ⟨ι, _, ⟨h⟩⟩ := exists_homeomorph_tens (F := F) (E := E) R
  exact h.isClosedEmbedding.locallyCompactSpace
instance t2Space_tensorProduct_finiteExtension : T2Space (R ⊗[F] E) := by
  obtain ⟨ι, _, ⟨h⟩⟩ := exists_homeomorph_tens (F := F) (E := E) R
  exact h.isEmbedding.t2Space
theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  have e : (sigR R σ : R ⊗[F] E → R ⊗[F] E) = (σ.toLinearMap.baseChange R : R ⊗[F] E → R ⊗[F] E) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r y => simp [sigR, LinearMap.baseChange_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [e]
  exact IsModuleTopology.continuous_of_linearMap _
variable {M : ℕ}
instance locallyCompactSpace_mat : LocallyCompactSpace (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
  inferInstanceAs (LocallyCompactSpace (Fin M → Fin M → R ⊗[F] E))
instance t2Space_matrix_tensor : T2Space (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
  inferInstanceAs (T2Space (Fin M → Fin M → R ⊗[F] E))
theorem isClosed_HR (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    IsClosed (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))) := by
  have hc : Continuous fun g : GL (Fin M) (R ⊗[F] E) =>
      Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
    unfold Formalism.UG.cT
    exact (((Units.continuous_val.matrix_map (continuous_sigR R σ)).matrix_transpose).matrix_mul
      continuous_const).matrix_mul Units.continuous_val
  exact isClosed_eq hc continuous_const
instance locallyCompactSpace_HR (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    LocallyCompactSpace (HR R σ J) :=
  (isClosed_HR R σ J).isClosedEmbedding_subtypeVal.locallyCompactSpace
instance isTopologicalGroup_HA (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    IsTopologicalGroup (HA R σ J) :=
  inferInstanceAs (IsTopologicalGroup (HR R σ J))
instance locallyCompactSpace_HA (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    LocallyCompactSpace (HA R σ J) :=
  inferInstanceAs (LocallyCompactSpace (HR R σ J))
instance borelSpace_HA (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) :
    BorelSpace (HA R σ J) := ⟨rfl⟩
end Gen
end PI.AdicCompletionValuation


