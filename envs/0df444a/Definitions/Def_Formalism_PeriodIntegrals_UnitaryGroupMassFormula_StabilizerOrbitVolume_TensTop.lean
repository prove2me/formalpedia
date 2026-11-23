-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:07:00.889585+00:00
-- url     : https://prove2.me/theorems/d5b40881-ad08-411f-ace1-e948cdd7f553
-- title:
--   Tens Top
-- statement:
--   Definitions and structural lemmas for Tens Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/TensTop.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabSW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
section Gen
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
instance secondCountable_tens [SecondCountableTopology R] :
    SecondCountableTopology (R ⊗[F] E) := by
  obtain ⟨ι, _, ⟨h⟩⟩ := exists_homeomorph_tens (F := F) (E := E) R
  exact h.isInducing.secondCountableTopology
instance borelSpace_tens : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
instance borelSpace_herm (σ : E →ₐ[F] E) (n : ℕ) : BorelSpace (HermR R σ n) := ⟨rfl⟩
def hLin (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin M → R ⊗[F] E) :
    (Fin M → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun := hR R σ J x
  map_add' y z := by
    simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
variable [LocallyCompactSpace R] [T2Space R]
theorem continuous_sigR_stabilizer_orbit_volume (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have e : ⇑(sigR R σ) = ⇑(LinearMap.baseChange R σ.toLinearMap) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [sigR, LinearMap.baseChange_tmul]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  rw [e]
  exact IsModuleTopology.continuous_of_linearMap _
theorem isClosed_HermR (σ : E →ₐ[F] E) (n : ℕ) :
    IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : T2Space (R ⊗[F] E) :=
    T2Space.of_injective_continuous (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun.injective
      (IsModuleTopology.continuous_of_linearMap
        (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun.toLinearMap)
  have hs := continuous_sigR_stabilizer_orbit_volume (F := F) (E := E) R σ
  have e : (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      ⋂ a, ⋂ b, {S | sigR R σ (S b a) = S a b} := by
    ext S
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [e]
  exact isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_eq (hs.comp ((continuous_apply a).comp (continuous_apply b)))
      ((continuous_apply b).comp (continuous_apply a))
instance locallyCompact_herm (σ : E →ₐ[F] E) (n : ℕ) : LocallyCompactSpace (HermR R σ n) :=
  (isClosed_HermR R σ n).isClosedEmbedding_subtypeVal.locallyCompactSpace
end Gen
section CM
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
theorem sigR_invol (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) :
    sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hσ]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
theorem gramR_mem (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (X : Fin n → Fin M → R ⊗[F] E) : gramR R σ J X ∈ HermR R σ n := by
  have hJR : ∀ p q, sigR R σ (JR R J q p) = JR R J p q := fun p q => by
    simp [JR, inclR, sigR, hJ]
  show ∀ a b, sigR R σ (gramR R σ J X b a) = gramR R σ J X a b
  intro a b
  simp only [gramR, hR, Formalism.UG.hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [sigR_invol R σ hσ, hJR]
  ring
end CM
section Arch
variable (F : Type) [Field F] [NumberField F]
instance secondCountable_completion (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding (v := v)).isEmbedding.isInducing.secondCountableTopology
instance secondCountable_Ainf : SecondCountableTopology (InfiniteAdeleRing F) :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))
end Arch
section Glue
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
def gramH (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → R ⊗[F] E) : HermR R σ n :=
  ⟨gramR R σ J X, gramR_mem R σ hσ J hJ X⟩
end Glue
section GlueTop
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]
end GlueTop
end PI.VolStabSW


