-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TensTop
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TensTop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:09.581079+00:00
-- url     : https://prove2.me/theorems/ff4790e0-a6f0-45a5-a5bc-f506eda3f7a6
-- title:
--   Tens Top
-- statement:
--   Definitions and structural lemmas for Tens Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/TensTop.lean

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
namespace PI.VolStabS
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
theorem isClosed_HermR (σ : E →ₐ[F] E) (n : ℕ) :
    IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  let sL : R ⊗[F] E →ₗ[R] R ⊗[F] E :=
    { toFun := sigR R σ
      map_add' := map_add _
      map_smul' := fun r x => by
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        simp [sigR, Algebra.TensorProduct.algebraMap_apply] }
  have hs : Continuous (sigR R σ) := IsModuleTopology.continuous_of_linearMap sL
  have hset : (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      ⋂ a, ⋂ b, {S | sigR R σ (S b a) = S a b} := by
    ext S
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [hset]
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
  | tmul a e => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
theorem gramR_mem (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (X : Fin n → Fin M → R ⊗[F] E) : gramR R σ J X ∈ HermR R σ n := by
  intro a b
  have hJR : ∀ i j, sigR R σ (JR R J j i) = JR R J i j := fun i j => by
    simp [JR, inclR, sigR, hJ]
  simp only [gramR, hR, Formalism.UG.hform, map_sum, map_mul, sigR_invol R σ hσ, hJR]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
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
end PI.VolStabS


