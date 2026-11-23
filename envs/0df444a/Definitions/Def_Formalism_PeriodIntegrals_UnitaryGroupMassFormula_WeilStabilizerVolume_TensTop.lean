-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:11.124815+00:00
-- url     : https://prove2.me/theorems/e0137946-d35d-4052-8c9b-608816b637e0
-- title:
--   Tens Top
-- statement:
--   Definitions and structural lemmas for Tens Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/TensTop.lean

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
namespace PI.VolStabW
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
  have hsig : Continuous (sigR R σ) := by
    have e : ⇑(sigR R σ) = ⇑(LinearMap.baseChange R σ.toLinearMap) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r e => simp [sigR]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [e]
    exact IsModuleTopology.continuous_of_linearMap _
  let b := Algebra.TensorProduct.basis R (Module.finBasis F E)
  haveI : T2Space (R ⊗[F] E) := T2Space.of_injective_continuous b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)
  show IsClosed {S : Matrix (Fin n) (Fin n) (R ⊗[F] E) | ∀ a b, sigR R σ (S b a) = S a b}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun c => isClosed_eq
    (hsig.comp ((continuous_apply a).comp (continuous_apply c)))
    ((continuous_apply c).comp (continuous_apply a))
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
  | add x y hx hy => simp only [map_add, hx, hy]
theorem gramR_mem (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (X : Fin n → Fin M → R ⊗[F] E) : gramR R σ J X ∈ HermR R σ n := by
  have hsi : ∀ e, sigR R σ (inclR R e) = inclR R (σ e) := fun e => by simp [sigR, inclR]
  show ∀ a b, sigR R σ (gramR R σ J X b a) = gramR R σ J X a b
  intro a b
  simp only [gramR, hR, Formalism.UG.hform, JR, Matrix.map_apply, map_sum, map_mul, sigR_invol R σ hσ, hsi, hJ]
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
end PI.VolStabW


