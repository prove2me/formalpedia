-- Prove2me | solution 1 for AutomorphicForm.exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a7dd776f-1b6b-5d65-98ed-aa4dc39f6c4e

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_exists_isArchTestFactor_forall_isNormConjugator_one_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom
import Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom

set_option autoImplicit false

open NumberField MeasureTheory
open scoped TensorProduct TensorProduct.RightActions
open AutomorphicForm

section Generic

variable {G : Type*} [Group G]

private theorem prod_range_iterate_conj (f : G →* G) (x δ : G) (n : ℕ) :
    ((List.range n).map fun i => (⇑f)^[i] (x⁻¹ * δ * f x)).prod =
      x⁻¹ * ((List.range n).map fun i => (⇑f)^[i] δ).prod * (⇑f)^[n] x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ]
    simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    rw [ih]
    simp only [iterate_map_mul, iterate_map_inv, Function.iterate_succ_apply, mul_assoc, mul_inv_cancel_left]

end Generic

section Twisted

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

private theorem sigmaTensor_mul_apply (σ σ' : L ≃ₐ[K] L) (z : L ⊗[K] A) :
    sigmaTensor K L A (σ * σ') z = sigmaTensor K L A σ (sigmaTensor K L A σ' z) := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro l a
    simp [sigmaTensor, Algebra.TensorProduct.map_tmul, AlgEquiv.mul_apply]
  · intro x y hx hy
    simp only [map_add, hx, hy]

private theorem sigmaTensor_one_apply (z : L ⊗[K] A) : sigmaTensor K L A 1 z = z := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro l a
    simp [sigmaTensor, Algebra.TensorProduct.map_tmul, AlgEquiv.one_apply]
  · intro x y hx hy
    simp only [map_add, hx, hy]

private theorem sigmaGL_mul_apply (σ σ' : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] A)) :
    sigmaGL K L A (σ * σ') g = sigmaGL K L A σ (sigmaGL K L A σ' g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show Matrix.GeneralLinearGroup.map (sigmaTensor K L A (σ * σ')) g i j =
    Matrix.GeneralLinearGroup.map (sigmaTensor K L A σ)
      (Matrix.GeneralLinearGroup.map (sigmaTensor K L A σ') g) i j
  simp only [Matrix.GeneralLinearGroup.map_apply, sigmaTensor_mul_apply]

private theorem sigmaGL_one_apply (g : GL (Fin 2) (L ⊗[K] A)) : sigmaGL K L A 1 g = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show Matrix.GeneralLinearGroup.map (sigmaTensor K L A 1) g i j = g i j
  simp only [Matrix.GeneralLinearGroup.map_apply, sigmaTensor_one_apply]

private theorem sigmaGL_iterate (σ : L ≃ₐ[K] L) (n : ℕ) (g : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[n] g = sigmaGL K L A (σ ^ n) g := by
  induction n with
  | zero => simp [sigmaGL_one_apply]
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', sigmaGL_mul_apply]

private theorem pow_finrank_eq_one [FiniteDimensional K L] (σ : L ≃ₐ[K] L) : σ ^ Module.finrank K L = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← Nat.card_zpowers, ← IntermediateField.finrank_fixedField_eq_card]
  exact Dvd.intro_left _
    (Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L)

private theorem pow_finrank_eq_one' (σ : L ≃ₐ[K] L) : σ ^ Module.finrank K L = 1 := by
  by_cases h : FiniteDimensional K L
  · exact pow_finrank_eq_one K L σ
  · rw [Module.finrank_of_infinite_dimensional h, pow_zero]

private theorem sigmaGL_iterate_finrank' (σ : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[Module.finrank K L] g = g := by
  rw [sigmaGL_iterate, pow_finrank_eq_one', sigmaGL_one_apply]

end Twisted

section NormRepresentative

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

private theorem isNormConjugator_one_of_isNormConjugator (σ : L ≃ₐ[K] L) (γ : GL (Fin 2) A)
    (δ y : GL (Fin 2) (L ⊗[K] A))
    (hy : IsNormConjugator K L A σ γ δ y) :
    IsNormConjugator K L A σ γ (y⁻¹ * δ * sigmaGL K L A σ y) 1 := by
  unfold IsNormConjugator at hy ⊢
  unfold normString at hy ⊢
  rw [inv_one, one_mul, mul_one, prod_range_iterate_conj, sigmaGL_iterate_finrank']
  exact hy

end NormRepresentative

section HaarFact

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

private theorem isHaarMeasure_archHaarL :
    @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] InfiniteAdeleRing K)) (archHaarL K L) := by
  letI := glBorelOf (L ⊗[K] InfiniteAdeleRing K)
  haveI := borelSpace_glBorelOf (L ⊗[K] InfiniteAdeleRing K)
  haveI := isTopologicalGroup_tensorGL K L (InfiniteAdeleRing K)
  haveI := locallyCompactSpace_tensorGL K L (InfiniteAdeleRing K)
  unfold archHaarL
  infer_instance

end HaarFact

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hι : IsEmpty (L →ₐ[K] InfiniteAdeleRing K)) (tysL : ArchTypeFamily L)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : IsArchTestFactor L φa)
    (hφt : IsArchFactorBiFinite L tysL φa) :
    ∃ (tysK : ArchTypeFamily K) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ),
      IsArchTestFactor K fa ∧ IsArchFactorBiFinite K tysK fa ∧
      (∀ δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
        IsRegularSemisimple (normString K L (InfiniteAdeleRing K) σ δ) →
        ∀ γ : GL (Fin 2) (InfiniteAdeleRing K), IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K), IsNormConjugator K L (InfiniteAdeleRing K) σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
            (centralizerBorel (InfiniteAdeleRing K) γ))
          (τ' : @Measure (twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
            (twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfiniteAdeleRing K) γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ' →
          Coupled K L (InfiniteAdeleRing K) σ γ δ y τ τ' →
          ∃ I : ℂ,
            IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (archHaarL K L) δ τ' (φa ∘ archIdentGL K L) I ∧
              IsOrbitalIntegralOn (InfiniteAdeleRing K) (archHaarK K) γ τ fa I) ∧
      (∀ γ : GL (Fin 2) (InfiniteAdeleRing K), IsRegularSemisimple γ →
        (¬ ∃ δ, IsNormOf K L (InfiniteAdeleRing K) σ γ δ) →
        ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
            (centralizerBorel (InfiniteAdeleRing K) γ),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfiniteAdeleRing K) γ) τ →
          IsOrbitalIntegralOn (InfiniteAdeleRing K) (archHaarK K) γ τ fa 0) := by
  have hμ : ∀ g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      @Measure.map _ _ (glBorelOf (L ⊗[K] InfiniteAdeleRing K)) (glBorelOf (L ⊗[K] InfiniteAdeleRing K))
        (fun z => g * z) (archHaarL K L) = archHaarL K L := by
    intro g
    letI := glBorelOf (L ⊗[K] InfiniteAdeleRing K)
    haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by rw [hdeg]; exact two_pos)
    haveI := isHaarMeasure_archHaarL K L
    exact Measure.IsMulLeftInvariant.map_mul_left_eq_self (μ := archHaarL K L) g
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by rw [hdeg]; exact two_pos)
  obtain ⟨tysK, fa, hfa, hfat, H1, H2⟩ :=
    exists_isArchTestFactor_forall_isNormConjugator_one_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom
      K L hdeg σ hσ hι tysL φa hφa hφt
  refine ⟨tysK, fa, hfa, hfat, ?_, H2⟩
  intro δ _hNreg γ hγ y hy τ τ' hτ hτ' hC
  have hN1 := isNormConjugator_one_of_isNormConjugator K L (InfiniteAdeleRing K) σ γ δ y hy
  obtain ⟨τ₁, hτ₁, hC1, hback⟩ :=
    exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate K L (InfiniteAdeleRing K) σ (archHaarL K L) hμ
      γ δ y τ τ' hτ' hC
  obtain ⟨I, hTw, hOrb⟩ := H1 γ hγ _ hN1 τ τ₁ hτ hτ₁ hC1
  exact ⟨I, hback _ I hTw, hOrb⟩

end S_AutomorphicForm_exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom
end P2MW
export P2MW.S_AutomorphicForm_exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom (solution)
