-- Prove2me | solution 1 for AutomorphicForm.exists_isCompact_forall_mem_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/197e2239-17ce-5520-8c84-027e677153b1

import Mathlib
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isCompact_forall_mem_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

namespace S6a

open AutomorphicForm

section sigma

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

theorem sigmaTensor_mul_apply (σ τ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    sigmaTensor K L A (σ * τ) x = sigmaTensor K L A σ (sigmaTensor K L A τ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    change Algebra.TensorProduct.map (σ * τ).toAlgHom (AlgHom.id K A) (l ⊗ₜ a) =
      Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) (Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id K A) (l ⊗ₜ a))
    simp only [Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sigmaTensor_one_apply (x : L ⊗[K] A) : sigmaTensor K L A 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    change Algebra.TensorProduct.map (1 : L ≃ₐ[K] L).toAlgHom (AlgHom.id K A) (l ⊗ₜ a) = l ⊗ₜ a
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => rw [map_add, hx, hy]

theorem sigmaTensor_iterate (σ : L ≃ₐ[K] L) (n : ℕ) (x : L ⊗[K] A) :
    (⇑(sigmaTensor K L A σ))^[n] x = sigmaTensor K L A (σ ^ n) x := by
  induction n with
  | zero => rw [Function.iterate_zero_apply, pow_zero, sigmaTensor_one_apply]
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', sigmaTensor_mul_apply]

theorem sigmaGL_iterate_apply (σ : L ≃ₐ[K] L) (n : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    (((⇑(sigmaGL K L A σ))^[n] x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (⇑(sigmaTensor K L A σ))^[n] ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

theorem pow_finrank_eq_one [FiniteDimensional K L] (σ : L ≃ₐ[K] L) : σ ^ Module.finrank K L = 1 := by
  apply orderOf_dvd_iff_pow_eq_one.mp
  have h1 : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers σ)) L = Nat.card (Subgroup.zpowers σ) :=
    IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)
  rw [Nat.card_zpowers] at h1
  rw [← h1]
  exact Dvd.intro_left _ (Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L)

theorem sigmaGL_iterate_finrank [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (x : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[Module.finrank K L] x = x := by
  apply Units.ext
  ext i j
  rw [sigmaGL_iterate_apply, sigmaTensor_iterate, pow_finrank_eq_one, sigmaTensor_one_apply]

def P (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) (n : ℕ) : GL (Fin 2) (L ⊗[K] A) :=
  ((List.range n).map fun i => (⇑(sigmaGL K L A σ))^[i] δ).prod

theorem P_succ (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) (n : ℕ) :
    P K L A σ δ (n + 1) = P K L A σ δ n * (⇑(sigmaGL K L A σ))^[n] δ := by
  simp only [P, List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]

theorem normString_eq_P (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ δ = P K L A σ δ (Module.finrank K L) := rfl

theorem iterate_sigmaGL_mul (σ : L ≃ₐ[K] L) (n : ℕ) (x y : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[n] (x * y) = (⇑(sigmaGL K L A σ))^[n] x * (⇑(sigmaGL K L A σ))^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_mul]

theorem iterate_sigmaGL_inv (σ : L ≃ₐ[K] L) (n : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(sigmaGL K L A σ))^[n] x⁻¹ = ((⇑(sigmaGL K L A σ))^[n] x)⁻¹ := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_inv]

theorem P_conj (σ : L ≃ₐ[K] L) (x δ : GL (Fin 2) (L ⊗[K] A)) (n : ℕ) :
    P K L A σ (x⁻¹ * δ * sigmaGL K L A σ x) n = x⁻¹ * P K L A σ δ n * (⇑(sigmaGL K L A σ))^[n] x := by
  induction n with
  | zero => simp [P]
  | succ n ih =>
    rw [P_succ, P_succ, ih, iterate_sigmaGL_mul, iterate_sigmaGL_mul, iterate_sigmaGL_inv,
      ← Function.iterate_succ_apply (⇑(sigmaGL K L A σ)) n x]
    group

theorem normString_conj [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (x δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ (x⁻¹ * δ * sigmaGL K L A σ x) = x⁻¹ * normString K L A σ δ * x := by
  rw [normString_eq_P, P_conj, sigmaGL_iterate_finrank, ← normString_eq_P]

theorem continuous_P [TopologicalSpace A] [IsTopologicalRing A] [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (n : ℕ) :
    Continuous fun δ : GL (Fin 2) (L ⊗[K] A) => P K L A σ δ n := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  have hσ : Continuous (sigmaGL K L A σ) := by
    refine Continuous.units_map _ ?_
    refine continuous_id.matrix_map ?_
    have h := IsModuleTopology.continuous_of_linearMap
      (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap
    exact h
  have hit : ∀ k : ℕ, Continuous fun δ : GL (Fin 2) (L ⊗[K] A) => (⇑(sigmaGL K L A σ))^[k] δ := by
    intro k
    induction k with
    | zero => exact continuous_id
    | succ k ih => simp only [Function.iterate_succ_apply']; exact hσ.comp ih
  induction n with
  | zero => simp only [P, List.range_zero, List.map_nil, List.prod_nil]; exact continuous_const
  | succ n ih => simp only [P_succ]; exact ih.mul (hit n)

end sigma

theorem isCompact_sq_preimage {F : Type*} [NormedField F] [ProperSpace F] (C : Set F) (hC : IsCompact C) :
    IsCompact {x : F | x ^ 2 ∈ C} := by
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall 0
  have hcl : IsClosed {x : F | x ^ 2 ∈ C} := hC.isClosed.preimage (continuous_pow 2)
  refine (isCompact_closedBall (0 : F) (Real.sqrt R)).of_isClosed_subset hcl fun x hx => ?_
  have h := hR hx
  rw [mem_closedBall_zero_iff, norm_pow] at h
  rw [mem_closedBall_zero_iff]
  have h2 := Real.abs_le_sqrt h
  rwa [abs_of_nonneg (norm_nonneg x)] at h2

theorem val_mul_apply {R : Type*} [CommRing R] (x y : GL (Fin 2) R) (i j : Fin 2) :
    ((x * y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j =
      (x : Matrix (Fin 2) (Fin 2) R) i 0 * (y : Matrix (Fin 2) (Fin 2) R) 0 j +
        (x : Matrix (Fin 2) (Fin 2) R) i 1 * (y : Matrix (Fin 2) (Fin 2) R) 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_scalar_mul_diagUnits2 {R : Type*} [CommRing R] (b a : Rˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1 : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det =
      (b : R) ^ 2 * a := by
  have h : ((Matrix.GeneralLinearGroup.scalar (Fin 2) b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      Matrix.scalar (Fin 2) (b : R) := rfl
  rw [Units.val_mul, Matrix.det_mul, h, Matrix.scalar_apply, Matrix.det_diagonal, LanglandsTunnell.CubicInduction.coe_diagUnits2,
    Matrix.det_fin_two]
  simp [Fin.prod_univ_two]

theorem det_inv_scalar_mul_diagUnits2 {R : Type*} [CommRing R] (b a : Rˣ) :
    (((Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det =
      ((b⁻¹ : Rˣ) : R) ^ 2 * ((a⁻¹ : Rˣ) : R) := by
  have hinv : (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1 : GL (Fin 2) R)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) b⁻¹ * diagUnits2 a⁻¹ 1 := by
    rw [mul_inv_rev, map_inv]
    have hd : (diagUnits2 a 1 : GL (Fin 2) R)⁻¹ = diagUnits2 a⁻¹ 1 := by
      rw [inv_eq_iff_mul_eq_one]
      apply Units.ext
      rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, LanglandsTunnell.CubicInduction.coe_diagUnits2,
        Units.val_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hd]

    apply Units.ext
    have h : ((Matrix.GeneralLinearGroup.scalar (Fin 2) b⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
        Matrix.scalar (Fin 2) ((b⁻¹ : Rˣ) : R) := rfl
    simp only [Units.val_mul, h]
    exact ((Matrix.scalar_commute ((b⁻¹ : Rˣ) : R) (fun r' => mul_comm _ _) _).eq).symm
  rw [hinv, det_scalar_mul_diagUnits2]

theorem det_toTensorGL (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (γ : GL (Fin 2) A) :
    ((toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom ((γ : Matrix (Fin 2) (Fin 2) A).det) := by
  rw [RingHom.map_det]
  rfl

theorem det_val_conj {R : Type*} [CommRing R] (x g : GL (Fin 2) R) :
    ((x⁻¹ * g * x : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det = (g : Matrix (Fin 2) (Fin 2) R).det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]

end S6a

open S6a AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ)
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : AutomorphicForm.IsSemiLocalTestFn K L v φv) :
    ∃ C : Set (v.adicCompletion K)ˣ, IsCompact C ∧
      ∀ (b : (v.adicCompletion K)ˣ) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
        AutomorphicForm.normString K L (v.adicCompletion K) σ δ =
          AutomorphicForm.toTensorGL K L (v.adicCompletion K)
            (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1) →
        ∀ (τ' : Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)) (J : ℂ),
          AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ δ τ' φv J → J ≠ 0 → b ∈ C := by
  classical
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  set ℓ : ℕ := Module.finrank K L with hℓ
  have hℓ0 : (ℓ : v.adicCompletion K) ≠ 0 := Nat.cast_ne_zero.mpr (Module.finrank_pos).ne'

  set tr := Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) with htr
  have htrc : Continuous tr := by rw [htr]; exact IsModuleTopology.continuous_of_linearMap _
  set h₁ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → v.adicCompletion K := fun y =>
    tr (((normString K L (v.adicCompletion K) σ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det) with hh₁
  set h₂ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → v.adicCompletion K := fun y =>
    tr ((((normString K L (v.adicCompletion K) σ y)⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det) with hh₂
  have hNc : Continuous (normString K L (v.adicCompletion K) σ) := by
    have := continuous_P K L (v.adicCompletion K) σ (Module.finrank K L)
    exact this
  have hh₁c : Continuous h₁ := htrc.comp ((Units.continuous_val.comp hNc).matrix_det)
  have hh₂c : Continuous h₂ := htrc.comp ((Units.continuous_coe_inv.comp hNc).matrix_det)
  have hS : IsCompact (tsupport φv) := hφv.2
  set C₁ := h₁ '' tsupport φv with hC₁
  set C₂ := h₂ '' tsupport φv with hC₂
  have hC₁c : IsCompact C₁ := hS.image hh₁c
  have hC₂c : IsCompact C₂ := hS.image hh₂c

  set A₁ : Set (v.adicCompletion K) := {x | (ℓ : v.adicCompletion K) * (x ^ 2 * (a : v.adicCompletion K)) ∈ C₁} with hA₁
  set A₂ : Set (v.adicCompletion K) :=
    {w | (ℓ : v.adicCompletion K) * (w ^ 2 * ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ∈ C₂} with hA₂
  have hA₁c : IsCompact A₁ := by
    have hcont : Continuous fun x : v.adicCompletion K => (ℓ : v.adicCompletion K) * (x * (a : v.adicCompletion K)) :=
      continuous_const.mul (continuous_id.mul continuous_const)
    have heq : A₁ = {x | x ^ 2 ∈ (fun x => (ℓ : v.adicCompletion K) * (x * (a : v.adicCompletion K))) ⁻¹' C₁} := rfl
    rw [heq]
    refine isCompact_sq_preimage _ ?_

    have hu : IsUnit ((ℓ : v.adicCompletion K) * (a : v.adicCompletion K)) :=
      (isUnit_iff_ne_zero.mpr hℓ0).mul (Units.isUnit a)
    have : (fun x => (ℓ : v.adicCompletion K) * (x * (a : v.adicCompletion K))) ⁻¹' C₁ =
        (fun s => s * ((ℓ : v.adicCompletion K) * (a : v.adicCompletion K))⁻¹) '' C₁ := by
      ext x
      constructor
      · intro hx
        refine ⟨_, hx, ?_⟩
        field_simp
      · rintro ⟨s, hs, rfl⟩
        show (ℓ : v.adicCompletion K) * (s * ((ℓ : v.adicCompletion K) * (a : v.adicCompletion K))⁻¹ * (a : v.adicCompletion K)) ∈ C₁
        have : (ℓ : v.adicCompletion K) * (s * ((ℓ : v.adicCompletion K) * (a : v.adicCompletion K))⁻¹ * (a : v.adicCompletion K)) = s := by
          field_simp
        rw [this]; exact hs
    rw [this]
    exact hC₁c.image (continuous_id.mul continuous_const)
  have hA₂c : IsCompact A₂ := by
    have heq : A₂ = {x | x ^ 2 ∈ (fun x => (ℓ : v.adicCompletion K) * (x * ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K))) ⁻¹' C₂} := rfl
    rw [heq]
    refine isCompact_sq_preimage _ ?_
    have ha' : ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 0 := Units.ne_zero _
    have : (fun x => (ℓ : v.adicCompletion K) * (x * ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K))) ⁻¹' C₂ =
        (fun s => s * ((ℓ : v.adicCompletion K) * ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K))⁻¹) '' C₂ := by
      ext x
      constructor
      · intro hx
        refine ⟨_, hx, ?_⟩
        field_simp
      · rintro ⟨s, hs, rfl⟩
        show (ℓ : v.adicCompletion K) * (s * ((ℓ : v.adicCompletion K) * ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K))⁻¹ *
          ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ∈ C₂
        have : (ℓ : v.adicCompletion K) * (s * ((ℓ : v.adicCompletion K) * ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K))⁻¹ *
            ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)) = s := by
          field_simp
        rw [this]; exact hs
    rw [this]
    exact hC₂c.image (continuous_id.mul continuous_const)
  set C : Set (v.adicCompletion K)ˣ :=
    Units.embedProduct (v.adicCompletion K) ⁻¹' (A₁ ×ˢ (MulOpposite.op '' A₂)) with hC
  have hCc : IsCompact C := by
    refine Units.isClosedEmbedding_embedProduct.isCompact_preimage ?_
    exact hA₁c.prod (hA₂c.image MulOpposite.continuous_op)
  refine ⟨C, hCc, ?_⟩
  intro b δ hN τ' J hJ hJ0

  obtain ⟨s, hs, hJeq⟩ := hJ
  have hex : ∃ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      φv (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hJ0
    rw [hJeq]
    simp only [hall, zero_mul, integral_zero]
  obtain ⟨x, hx⟩ := hex
  set y := x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x with hy
  have hyS : y ∈ tsupport φv := subset_tsupport _ hx
  have hNy : normString K L (v.adicCompletion K) σ y =
      x⁻¹ * toTensorGL K L (v.adicCompletion K) (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1) * x := by
    rw [hy, normString_conj, hN]

  have hfr : Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) = ℓ := TensorProduct.finrank_rightAlgebra L
  have e₁ : h₁ y = (ℓ : v.adicCompletion K) * ((b : v.adicCompletion K) ^ 2 * (a : v.adicCompletion K)) := by
    simp only [hh₁]
    rw [hNy, det_val_conj, det_toTensorGL, det_scalar_mul_diagUnits2]
    show tr (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _) = _
    rw [htr, Algebra.trace_algebraMap, hfr, nsmul_eq_mul]
  have e₂ : h₂ y = (ℓ : v.adicCompletion K) * (((b⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ^ 2 *
      ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)) := by
    simp only [hh₂]
    have hinv : (normString K L (v.adicCompletion K) σ y)⁻¹ =
        x⁻¹ * (toTensorGL K L (v.adicCompletion K) (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1))⁻¹ * x := by
      rw [hNy]; group
    rw [hinv, det_val_conj, ← map_inv, det_toTensorGL, det_inv_scalar_mul_diagUnits2]
    show tr (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _) = _
    rw [htr, Algebra.trace_algebraMap, hfr, nsmul_eq_mul]

  show Units.embedProduct (v.adicCompletion K) b ∈ A₁ ×ˢ (MulOpposite.op '' A₂)
  refine ⟨?_, ?_⟩
  · show (ℓ : v.adicCompletion K) * ((b : v.adicCompletion K) ^ 2 * (a : v.adicCompletion K)) ∈ C₁
    rw [← e₁]; exact ⟨y, hyS, rfl⟩
  · refine ⟨((b⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K), ?_, rfl⟩
    show (ℓ : v.adicCompletion K) * (((b⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ^ 2 *
      ((a⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ∈ C₂
    rw [← e₂]; exact ⟨y, hyS, rfl⟩

end S_AutomorphicForm_exists_isCompact_forall_mem_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
end P2MW
export P2MW.S_AutomorphicForm_exists_isCompact_forall_mem_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2 (solution)
