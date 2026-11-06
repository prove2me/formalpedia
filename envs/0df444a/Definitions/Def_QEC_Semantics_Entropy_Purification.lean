-- Prove2me | Definitions.Def_QEC_Semantics_Entropy_Purification
-- name    : QEC_Semantics_Entropy_Purification
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:28:47.010757+00:00
-- url     : https://prove2.me/theorems/b2e91e78-a298-4980-ab46-69a3f5c516d7
-- title:
--   Purification
-- statement:
--   Definitions and structural lemmas for Purification, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Theorems.Thm_QEC_Semantics_DensityOperator_spectralEigenvalues_nonnegative
import Theorems.Thm_QEC_Semantics_DensityOperator_spectralEigenvalues_sum_eq_one
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
universe u
namespace QEC
namespace Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
namespace DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
noncomputable def spectralEigenbasis (rho : DensityOperator H) :
    OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H :=
  rho.positive.isSymmetric.eigenvectorBasis rfl
noncomputable def spectralPurificationVector (rho : DensityOperator H) : CompositeSystem H H :=
  ∑ i : Fin (Module.finrank Complex H),
    (Real.sqrt (rho.spectralEigenvalues i) : Complex) •
      (rho.spectralEigenbasis i ⊗ₜ[Complex] rho.spectralEigenbasis i)
theorem spectralPurificationVector_normSq (rho : DensityOperator H) :
    ‖rho.spectralPurificationVector‖ ^ 2 = 1 := by
  have hpair (i j : Fin (Module.finrank Complex H)) :
      inner Complex
          ((Real.sqrt (rho.spectralEigenvalues i) : Complex) •
            (rho.spectralEigenbasis i ⊗ₜ[Complex] rho.spectralEigenbasis i))
          ((Real.sqrt (rho.spectralEigenvalues j) : Complex) •
            (rho.spectralEigenbasis j ⊗ₜ[Complex] rho.spectralEigenbasis j)) =
        if i = j then (rho.spectralEigenvalues i : Complex) else 0 := by
    change inner Complex
        (((Real.sqrt (rho.spectralEigenvalues i) : Complex) • rho.spectralEigenbasis i) ⊗ₜ[Complex]
          rho.spectralEigenbasis i)
        (((Real.sqrt (rho.spectralEigenvalues j) : Complex) • rho.spectralEigenbasis j) ⊗ₜ[Complex]
          rho.spectralEigenbasis j) = _
    rw [TensorProduct.inner_tmul]
    rw [inner_smul_left, inner_smul_right]
    simp only [rho.spectralEigenbasis.inner_eq_ite]
    split_ifs with hij
    · subst j
      simp only [Complex.conj_ofReal, mul_one]
      exact_mod_cast (show Real.sqrt (rho.spectralEigenvalues i) *
          Real.sqrt (rho.spectralEigenvalues i) = rho.spectralEigenvalues i by
        simpa [pow_two] using Real.sq_sqrt (rho.spectralEigenvalues_nonnegative i))
    · simp
  have hinner :
      inner Complex rho.spectralPurificationVector rho.spectralPurificationVector =
        ∑ i, (rho.spectralEigenvalues i : Complex) := by
    unfold spectralPurificationVector
    rw [sum_inner]
    simp_rw [inner_sum]
    simp_rw [hpair]
    simp
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex), hinner, map_sum]
  simpa using rho.spectralEigenvalues_sum_eq_one
theorem spectralDecomposition (rho : DensityOperator H) :
    rho.toOperator = ∑ i : Fin (Module.finrank Complex H),
      (InnerProductSpace.rankOne Complex
        ((Real.sqrt (rho.spectralEigenvalues i) : Complex) • rho.spectralEigenbasis i)
        ((Real.sqrt (rho.spectralEigenvalues i) : Complex) • rho.spectralEigenbasis i)).toLinearMap := by
  ext x
  rw [LinearMap.sum_apply]
  change rho.toOperator x = ∑ i,
    inner Complex ((Real.sqrt (rho.spectralEigenvalues i) : Complex) •
      rho.spectralEigenbasis i) x •
      ((Real.sqrt (rho.spectralEigenvalues i) : Complex) • rho.spectralEigenbasis i)
  have hterm (i : Fin (Module.finrank Complex H)) :
      inner Complex ((Real.sqrt (rho.spectralEigenvalues i) : Complex) •
        rho.spectralEigenbasis i) x •
        ((Real.sqrt (rho.spectralEigenvalues i) : Complex) • rho.spectralEigenbasis i) =
      inner Complex (rho.spectralEigenbasis i) x •
        ((rho.spectralEigenvalues i : Complex) • rho.spectralEigenbasis i) := by
    rw [inner_smul_left]
    simp only [Complex.conj_ofReal, smul_smul]
    rw [show
      (Real.sqrt (rho.spectralEigenvalues i) : Complex) *
          inner Complex (rho.spectralEigenbasis i) x *
          (Real.sqrt (rho.spectralEigenvalues i) : Complex) =
        inner Complex (rho.spectralEigenbasis i) x *
          (rho.spectralEigenvalues i : Complex) by
      calc
        (Real.sqrt (rho.spectralEigenvalues i) : Complex) *
            inner Complex (rho.spectralEigenbasis i) x *
            (Real.sqrt (rho.spectralEigenvalues i) : Complex) =
          inner Complex (rho.spectralEigenbasis i) x *
            ((Real.sqrt (rho.spectralEigenvalues i) : Complex) *
              (Real.sqrt (rho.spectralEigenvalues i) : Complex)) := by ring
        _ = inner Complex (rho.spectralEigenbasis i) x *
            (rho.spectralEigenvalues i : Complex) := by
          congr 1
          exact_mod_cast (show Real.sqrt (rho.spectralEigenvalues i) *
              Real.sqrt (rho.spectralEigenvalues i) = rho.spectralEigenvalues i by
            simpa [pow_two] using Real.sq_sqrt (rho.spectralEigenvalues_nonnegative i))]
  calc
    rho.toOperator x = rho.toOperator (∑ i,
        inner Complex (rho.spectralEigenbasis i) x • rho.spectralEigenbasis i) := by
      congr 1
      exact (rho.spectralEigenbasis.sum_repr' x).symm
    _ = ∑ i, inner Complex (rho.spectralEigenbasis i) x •
        rho.toOperator (rho.spectralEigenbasis i) := by
      simp only [map_sum, map_smul]
    _ = ∑ i, inner Complex (rho.spectralEigenbasis i) x •
        ((rho.spectralEigenvalues i : Complex) • rho.spectralEigenbasis i) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold spectralEigenbasis spectralEigenvalues
      rw [rho.positive.isSymmetric.apply_eigenvectorBasis]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (hterm i).symm
noncomputable def pureDensity (psi : H) (hpsi : ‖psi‖ ^ 2 = 1) : DensityOperator H where
  toOperator := (InnerProductSpace.rankOne Complex psi psi).toLinearMap
  positive := (InnerProductSpace.isPositive_rankOne_self psi).toLinearMap
  trace_one := by
    rw [InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq_to_K]
    simpa using congrArg ((↑) : Real → Complex) hpsi
@[simp]
theorem pureDensity_toOperator (psi : H) (hpsi : ‖psi‖ ^ 2 = 1) :
    (pureDensity psi hpsi).toOperator =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap :=
  rfl
noncomputable def spectralPurification (rho : DensityOperator H) :
    DensityOperator (CompositeSystem H H) :=
  pureDensity rho.spectralPurificationVector rho.spectralPurificationVector_normSq
noncomputable def rightMarginal {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (omega : DensityOperator (CompositeSystem H K)) : DensityOperator H :=
  partialTraceRightRaw_mapDensity H K omega
noncomputable def tensorSwap (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    UnitaryTransport (CompositeSystem H K) (CompositeSystem K H) := by
  let U := TensorProduct.commIsometry Complex H K
  exact
    { toLinearEquiv := U.toLinearEquiv
      map_inner := U.inner_map_map }
@[simp]
theorem tensorSwap_apply_tmul (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (h : H) (k : K) :
    tensorSwap H K (h ⊗ₜ[Complex] k) = k ⊗ₜ[Complex] h :=
  rfl
noncomputable def leftMarginal {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (omega : DensityOperator (CompositeSystem H K)) : DensityOperator K :=
  rightMarginal ((tensorSwap H K).conjDensity omega)
noncomputable def rightTensorCoefficients {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) : Fin (Module.finrank Complex K) →₀ H :=
  TensorProduct.equivFinsuppOfBasisRight b.toBasis psi
noncomputable def rightAmplitude {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) : K →ₗ[Complex] H where
  toFun := fun k => ∑ j, inner Complex (b j) k • rightTensorCoefficients b psi j
  map_add' := by
    intro x y
    simp only [inner_add_right, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp only [inner_smul_right, RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_smul]
@[simp]
theorem rightAmplitude_apply_basis {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) (j : Fin (Module.finrank Complex K)) :
    rightAmplitude b psi (b j) = rightTensorCoefficients b psi j := by
  simp [rightAmplitude, b.inner_eq_ite]
noncomputable def coefficientMatrix {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (bH : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H)
    (bK : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) :
    Matrix (Fin (Module.finrank Complex H)) (Fin (Module.finrank Complex K)) Complex :=
  LinearMap.toMatrix bK.toBasis bH.toBasis (rightAmplitude bK psi)
def ket (psi : H) : Complex →ₗ[Complex] H where
  toFun := fun c => c • psi
  map_add' := by
    intro a b
    rw [add_smul]
  map_smul' := by
    intro a b
    change (a * b) • psi = a • (b • psi)
    rw [mul_smul]
def bra (psi : H) : H →ₗ[Complex] Complex where
  toFun := fun x => inner Complex psi x
  map_add' := by
    intro x y
    rw [inner_add_right]
  map_smul' := by
    intro c x
    rw [inner_smul_right]
    change c * inner Complex psi x = c * inner Complex psi x
    rfl
def conditionalEntropy {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (omega : DensityOperator (CompositeSystem H K)) : Real :=
  omega.vonNeumannEntropy - (rightMarginal omega).vonNeumannEntropy
omit [FiniteQuantumSystem H] in
/-- Tensoring two rank-one operators yields the rank one on the tensor product. -/
theorem tensorMap_rankOne {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (x y : H) (u v : K) :
    TensorProduct.map (InnerProductSpace.rankOne Complex x y).toLinearMap
      (InnerProductSpace.rankOne Complex u v).toLinearMap =
      (InnerProductSpace.rankOne Complex (x ⊗ₜ[Complex] u) (y ⊗ₜ[Complex] v)).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul h k =>
      change ((inner Complex y h) • x) ⊗ₜ[Complex] ((inner Complex v k) • u) =
        (inner Complex (y ⊗ₜ[Complex] v) (h ⊗ₜ[Complex] k)) • (x ⊗ₜ[Complex] u)
      rw [TensorProduct.inner_tmul, TensorProduct.smul_tmul, smul_smul,
        TensorProduct.tmul_smul]
  | add z w hz hw =>
      simp [map_add, hz, hw]
theorem tensorMap_sum_sum {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → Operator H) (b : κ → Operator K) :
    TensorProduct.map (∑ i, a i) (∑ j, b j) = ∑ i, ∑ j, TensorProduct.map (a i) (b j) := by
  classical
  have hleft (s : Finset ι) :
      TensorProduct.map (∑ i ∈ s, a i) (∑ j, b j) =
        ∑ i ∈ s, TensorProduct.map (a i) (∑ j, b j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
        simp [Finset.sum_insert hi, TensorProduct.map_add_left, ih]
  have hright (i : ι) (t : Finset κ) :
      TensorProduct.map (a i) (∑ j ∈ t, b j) =
        ∑ j ∈ t, TensorProduct.map (a i) (b j) := by
    induction t using Finset.induction_on with
    | empty => simp
    | insert j t hj ih =>
        simp [Finset.sum_insert hj, TensorProduct.map_add_right, ih]
  calc
    TensorProduct.map (∑ i, a i) (∑ j, b j) =
        ∑ i, TensorProduct.map (a i) (∑ j, b j) := by
          simpa using hleft Finset.univ
    _ = ∑ i, ∑ j, TensorProduct.map (a i) (b j) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa using hright i Finset.univ
noncomputable def tensorDensity {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) (sigma : DensityOperator K) :
    DensityOperator (CompositeSystem H K) where
  toOperator := TensorProduct.map rho.toOperator sigma.toOperator
  positive := by
    rw [rho.spectralDecomposition, sigma.spectralDecomposition, tensorMap_sum_sum]
    apply LinearMap.isPositive_sum Finset.univ
    intro i _
    apply LinearMap.isPositive_sum Finset.univ
    intro j _
    rw [tensorMap_rankOne]
    let w : CompositeSystem H K :=
      ((Real.sqrt (rho.spectralEigenvalues i) : Complex) • rho.spectralEigenbasis i) ⊗ₜ[Complex]
        ((Real.sqrt (sigma.spectralEigenvalues j) : Complex) • sigma.spectralEigenbasis j)
    exact (InnerProductSpace.isPositive_rankOne_self w).toLinearMap
  trace_one := by
    rw [LinearMap.trace_tensorProduct', rho.trace_one, sigma.trace_one, mul_one]
end DensityOperator
end
end Semantics
end QEC


