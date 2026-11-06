-- Prove2me | Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
-- name    : QEC_Semantics_Dynamics_ThermalEncoding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:45:50.386321+00:00
-- url     : https://prove2.me/theorems/92507c9a-c57d-4624-9495-ff9580e67433
-- title:
--   Thermal Encoding
-- statement:
--   Definitions and structural lemmas for Thermal Encoding, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC
namespace Semantics
namespace ThermalEncoding
open Classical
open scoped BigOperators ComplexOrder TensorProduct
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace DensityOperator
end DensityOperator
def gibbsPartitionFunction {ι : Type} [Fintype ι]
    (beta : Real) (energy : ι → Real) : Real :=
  ∑ i, Real.exp (-beta * energy i)
theorem gibbsPartitionFunction_pos {ι : Type} [Fintype ι] [Nonempty ι]
    (beta : Real) (energy : ι → Real) :
    0 < gibbsPartitionFunction beta energy := by
  exact Finset.sum_pos' (fun i _ => (Real.exp_pos _).le)
    (by exact ⟨Classical.choice ‹Nonempty ι›, Finset.mem_univ _,
      Real.exp_pos _⟩)
def gibbsProbability {ι : Type} [Fintype ι] [Nonempty ι]
    (beta : Real) (energy : ι → Real) (i : ι) : Real :=
  Real.exp (-beta * energy i) / gibbsPartitionFunction beta energy
theorem gibbsProbability_nonnegative {ι : Type} [Fintype ι] [Nonempty ι]
    (beta : Real) (energy : ι → Real) (i : ι) :
    0 ≤ gibbsProbability beta energy i :=
  div_nonneg (Real.exp_pos _).le (gibbsPartitionFunction_pos beta energy).le
theorem gibbsProbability_sum_eq_one {ι : Type} [Fintype ι] [Nonempty ι]
    (beta : Real) (energy : ι → Real) :
    (∑ i, gibbsProbability beta energy i) = 1 := by
  rw [show (∑ i, gibbsProbability beta energy i) =
      (∑ i, Real.exp (-beta * energy i)) /
        gibbsPartitionFunction beta energy by
    simp [gibbsProbability, Finset.sum_div]]
  exact div_self (gibbsPartitionFunction_pos beta energy).ne'
def spectralGibbsDensity {ι : Type} [Fintype ι] [Nonempty ι]
    (b : OrthonormalBasis ι Complex H) (energy : ι → Real) (beta : Real) :
    DensityOperator H where
  toOperator :=
    ∑ i, (gibbsProbability beta energy i : Complex) •
      (InnerProductSpace.rankOne Complex (b i) (b i)).toLinearMap
  positive := by
    apply LinearMap.isPositive_sum Finset.univ
    intro i _
    exact (InnerProductSpace.isPositive_rankOne_self (b i)).toLinearMap.smul_of_nonneg
      (by exact_mod_cast gibbsProbability_nonnegative beta energy i)
  trace_one := by
    rw [map_sum]
    simp only [map_smul, InnerProductSpace.trace_rankOne]
    have hnorm (i : ι) : inner Complex (b i) (b i) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, b.norm_eq_one]
      norm_num
    simp_rw [hnorm]
    simp only [smul_eq_mul, mul_one]
    rw [← Complex.ofReal_sum]
    exact_mod_cast gibbsProbability_sum_eq_one beta energy
@[simp]
theorem spectralGibbsDensity_apply_basis {ι : Type} [Fintype ι] [Nonempty ι]
    (b : OrthonormalBasis ι Complex H) (energy : ι → Real) (beta : Real) (i : ι) :
    (spectralGibbsDensity b energy beta).toOperator (b i) =
      (gibbsProbability beta energy i : Complex) • b i := by
  classical
  simp [spectralGibbsDensity, LinearMap.sum_apply,
    InnerProductSpace.rankOne_apply, b.inner_eq_ite]
structure PauliLikePair (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H] where
  x : Operator H
  z : Operator H
  x_symmetric : x.IsSymmetric
  z_symmetric : z.IsSymmetric
  x_sq : x * x = 1
  z_sq : z * z = 1
  anticommute : x * z = -(z * x)
namespace PauliLikePair
variable (P : PauliLikePair H)
abbrev AuxiliarySpace : Type :=
  Module.End.eigenspace P.z (1 : Complex)
abbrev NegativeSpace : Type :=
  Module.End.eigenspace P.z (-1 : Complex)
theorem x_apply_x (v : H) : P.x (P.x v) = v := by
  have h := congrArg (fun A : Operator H => A v) P.x_sq
  simpa [Module.End.mul_apply] using h
theorem z_apply_z (v : H) : P.z (P.z v) = v := by
  have h := congrArg (fun A : Operator H => A v) P.z_sq
  simpa [Module.End.mul_apply] using h
theorem z_x_anticommute : P.z * P.x = -(P.x * P.z) := by
  calc
    P.z * P.x = -(-(P.z * P.x)) := by simp
    _ = -(P.x * P.z) := by rw [P.anticommute]
theorem x_preserves_inner (v w : H) :
    inner Complex (P.x v) (P.x w) = inner Complex v w := by
  rw [P.x_symmetric v (P.x w), P.x_apply_x]
theorem auxiliary_mem_iff (v : H) :
    v ∈ Module.End.eigenspace P.z (1 : Complex) ↔ P.z v = v := by
  rw [Module.End.mem_eigenspace_iff]
  simp
theorem negative_mem_iff (v : H) :
    v ∈ Module.End.eigenspace P.z (-1 : Complex) ↔ P.z v = -v := by
  rw [Module.End.mem_eigenspace_iff]
  simp
noncomputable def xAuxToNegative : P.AuxiliarySpace →ₗ[Complex] P.NegativeSpace where
  toFun v := ⟨P.x v, by
    rw [P.negative_mem_iff]
    have hzx : P.z (P.x (v : H)) = -P.x (P.z (v : H)) := by
      simpa [Module.End.mul_apply] using
        congrArg (fun A : Operator H => A (v : H)) P.z_x_anticommute
    have hvz : P.z (v : H) = v :=
      (P.auxiliary_mem_iff (v : H)).1 v.property
    rw [hzx, hvz]⟩
  map_add' v w := by
    ext
    simp
  map_smul' c v := by
    ext
    simp
noncomputable def xNegativeToAux : P.NegativeSpace →ₗ[Complex] P.AuxiliarySpace where
  toFun v := ⟨P.x v, by
    rw [P.auxiliary_mem_iff]
    have hzx : P.z (P.x (v : H)) = -P.x (P.z (v : H)) := by
      simpa [Module.End.mul_apply] using
        congrArg (fun A : Operator H => A (v : H)) P.z_x_anticommute
    have hvz : P.z (v : H) = -v :=
      (P.negative_mem_iff (v : H)).1 v.property
    rw [hzx, hvz]
    simp⟩
  map_add' v w := by
    ext
    simp
  map_smul' c v := by
    ext
    simp
noncomputable def xEigenspaceEquiv : P.AuxiliarySpace ≃ₗ[Complex] P.NegativeSpace where
  toLinearMap := P.xAuxToNegative
  invFun := P.xNegativeToAux
  left_inv v := by
    ext
    exact P.x_apply_x v
  right_inv v := by
    ext
    exact P.x_apply_x v
theorem positive_negative_disjoint :
    Disjoint (Module.End.eigenspace P.z (1 : Complex))
      (Module.End.eigenspace P.z (-1 : Complex)) := by
  rw [Submodule.disjoint_def]
  intro v hvpos hvneg
  have hpos : P.z v = v := P.auxiliary_mem_iff v |>.1 hvpos
  have hneg : P.z v = -v := P.negative_mem_iff v |>.1 hvneg
  have hvnegself : v = -v := hpos.symm.trans hneg
  have htwo : (2 : Complex) • v = 0 := by
    rw [two_smul]
    exact (congrArg (fun w : H => w + v) hvnegself).trans (neg_add_cancel v)
  have hv : v = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  rw [hv]
theorem positive_negative_codisjoint :
    Codisjoint (Module.End.eigenspace P.z (1 : Complex))
      (Module.End.eigenspace P.z (-1 : Complex)) := by
  rw [codisjoint_iff_le_sup]
  intro v _
  let vp : H := (2 : Complex)⁻¹ • (v + P.z v)
  let vn : H := (2 : Complex)⁻¹ • (v - P.z v)
  have hvp : vp ∈ Module.End.eigenspace P.z (1 : Complex) := by
    rw [P.auxiliary_mem_iff]
    simp only [vp, map_smul, map_add, P.z_apply_z]
    module
  have hvn : vn ∈ Module.End.eigenspace P.z (-1 : Complex) := by
    rw [P.negative_mem_iff]
    simp only [vn, map_smul, map_sub, P.z_apply_z]
    module
  rw [Submodule.mem_sup']
  refine ⟨⟨vp, hvp⟩, ⟨vn, hvn⟩, ?_⟩
  dsimp [vp, vn]
  module
theorem positive_negative_isCompl :
    IsCompl (Module.End.eigenspace P.z (1 : Complex))
      (Module.End.eigenspace P.z (-1 : Complex)) :=
  ⟨P.positive_negative_disjoint, P.positive_negative_codisjoint⟩
noncomputable def qubitAuxCoordinates :
    CompositeSystem Qubit.QubitSpace P.AuxiliarySpace ≃ₗ[Complex]
      P.AuxiliarySpace × P.AuxiliarySpace :=
  (TensorProduct.comm Complex Qubit.QubitSpace P.AuxiliarySpace).trans
    (((WithLp.linearEquiv 2 Complex (Fin 2 → Complex)).lTensor P.AuxiliarySpace).trans
      ((TensorProduct.piScalarRight Complex Complex P.AuxiliarySpace (Fin 2)).trans
        (LinearEquiv.finTwoArrow Complex P.AuxiliarySpace)))
noncomputable def factorizationLinearEquiv :
    CompositeSystem Qubit.QubitSpace P.AuxiliarySpace ≃ₗ[Complex] H :=
  P.qubitAuxCoordinates |>.trans
    ((LinearEquiv.prodCongr (LinearEquiv.refl Complex P.AuxiliarySpace)
      P.xEigenspaceEquiv).trans
        (Submodule.prodEquivOfIsCompl
          (Module.End.eigenspace P.z (1 : Complex))
          (Module.End.eigenspace P.z (-1 : Complex))
          P.positive_negative_isCompl))
theorem factorizationLinearEquiv_tmul
    (q : Qubit.QubitSpace) (a : P.AuxiliarySpace) :
    P.factorizationLinearEquiv (q ⊗ₜ[Complex] a) =
      q 0 • (a : H) + q 1 • P.x (a : H) := by
  simp [factorizationLinearEquiv, qubitAuxCoordinates,
    LinearEquiv.trans_apply, xEigenspaceEquiv, xAuxToNegative]
theorem inner_aux_x_aux_eq_zero (a b : P.AuxiliarySpace) :
    inner Complex (a : H) (P.x (b : H)) = 0 := by
  have ha : P.z (a : H) = a :=
    (P.auxiliary_mem_iff (a : H)).1 a.property
  have hxb : P.z (P.x (b : H)) = -P.x (b : H) := by
    exact (P.negative_mem_iff (P.x (b : H))).1
      (P.xAuxToNegative b).property
  have hneg :
      inner Complex (a : H) (P.x (b : H)) =
        -inner Complex (a : H) (P.x (b : H)) := by
    calc
      inner Complex (a : H) (P.x (b : H)) =
          inner Complex (P.z (a : H)) (P.x (b : H)) := by rw [ha]
      _ = inner Complex (a : H) (P.z (P.x (b : H))) :=
        P.z_symmetric (a : H) (P.x (b : H))
      _ = -inner Complex (a : H) (P.x (b : H)) := by
        rw [hxb, inner_neg_right]
  exact CharZero.eq_neg_self_iff.mp hneg
theorem inner_x_aux_aux_eq_zero (a b : P.AuxiliarySpace) :
    inner Complex (P.x (a : H)) (b : H) = 0 := by
  rw [← inner_conj_symm]
  simp [P.inner_aux_x_aux_eq_zero]
theorem factorizationLinearEquiv_tmul_inner
    (q r : Qubit.QubitSpace) (a b : P.AuxiliarySpace) :
    inner Complex
        (P.factorizationLinearEquiv (q ⊗ₜ[Complex] a))
        (P.factorizationLinearEquiv (r ⊗ₜ[Complex] b)) =
      inner Complex (q ⊗ₜ[Complex] a) (r ⊗ₜ[Complex] b) := by
  rw [P.factorizationLinearEquiv_tmul, P.factorizationLinearEquiv_tmul,
    TensorProduct.inner_tmul]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    P.inner_aux_x_aux_eq_zero, P.inner_x_aux_aux_eq_zero, mul_zero,
    add_zero, zero_add, P.x_preserves_inner]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two]
  ring
theorem factorizationLinearEquiv_map_inner
    (v w : CompositeSystem Qubit.QubitSpace P.AuxiliarySpace) :
    inner Complex (P.factorizationLinearEquiv v) (P.factorizationLinearEquiv w) =
      inner Complex v w := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul q a =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul r b => exact P.factorizationLinearEquiv_tmul_inner q r a b
      | add first second hfirst hsecond =>
          simp only [map_add, inner_add_right, hfirst, hsecond]
  | add first second hfirst hsecond =>
      simp only [map_add, inner_add_left, hfirst, hsecond]
noncomputable def factorization :
    UnitaryTransport
      (CompositeSystem Qubit.QubitSpace P.AuxiliarySpace) H where
  toLinearEquiv := P.factorizationLinearEquiv
  map_inner := P.factorizationLinearEquiv_map_inner
noncomputable def tensorPauliX :
    Operator (CompositeSystem Qubit.QubitSpace P.AuxiliarySpace) :=
  TensorProduct.map Qubit.pauliX (1 : Operator P.AuxiliarySpace)
noncomputable def tensorPauliZ :
    Operator (CompositeSystem Qubit.QubitSpace P.AuxiliarySpace) :=
  TensorProduct.map Qubit.pauliZ (1 : Operator P.AuxiliarySpace)
@[simp]
theorem tensorPauliX_tmul (q : Qubit.QubitSpace) (a : P.AuxiliarySpace) :
    P.tensorPauliX (q ⊗ₜ[Complex] a) = Qubit.pauliX q ⊗ₜ[Complex] a := by
  simp [tensorPauliX]
@[simp]
theorem tensorPauliZ_tmul (q : Qubit.QubitSpace) (a : P.AuxiliarySpace) :
    P.tensorPauliZ (q ⊗ₜ[Complex] a) = Qubit.pauliZ q ⊗ₜ[Complex] a := by
  simp [tensorPauliZ]
noncomputable def auxiliaryOperator (A : Operator H) (hZ : Commute A P.z) :
    Operator P.AuxiliarySpace where
  toFun a := ⟨A a, by
    rw [P.auxiliary_mem_iff]
    have hcomm : P.z (A (a : H)) = A (P.z (a : H)) := by
      simpa [Module.End.mul_apply] using
        congrArg (fun T : Operator H => T (a : H)) hZ.eq.symm
    rw [hcomm, (P.auxiliary_mem_iff (a : H)).1 a.property]⟩
  map_add' a b := by
    ext
    simp
  map_smul' c a := by
    ext
    simp
noncomputable def tensorAuxiliaryOperator (A : Operator H) (hZ : Commute A P.z) :
    Operator (CompositeSystem Qubit.QubitSpace P.AuxiliarySpace) :=
  TensorProduct.map (1 : Operator Qubit.QubitSpace) (P.auxiliaryOperator A hZ)
@[simp]
theorem tensorAuxiliaryOperator_tmul
    (A : Operator H) (hZ : Commute A P.z)
    (q : Qubit.QubitSpace) (a : P.AuxiliarySpace) :
    P.tensorAuxiliaryOperator A hZ (q ⊗ₜ[Complex] a) =
      q ⊗ₜ[Complex] P.auxiliaryOperator A hZ a := by
  simp [tensorAuxiliaryOperator]
end PauliLikePair
section Preparation
variable {K : Type}
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
noncomputable def prepareRightBranch (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (v : K) : H →ₗ[Complex] CompositeSystem H K :=
  TensorProduct.mk Complex H K |>.flip v
@[simp]
theorem prepareRightBranch_apply (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (v : K) (h : H) :
    prepareRightBranch H K v h = h ⊗ₜ[Complex] v :=
  rfl
theorem adjoint_prepareRightBranch_comp (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (v : K) :
    (LinearMap.adjoint (prepareRightBranch H K v)).comp (prepareRightBranch H K v) =
      (inner Complex v v) • (1 : Operator H) := by
  apply LinearMap.ext
  intro h
  apply (ext_iff_inner_left Complex).mpr
  intro g
  change inner Complex g
      (LinearMap.adjoint (prepareRightBranch H K v)
        (prepareRightBranch H K v h)) =
    inner Complex g (((inner Complex v v) • (1 : Operator H)) h)
  rw [LinearMap.adjoint_inner_right]
  simp [prepareRightBranch, TensorProduct.inner_tmul, mul_comm]
noncomputable def spectralEnsembleVector (sigma : DensityOperator K)
    (i : Fin (Module.finrank Complex K)) : K :=
  (Real.sqrt (sigma.spectralEigenvalues i) : Complex) • sigma.spectralEigenbasis i
theorem spectralEnsembleVector_sum_inner (sigma : DensityOperator K) :
    ∑ i, inner Complex (spectralEnsembleVector sigma i)
      (spectralEnsembleVector sigma i) = 1 := by
  have htrace := sigma.trace_one
  rw [sigma.spectralDecomposition] at htrace
  change (∑ i, inner Complex
    ((Real.sqrt (sigma.spectralEigenvalues i) : Complex) • sigma.spectralEigenbasis i)
    ((Real.sqrt (sigma.spectralEigenvalues i) : Complex) • sigma.spectralEigenbasis i)) = 1
  simpa only [map_sum, InnerProductSpace.trace_rankOne] using htrace
noncomputable def prepareRightKraus (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) :
    FiniteKrausFamily (Fin (Module.finrank Complex K)) H (CompositeSystem H K) where
  operator i := prepareRightBranch H K (spectralEnsembleVector sigma i)
theorem prepareRightKraus_complete (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) :
    (prepareRightKraus H K sigma).Complete := by
  rw [FiniteKrausFamily.Complete]
  simp only [prepareRightKraus, adjoint_prepareRightBranch_comp]
  apply LinearMap.ext
  intro h
  calc
    (∑ i, inner Complex (spectralEnsembleVector sigma i)
        (spectralEnsembleVector sigma i) • (1 : Operator H)) h =
      (∑ i, inner Complex (spectralEnsembleVector sigma i)
        (spectralEnsembleVector sigma i)) • h := by
          simp [Finset.sum_smul]
    _ = h := by rw [spectralEnsembleVector_sum_inner]; simp
noncomputable def prepareRight (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) : QuantumChannel H (CompositeSystem H K) :=
  (prepareRightKraus H K sigma).toQuantumChannel
    (prepareRightKraus_complete H K sigma)
end Preparation
namespace PauliLikePair
variable (P : PauliLikePair H)
noncomputable def maximallyMixedQubit : DensityOperator Qubit.QubitSpace where
  toOperator := (2 : Complex)⁻¹ • (1 : Operator Qubit.QubitSpace)
  positive := by
    have htwo : 0 ≤ (2 : Complex) := by
      exact_mod_cast (show (0 : Nat) ≤ 2 by norm_num)
    exact LinearMap.isPositive_one.smul_of_nonneg ((inv_nonneg).2 htwo)
  trace_one := by
    rw [map_smul, LinearMap.trace_one, finrank_euclideanSpace]
    norm_num
theorem auxiliaryOperator_symmetric
    (A : Operator H) (hZ : Commute A P.z) (hA : A.IsSymmetric) :
    (P.auxiliaryOperator A hZ).IsSymmetric := by
  intro a b
  change inner Complex (A (a : H)) (b : H) =
    inner Complex (a : H) (A (b : H))
  exact hA (a : H) (b : H)
section Gibbs
variable [Nontrivial P.AuxiliarySpace]
local instance _p2m_local_instance_c824123c1a_1011 : Nonempty (Fin (Module.finrank Complex P.AuxiliarySpace)) :=
  Fin.pos_iff_nonempty.mp Module.finrank_pos
noncomputable def auxiliaryHamiltonianEigenbasis
    (A : Operator H) (hZ : Commute A P.z) (hA : A.IsSymmetric) :
    OrthonormalBasis (Fin (Module.finrank Complex P.AuxiliarySpace))
      Complex P.AuxiliarySpace :=
  (P.auxiliaryOperator_symmetric A hZ hA).eigenvectorBasis rfl
noncomputable def auxiliaryHamiltonianEnergies
    (A : Operator H) (hZ : Commute A P.z) (hA : A.IsSymmetric) :
    Fin (Module.finrank Complex P.AuxiliarySpace) → Real :=
  (P.auxiliaryOperator_symmetric A hZ hA).eigenvalues rfl
noncomputable def auxiliaryGibbsState
    (A : Operator H) (hZ : Commute A P.z) (hA : A.IsSymmetric) (beta : Real) :
    DensityOperator P.AuxiliarySpace :=
  spectralGibbsDensity
    (P.auxiliaryHamiltonianEigenbasis A hZ hA)
    (P.auxiliaryHamiltonianEnergies A hZ hA) beta
noncomputable def tensorHamiltonianEigenbasis
    (A : Operator H) (hZ : Commute A P.z) (hA : A.IsSymmetric) :
    OrthonormalBasis
      (Fin 2 × Fin (Module.finrank Complex P.AuxiliarySpace))
      Complex (CompositeSystem Qubit.QubitSpace P.AuxiliarySpace) :=
  (EuclideanSpace.basisFun (Fin 2) Complex).tensorProduct
    (P.auxiliaryHamiltonianEigenbasis A hZ hA)
noncomputable def physicalHamiltonianEigenbasis
    (A : Operator H) (hZ : Commute A P.z) (hA : A.IsSymmetric) :
    OrthonormalBasis
      (Fin 2 × Fin (Module.finrank Complex P.AuxiliarySpace)) Complex H :=
  (P.tensorHamiltonianEigenbasis A hZ hA).map
    P.factorization.toLinearIsometryEquiv
noncomputable def physicalHamiltonianEnergies
    (A : Operator H) (hZ : Commute A P.z) (hA : A.IsSymmetric) :
    (Fin 2 × Fin (Module.finrank Complex P.AuxiliarySpace)) → Real :=
  fun qi => P.auxiliaryHamiltonianEnergies A hZ hA qi.2
noncomputable def physicalGibbsState
    (A : Operator H) (hZ : Commute A P.z) (hA : A.IsSymmetric) (beta : Real) :
    DensityOperator H :=
  spectralGibbsDensity
    (P.physicalHamiltonianEigenbasis A hZ hA)
    (P.physicalHamiltonianEnergies A hZ hA) beta
end Gibbs
noncomputable def thermalEncoding (sigma : DensityOperator P.AuxiliarySpace) :
    QuantumChannel Qubit.QubitSpace H :=
  QuantumChannel.comp (QuantumChannel.unitaryConj P.factorization)
    (prepareRight Qubit.QubitSpace P.AuxiliarySpace sigma)
noncomputable def thermalDecoding :
    QuantumChannel H Qubit.QubitSpace :=
  QuantumChannel.comp
    (partialTraceRightRaw_cptp Qubit.QubitSpace P.AuxiliarySpace)
    (QuantumChannel.unitaryConj P.factorization.symm)
noncomputable def thermalReferenceState (sigma : DensityOperator P.AuxiliarySpace) :
    DensityOperator H :=
  P.factorization.conjDensity (DensityOperator.tensorDensity maximallyMixedQubit sigma)
noncomputable def encodedObservable (eta : DensityOperator Qubit.QubitSpace) :
    Operator H :=
  P.factorization.conjOperator
    (TensorProduct.map ((2 : Complex) • eta.toOperator)
      (1 : Operator P.AuxiliarySpace))
end PauliLikePair
end ThermalEncoding
end Semantics
end QEC


