-- Prove2me | Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
-- name    : QEC_Semantics_Entropy_FiniteDimensional
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:04:38.795116+00:00
-- url     : https://prove2.me/theorems/55cbcca0-c8ba-4617-985c-0f4330a87578
-- title:
--   Finite Dimensional
-- statement:
--   Definitions and structural lemmas for Finite Dimensional, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/FiniteDimensional.lean

import Definitions.Def_QEC_Semantics_Core_Definitions
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
universe u
namespace QEC
namespace Semantics
open scoped BigOperators ComplexOrder
noncomputable section
namespace DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
def entropyTerm (x : Real) : Real :=
  if x = 0 then 0 else -x * Real.logb 2 x
@[simp]
theorem entropyTerm_zero : entropyTerm 0 = 0 := by
  simp [entropyTerm]
@[simp]
theorem entropyTerm_one : entropyTerm 1 = 0 := by
  simp [entropyTerm]
@[simp]
theorem entropyTerm_half : entropyTerm (1 / 2 : Real) = 1 / 2 := by
  rw [entropyTerm, if_neg (by norm_num)]
  have hhalf : (1 / 2 : Real) = (2 : Real)⁻¹ := by norm_num
  rw [hhalf, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
  norm_num
def finiteSpectrum (rho : DensityOperator H) : Multiset Real :=
  rho.toOperator.charpoly.roots.map Complex.re
def vonNeumannEntropy (rho : DensityOperator H) : Real :=
  (rho.finiteSpectrum.map entropyTerm).sum
def spectralEigenvalues (rho : DensityOperator H) :
    Fin (Module.finrank Complex H) -> Real :=
  rho.positive.isSymmetric.eigenvalues rfl
def spectralMatrix (rho : DensityOperator H)
    (b : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H) :
    Matrix (Fin (Module.finrank Complex H)) (Fin (Module.finrank Complex H)) Complex :=
  rho.toOperator.toMatrix b.toBasis b.toBasis
theorem spectralMatrix_isHermitian (rho : DensityOperator H)
    (b : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H) :
    (rho.spectralMatrix b).IsHermitian := by
  exact (LinearMap.isHermitian_toMatrix_iff b).2 rho.positive.isSymmetric
noncomputable def diagonalDensity (n : Nat) (p : Fin n -> Real)
    (hp : forall i, 0 <= p i) (hsum : (∑ i, p i) = 1) :
    DensityOperator (EuclideanSpace Complex (Fin n)) where
  toOperator := Matrix.toEuclideanLin (Matrix.diagonal fun i => (p i : Complex))
  positive := by
    apply Matrix.isPositive_toEuclideanLin_iff.mpr
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · apply Matrix.isHermitian_diagonal_iff.mpr
      intro i
      change star (p i : Complex) = (p i : Complex)
      simp
    · intro x
      have hquadratic :
          dotProduct (star x) (Matrix.mulVec (Matrix.diagonal fun i => (p i : Complex)) x) =
            ((∑ i, p i * Complex.normSq (x i) : Real) : Complex) := by
        simp [dotProduct, Matrix.mulVec_diagonal, Complex.normSq_eq_conj_mul_self,
          mul_comm, mul_left_comm, mul_assoc]
      rw [hquadratic]
      exact (RCLike.ofReal_nonneg (K := Complex)).mpr
        (Fintype.sum_nonneg fun i => mul_nonneg (hp i) (Complex.normSq_nonneg _))
  trace_one := by
    change LinearMap.trace Complex _
      (Matrix.toLin (EuclideanSpace.basisFun (Fin n) Complex).toBasis
        (EuclideanSpace.basisFun (Fin n) Complex).toBasis
        (Matrix.diagonal fun i => (p i : Complex))) = 1
    rw [Matrix.trace_toLin_eq]
    simp only [Matrix.trace_diagonal]
    exact_mod_cast hsum
noncomputable def diagOneZero : DensityOperator (EuclideanSpace Complex (Fin 2)) :=
  diagonalDensity 2 (fun i => if i = 0 then 1 else 0)
    (by intro i; by_cases h : i = 0 <;> simp [h])
    (by rw [Fin.sum_univ_two]; simp)
noncomputable def diagHalfHalf : DensityOperator (EuclideanSpace Complex (Fin 2)) :=
  diagonalDensity 2 (fun _ => 1 / 2)
    (by intro i; norm_num)
    (by rw [Fin.sum_univ_two]; norm_num)
end DensityOperator
end
end Semantics
end QEC


