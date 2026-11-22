-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:25:52.063402+00:00
-- url     : https://prove2.me/theorems/d01cf07d-c230-4456-85e4-b5c872cdc73f
-- title:
--   Eq Smul Canonical Of Unipotent Invariant
-- statement:
--   Definitions and structural lemmas for Eq Smul Canonical Of Unipotent Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
def qd_sig (n : ℕ) : MvPolynomial (Fin n × Fin n) ℚ →ₐ[ℚ] GLCoord ℚ n :=
  (IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n)).comp (rename Prod.swap)
variable [NeZero n]
def qd_P (mu : Fin n → ℤ) (I : TIdx mu) : MvPolynomial (Fin n × Fin n) ℚ :=
  ∏ c : ↥(TCols mu), initMinor ℚ (fun p => (I c).1.orderEmbOfFin (I c).2 p) (colH_le mu c)
def qd_U (mu : Fin n → ℤ) : GLCoord ℚ n := mapCoord ℚ ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)
def qd_nu (mu : Fin n → ℤ) : Fin n → ℕ := ∑ c : ↥(TCols mu), initW n (colH mu c)
def qd_L (mu : Fin n → ℤ) : MvPolynomial (Fin n × Fin n) ℚ →ₗ[ℚ] GLCoord ℚ n :=
  (LinearMap.mulLeft ℚ (qd_U mu)) ∘ₗ (qd_sig n).toLinearMap
omit [NeZero n] in
lemma generic_point_det_isUnit (n : ℕ) : IsUnit (Matrix.of fun a b : Fin n =>
    Polynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n) (X (a, b)))).det := by
  have : (Matrix.of fun a b : Fin n =>
      Polynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n) (X (a, b)))) =
      (Polynomial.C.comp (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n))).mapMatrix (genMat ℚ n) := by
    ext a b : 2; simp [genMat]
  rw [this, ← RingHom.map_det]
  exact (IsLocalization.Away.algebraMap_isUnit (S := GLCoord ℚ n) (genMat ℚ n).det).map Polynomial.C
def qd_genPt (n : ℕ) : GL (Fin n) (Polynomial (GLCoord ℚ n)) :=
  Matrix.GeneralLinearGroup.mk'' _ (generic_point_det_isUnit n)
def qd_trans {R : Type} [CommRing R] (a b : Fin n) (hab : a ≠ b) (t : R) : GL (Fin n) R :=
  Matrix.GeneralLinearGroup.mk'' (Matrix.transvection a b t)
    (by rw [Matrix.det_transvection_of_ne _ _ hab]; exact isUnit_one)
end Formalism.InvariantFactorPaths.ColumnFamilies


