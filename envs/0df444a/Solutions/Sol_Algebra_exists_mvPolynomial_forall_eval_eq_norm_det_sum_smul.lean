-- Prove2me | solution 1 for Algebra.exists_mvPolynomial_forall_eval_eq_norm_det_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/8709d4d1-5498-51b4-bd77-cf766f32168a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_mvPolynomial_forall_eval_eq_norm_det_sum_smul

set_option autoImplicit false

open MvPolynomial

namespace P2mPoly

variable (E : Type) [CommRing E] [Algebra ℝ E] [Module.Free ℝ E] [Module.Finite ℝ E]
  (m : Type) [Fintype m] [DecidableEq m] (n : ℕ) (e : Fin n → Matrix m m E)

noncomputable def genMat : Matrix m m (MvPolynomial (Fin n) E) :=
  ∑ a, (X a : MvPolynomial (Fin n) E) • (e a).map (C : E → MvPolynomial (Fin n) E)

noncomputable def genDet : MvPolynomial (Fin n) E := (genMat E m n e).det

noncomputable def evE (c : Fin n → ℝ) : MvPolynomial (Fin n) E →+* E :=
  MvPolynomial.eval fun a => algebraMap ℝ E (c a)

theorem evE_genMat (c : Fin n → ℝ) :
    (evE E n c).mapMatrix (genMat E m n e) = ∑ a, c a • e a := by
  ext p q
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  simp only [genMat, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, evE, MvPolynomial.eval_X, MvPolynomial.eval_C, Algebra.smul_def]

theorem evE_genDet (c : Fin n → ℝ) : evE E n c (genDet E m n e) = (∑ a, c a • e a).det := by
  rw [genDet, RingHom.map_det, evE_genMat]

theorem evE_eq_sum (c : Fin n → ℝ) (D : MvPolynomial (Fin n) E) :
    evE E n c D = ∑ s ∈ D.support, (s.prod fun a k => c a ^ k) • MvPolynomial.coeff s D := by
  conv_lhs => rw [MvPolynomial.as_sum D]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [evE, MvPolynomial.eval_monomial, Algebra.smul_def, mul_comm]
  congr 1
  rw [Finsupp.prod, Finsupp.prod, map_prod]
  exact Finset.prod_congr rfl fun a _ => by rw [map_pow]

variable {κ : Type} [Fintype κ] [DecidableEq κ] (b : Module.Basis κ ℝ E)

noncomputable def lmPoly : Matrix κ κ (MvPolynomial (Fin n) ℝ) :=
  ∑ s ∈ (genDet E m n e).support,
    (Algebra.leftMulMatrix b (MvPolynomial.coeff s (genDet E m n e))).map fun r => MvPolynomial.monomial s r

theorem eval_lmPoly (c : Fin n → ℝ) :
    (MvPolynomial.eval c).mapMatrix (lmPoly E m n e b) =
      Algebra.leftMulMatrix b (evE E n c (genDet E m n e)) := by
  rw [evE_eq_sum, map_sum]
  ext k l
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, lmPoly, Matrix.sum_apply, map_sum,
    MvPolynomial.eval_monomial, map_smul, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

end P2mPoly

open P2mPoly in
theorem solution
    (E : Type) [CommRing E] [Algebra ℝ E] [Module.Free ℝ E] [Module.Finite ℝ E]
    (m : Type) [Fintype m] [DecidableEq m]
    (n : ℕ) (e : Fin n → Matrix m m E) :
    ∃ P : MvPolynomial (Fin n) ℝ, ∀ c : Fin n → ℝ,
      MvPolynomial.eval c P = Algebra.norm ℝ (Matrix.det (∑ a, c a • e a)) := by
  classical
  let b := Module.Free.chooseBasis ℝ E
  refine ⟨(lmPoly E m n e b).det, fun c => ?_⟩
  rw [RingHom.map_det, eval_lmPoly, ← Algebra.norm_eq_matrix_det b, evE_genDet]

#print axioms solution

end S_Algebra_exists_mvPolynomial_forall_eval_eq_norm_det_sum_smul
end P2MW
export P2MW.S_Algebra_exists_mvPolynomial_forall_eval_eq_norm_det_sum_smul (solution)
