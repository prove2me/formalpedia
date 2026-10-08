-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_QuadraticNormRigidity_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_QuadraticNormRigidity_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:21:34.495913+00:00
-- url     : https://prove2.me/theorems/a4d04d2b-6747-4464-b5e8-05cca4c9681b
-- title:
--   FLT.Assumptions.MazurProof.QuadraticNormRigidity source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.QuadraticNormRigidity

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.QuadraticNormRigidity
Original leading source comments and nonproject imports are retained below. -/
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Trace.Basic

set_option autoImplicit false




/-!
# Square-norm rigidity in a quadratic algebra

In a two-dimensional commutative algebra over a field, an invertible element
whose square and norm are the same scalar is itself scalar.  This is the
structural quadratic-algebra step in the inverse Kummer construction; it is
just Cayley--Hamilton, with no splitting or root enumeration.
-/

namespace MazurProof.QuadraticNormRigidity

noncomputable section

variable {K E : Type*}
  [Field K] [CharZero K] [CommRing E] [Nontrivial E] [Algebra K E]
  [Module.Finite K E] [Module.Free K E]

/-- If a unit in a rank-two algebra has both square and norm equal to the
same nonzero scalar, then it comes from the ground field. -/
theorem eq_algebraMap_of_sq_eq_norm
    (b : Module.Basis (Fin 2) K E) (t : E) (s : K)
    (hs : s ≠ 0)
    (hsq : t ^ 2 = algebraMap K E s)
    (hnorm : Algebra.norm K t = s) :
    ∃ r : K, t = algebraMap K E r := by
  let φ : Module.End K E := Algebra.lmul K E t
  let A : Matrix (Fin 2) (Fin 2) K :=
    LinearMap.toMatrix b b φ
  have hchar :
      φ.charpoly =
        Polynomial.X ^ 2 -
          Polynomial.C (Algebra.trace K E t) * Polynomial.X +
          Polynomial.C (Algebra.norm K t) := by
    calc
      φ.charpoly = A.charpoly := by
        exact (LinearMap.charpoly_toMatrix φ b).symm
      _ =
          Polynomial.X ^ 2 -
            Polynomial.C A.trace * Polynomial.X +
            Polynomial.C A.det :=
        Matrix.charpoly_fin_two A
      _ =
          Polynomial.X ^ 2 -
            Polynomial.C (Algebra.trace K E t) * Polynomial.X +
            Polynomial.C (Algebra.norm K t) := by
        dsimp only [A, φ]
        rw [← Algebra.leftMulMatrix_apply]
        rw [← Algebra.trace_eq_matrix_trace b,
          ← Algebra.norm_eq_matrix_det b]
  have hcayley :=
    Algebra.aeval_self_charpoly_lmul (R := K) t
  rw [hchar] at hcayley
  simp only [map_add, map_sub, map_mul, map_pow,
    Polynomial.aeval_X, Polynomial.aeval_C] at hcayley
  rw [hsq, hnorm] at hcayley
  have htrace_ne :
      Algebra.trace K E t ≠ 0 := by
    intro htrace
    rw [htrace] at hcayley
    simp only [map_zero, zero_mul, sub_zero] at hcayley
    have hsum : s + s = 0 := by
      apply FaithfulSMul.algebraMap_injective K E
      simpa only [map_add, map_zero] using hcayley
    have htwo_s : (2 : K) * s = 0 := by
      linear_combination hsum
    exact hs
      ((mul_eq_zero.mp htwo_s).resolve_left (by norm_num))
  have hlinear :
      algebraMap K E (Algebra.trace K E t) * t =
        algebraMap K E (2 * s) := by
    calc
      algebraMap K E (Algebra.trace K E t) * t =
          algebraMap K E s + algebraMap K E s := by
        linear_combination -hcayley
      _ = algebraMap K E (s + s) := by
        rw [map_add]
      _ = algebraMap K E (2 * s) := by
        congr 1
        ring
  refine
    ⟨(2 * s) / Algebra.trace K E t, ?_⟩
  calc
    t =
        algebraMap K E (Algebra.trace K E t)⁻¹ *
          (algebraMap K E (Algebra.trace K E t) * t) := by
      rw [← mul_assoc, ← map_mul]
      simp [htrace_ne]
    _ =
        algebraMap K E (Algebra.trace K E t)⁻¹ *
          algebraMap K E (2 * s) := by
      rw [hlinear]
    _ =
        algebraMap K E
          ((Algebra.trace K E t)⁻¹ * (2 * s)) := by
      exact
        (map_mul (algebraMap K E)
          (Algebra.trace K E t)⁻¹ (2 * s)).symm
    _ =
        algebraMap K E
          ((2 * s) / Algebra.trace K E t) := by
      congr 1
      rw [div_eq_mul_inv]
      ring

/-- The scalar supplied by quadratic rigidity is itself a square root of
the common square and norm. -/
theorem exists_scalar_square_root
    (b : Module.Basis (Fin 2) K E) (t : E) (s : K)
    (hs : s ≠ 0)
    (hsq : t ^ 2 = algebraMap K E s)
    (hnorm : Algebra.norm K t = s) :
    ∃ r : K,
      t = algebraMap K E r ∧ r ^ 2 = s := by
  obtain ⟨r, hr⟩ :=
    eq_algebraMap_of_sq_eq_norm b t s hs hsq hnorm
  refine ⟨r, hr, ?_⟩
  apply FaithfulSMul.algebraMap_injective K E
  rw [map_pow, ← hr, hsq]

end

end MazurProof.QuadraticNormRigidity


