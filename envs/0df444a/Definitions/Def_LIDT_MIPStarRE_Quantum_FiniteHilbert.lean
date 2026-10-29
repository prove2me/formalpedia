-- Prove2me | Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
-- name    : LIDT_MIPStarRE_Quantum_FiniteHilbert
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:46:19.818186+00:00
-- url     : https://prove2.me/theorems/f29f5f76-1517-44cd-be96-529dd411c237
-- title:
--   LIDT definitions: Quantum / FiniteHilbert
-- statement:
--   This bundle records finite-dimensional matrix identities for rectangular operators. It identifies the linear map represented by an adjoint product and proves that orthonormal rows give the coisometry identity.
--
--   Principal definitions:
--   - `toEuclideanLin_conjTranspose_mul_self`: The Euclidean linear map of $A^\dagger A$ is the adjoint composition of the map represented by $A$.
--   - `mul_conjTranspose_eq_one_of_orthonormal_rows`: If the rows of $A$ are orthonormal, then $AA^\dagger=I$.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/Quantum/FiniteHilbert.lean#L57-L87

-- Generated from MIPStarRE/Quantum/FiniteHilbert.lean by skeleton subtraction.
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped _root_.Matrix

namespace LIDT

/-!
# Finite-dimensional Hilbert spaces

This file contains small reusable lemmas about finite-dimensional Hilbert
spaces which are independent of the low individual degree test.  The first
ingredient is the elementary fact that a Hilbert space embeds linearly and
isometrically into any finite-dimensional Hilbert space of at least the same
dimension.  The second translates this dimension-controlled isometry into a
rectangular matrix with orthonormal rows.

## References

The construction is the standard one: choose orthonormal bases in the two
spaces and send the first basis into the corresponding initial segment of the
second basis.  The resulting matrix statement is the finite-dimensional
coisometry identity used in the paper's rectangular `Xhat` construction.
-/

@[expose] public section

open Module

namespace LinearIsometry



end LinearIsometry

namespace Matrix

/-- The matrix of an adjoint product is the adjoint-composition of the
corresponding Euclidean linear map. -/
theorem toEuclideanLin_conjTranspose_mul_self
    {𝕜 : Type*} [RCLike 𝕜]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) :
    Matrix.toEuclideanLin (Aᴴ * A) =
      (Matrix.toEuclideanLin A).adjoint.comp (Matrix.toEuclideanLin A) := by
  classical
  rw [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same (p := (2 : ENNReal)),
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

/-- A matrix whose rows form an orthonormal family is a coisometry. -/
theorem mul_conjTranspose_eq_one_of_orthonormal_rows
    {𝕜 : Type*} [RCLike 𝕜]
    {m n : Type*} [DecidableEq m] [Fintype n]
    (row : m → EuclideanSpace 𝕜 n)
    (hrow : Orthonormal 𝕜 row) :
    (Matrix.of fun i j => row i j) * (Matrix.of fun i j => row i j)ᴴ =
      (1 : Matrix m m 𝕜) := by
  classical
  ext i j
  have horth := orthonormal_iff_ite.mp hrow j i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.one_apply]
  calc
    ∑ k, row i k * star (row j k) = inner 𝕜 (row j) (row i) := by
      simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    _ = if j = i then (1 : 𝕜) else 0 := horth
    _ = if i = j then (1 : 𝕜) else 0 := by
      by_cases hij : i = j <;> simp [hij, eq_comm]



end Matrix

end

/- The QPBT consumer reaches Mathlib's compiler-generated equation theorem for
`Matrix.toEuclideanLin`. Compiler companions are normally regenerated with
their parent declaration, but this parent belongs to Mathlib rather than the
vendored project. Re-export the exact equation under the upload namespace. -/
namespace Matrix.toEuclideanLin

universe u v w

@[defeq] theorem eq_1
    {𝕜 : Type u} [RCLike 𝕜] {m : Type v} {n : Type w}
    [Fintype n] [DecidableEq n] :
    @_root_.Matrix.toEuclideanLin 𝕜 _ m n _ _ =
      @_root_.Matrix.toLpLin m n 𝕜 _ _ _ 2 2 := by
  exact _root_.Matrix.toEuclideanLin.eq_1

end Matrix.toEuclideanLin

end LIDT


