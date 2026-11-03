-- Prove2me | Definitions.Def_Grothendieck_Reduced
-- name    : Grothendieck_Reduced
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-02T14:27:22.278465+00:00
-- url     : https://prove2.me/theorems/4d6255e6-c3d4-405e-bdde-6982331033f1
-- title:
--   The two-column reduction of the matrix Grothendieck identity: integrand and law
-- statement:
--   The matrix Grothendieck identity of the paper compares a rounding expectation over an $r\times n$ Gaussian matrix $Z$ with the scalar series $E_r(u\cdot v)$. Everything about that expectation depends on $u$ and $v$ only through their inner product $t=u\cdot v$: the $r$ rows of the pair $(Zu,Zv)\in\mathbb R^r\times\mathbb R^r$ are independent, and each row is a two-dimensional Gaussian with covariance $\big(\begin{smallmatrix}1&t\\t&1\end{smallmatrix}\big)$, which is nondegenerate whenever $|t|<1$.
--
--   This file fixes the objects in which that reduction is stated. For a random $r\times 2$ matrix $W$ (written as $r$ vectors of $\mathbb R^2$):
--
--   1. `colFun r 0 W` and `colFun r 1 W` are its two columns, vectors of $\mathbb R^r$;
--   2. `reducedIntegrand r W` is the cosine of the angle between them, $\langle W_0/\lVert W_0\rVert, W_1/\lVert W_1\rVert\rangle$, the integrand of the rounding expectation;
--   3. `reducedLaw r t` is the law of $r$ independent two-dimensional Gaussians with covariance $\big(\begin{smallmatrix}1&t\\t&1\end{smallmatrix}\big)$, i.e. the law of the two columns of the Gaussian matrix.
--
--   It also records the change of variables `cholMap t`, which carries a pair of independent standard Gaussians to the correlated pair, its transpose `cholAdj`, and the flip of the second coordinate used for negative correlation.
--
--   These are exactly the definitions the node `Grothendieck.matrix_grothendieck_identity_of_canonical` is stated in, and they are reusable for any other rounding identity whose randomness is Gaussian.
--
--   **Formalization Note** A function `Fin r → EuclideanSpace ℝ (Fin 2)` is the Lean rendering of an $r\times 2$ matrix; `Grothendieck.normalize` is the normalization to the unit sphere of the mission's Gaussian definition layer.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — Lemma 2.1, p. 84, and Algorithm A, p. 82.

import Mathlib
import Definitions.Def_Grothendieck_Series
import Definitions.Def_Grothendieck_Gaussian

/-!
# Reduction of Lemma 2.1 (matrix_grothendieck_identity) to a two-column integral

The expectation `grothendieckExpectation r n u v` of Lemma 2.1 is an integral over the
`r × n` standard Gaussian matrix `Z` of `⟪Zu/‖Zu‖, Zv/‖Zv‖⟫`.  This file fixes the two-column
object: the integrand `reducedIntegrand r W` (the cosine of the angle between the two
columns of a `r × 2` matrix `W`) and the law `reducedLaw r t` of the two columns, whose `r`
rows are independent two-dimensional Gaussians with covariance `!![1, t; t, 1]`.  The
statement that the Gaussian expectation equals the integral of `reducedIntegrand` against
`reducedLaw` is the node `Grothendieck.matrix_grothendieck_identity_of_canonical`; this file
supplies the definitions it is stated in.

It also records the change of variables `cholMap t` carrying the standard Gaussian on `ℝ²` to
the correlated one, and the row flip used to handle negative correlation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Real RealInnerProductSpace

namespace Grothendieck

/-! ### Small facts about Euclidean space coercions -/

def corrMat (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, t; t, 1]

@[simp] lemma corrMat_apply_zero_zero (t : ℝ) : corrMat t 0 0 = 1 := rfl
@[simp] lemma corrMat_apply_zero_one (t : ℝ) : corrMat t 0 1 = t := rfl
@[simp] lemma corrMat_apply_one_zero (t : ℝ) : corrMat t 1 0 = t := rfl
@[simp] lemma corrMat_apply_one_one (t : ℝ) : corrMat t 1 1 = 1 := rfl

def projFun {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) (x : Fin n → ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(∑ k, x k * (u.ofLp k)), (∑ k, x k * (v.ofLp k))]

/-- The `j`-th column of a random `r × 2` matrix, as a vector in `ℝ^r`. -/
def colFun (r : ℕ) (j : Fin 2) (W : Fin r → EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin r) :=
  WithLp.toLp 2 fun i => (W i).ofLp j

def reducedIntegrand (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) : ℝ :=
  inner ℝ (normalize r (colFun r 0 W)) (normalize r (colFun r 1 W))

/-- The law of the two columns: `r` independent correlated two-dimensional Gaussians. -/
def reducedLaw (r : ℕ) (t : ℝ) : Measure (Fin r → EuclideanSpace ℝ (Fin 2)) :=
  Measure.pi fun _ : Fin r => multivariateGaussian 0 (corrMat t)

def flipCoord (x : Fin 2 → ℝ) : Fin 2 → ℝ := ![x 0, -(x 1)]

/-- The flip of the second coordinate of `ℝ²`. -/
def flip2 (y : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (flipCoord y.ofLp)

def flipRows (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) : Fin r → EuclideanSpace ℝ (Fin 2) :=
  fun i => flip2 (W i)

def cholMap (t : ℝ) (y : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![y.ofLp 0, t * y.ofLp 0 + Real.sqrt (1 - t ^ 2) * y.ofLp 1]

/-- The transpose of `cholMap t`: `z ↦ (z₀ + t z₁, √(1-t²) z₁)`. -/
def cholAdj (t : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![z.ofLp 0 + t * z.ofLp 1, Real.sqrt (1 - t ^ 2) * z.ofLp 1]

end Grothendieck


