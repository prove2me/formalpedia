-- Prove2me | Definitions.Def_ShapeSOS_ConvexConsistency_Algebra
-- name    : ShapeSOS_ConvexConsistency_Algebra
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T23:21:57.716313+00:00
-- url     : https://prove2.me/theorems/ceb48ccf-e042-4dbf-a335-fe22951b1284
-- title:
--   Exact degree cones, Theta, Phi, and the geometric band matrix
-- statement:
--   The degree-capped SOS cone contains exactly the published finite sums of squares whose total degree meets the given integer cap. For negative caps only zero is allowed. Matrix cones use the published factorization $S=V^TV$ and bound the total degree of each entry of $S$, without bounding the number of rows of $V$.
--
--   The perturbations are exactly
--   $$\Theta_d(x)=\sum_i x_i^2+\sum_{i<j}(8x_i^{2d+2}+x_i^{2d}x_j^2+x_i^2x_j^{2d}+8x_j^{2d+2}),\qquad
--   \Phi_d(x,y)=\sum_i y_i^2(1+\sum_j x_j^{2d}).$$
--   The quadratic expression $y^TM(x)y$ is one polynomial in the joint variables $(x,y)$.
--
--   The geometric entries interpolate positive endpoints by $a_i=a_1(a_n/a_1)^{(i-1)/(n-1)}$ using real exponents. The band matrix has diagonal $a_i/2$ at indices $1,2,n-1,n$ and $a_i$ elsewhere, with second off-diagonal entries $-a_i/2$ indexed by their middle coordinate. All other entries vanish. These are the source objects, including small dimensions.
-- source:
--   Curmei and Hall, Shape-Constrained Regression using Sum of Squares Polynomials, arXiv:2004.03853v3, pp. 3–4 and 8–11, Theorem 3.1, Proposition 3.4, Lemmas 3.6–3.7

import Definitions.Def_ShapeSOS_ConvexConsistency_Geometry
import Definitions.Def_RobustPMI_Hierarchy_Model

set_option autoImplicit false
open scoped BigOperators

namespace ShapeSOS.ConvexConsistency
noncomputable section
open MvPolynomial

/-- Integer degree cap: the zero polynomial is allowed even under negative caps. -/
def degreeCap {n : ℕ} (k : ℤ) (p : Poly n) : Prop :=
  p = 0 ∨ (p.totalDegree : ℤ) ≤ k

def sosCap {n : ℕ} (k : ℤ) (p : Poly n) : Prop :=
  RobustPMI.Hierarchy.IsSOSPoly p ∧ degreeCap k p

def sosMatrixCap {n : ℕ} (k : ℤ) (S : PMat n) : Prop :=
  RobustPMI.Hierarchy.IsSOSMat S ∧ ∀ i j, degreeCap k (S i j)

/-- Theorem 3.1, exactly including the empty pair sum when n=1. -/
def theta (n d : ℕ) : Poly n :=
  (∑ i, X i ^ 2) + ∑ i, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
    (8 * X i ^ (2*d+2) + X i ^ (2*d) * X j ^ 2 +
      X i ^ 2 * X j ^ (2*d) + 8 * X j ^ (2*d+2))

abbrev JointPoly (n : ℕ) := MvPolynomial (Fin n ⊕ Fin n) ℝ

/-- yᵀM(x)y as one joint polynomial, not a family with numerical y. -/
def jointQuadratic {n : ℕ} (M : PMat n) : JointPoly n :=
  ∑ i, ∑ j, X (Sum.inr i) * rename Sum.inl (M i j) * X (Sum.inr j)

def phi (n d : ℕ) : JointPoly n :=
  ∑ i : Fin n, X (Sum.inr i) ^ 2 * (1 + ∑ j : Fin n, X (Sum.inl j) ^ (2*d))

/-- Zero-based version of the geometric entries, with endpoints supplied explicitly. -/
def geometricEntries (n : ℕ) (first last : ℝ) (i : Fin n) : ℝ :=
  if i.val = 0 then first else if i.val + 1 = n then last
  else first * Real.rpow (last / first) ((i.val : ℝ) / ((n : ℝ) - 1))

/-- All small compatible sizes are included; diagonal boundary cases take precedence. -/
def geometricMatrix (n : ℕ) (first last : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if i = j then
      if i.val < 2 ∨ n ≤ i.val + 2 then geometricEntries n first last i / 2
      else geometricEntries n first last i
    else if i.val + 2 = j.val then
      -(first * Real.rpow (last / first) (((i.val : ℝ) + 1) / ((n : ℝ) - 1))) / 2
    else if j.val + 2 = i.val then
      -(first * Real.rpow (last / first) (((j.val : ℝ) + 1) / ((n : ℝ) - 1))) / 2
    else 0

end
end ShapeSOS.ConvexConsistency


