-- Prove2me | Definitions.Def_AffineBernstein
-- name    : AffineBernstein
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:31:59.875121+00:00
-- url     : https://prove2.me/theorems/591e6c43-a7ed-4d91-a0c8-5cd18a75d6bf
-- statement:
--   For each nonnegative integer n, Space(n) is real Euclidean n-space, with coordinate vectors eᵢ. For a real-valued function u on this space, its coordinate Hessian H(u,x) has entry D( y ↦ Du(y)eⱼ )(x)eᵢ, its cofactor Hessian is det(H)H⁻¹, and its affine weight is w(x)=det(H(u,x))^{−(n+1)/(n+2)}, using the real power operation. AffineMaximalOn(Ω,u) is the proposition that ∑ᵢ∑ⱼ det(H(u,x))(H(u,x)⁻¹)ᵢⱼ H(w,x)ᵢⱼ=0 at every x∈Ω. The length of a path γ over [0,1] is the extended nonnegative integral of √(‖γ′(t)‖²+(Du(γ(t))γ′(t))²), where the path derivative is taken within [0,1]. The intrinsic extended distance between x and y is the infimum of these lengths over C¹ paths staying in Ω and joining x to y; if no such path exists, the distance is infinite. EuclideanGraphComplete(Ω,u) means that every sequence in Ω that is Cauchy for this intrinsic distance converges in that distance to a point of Ω. This is completeness for the metric induced by the Euclidean graph embedding, with no growth condition or affine-metric completeness requirement. The graph is {(x,u(x)):x∈Ω}, and the standard paraboloid is {(x,∑ᵢxᵢ²):x∈Space(n)}. These definitions themselves impose no smoothness or convexity assumptions on u.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/AffineBernstein.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/AffineBernstein.lean; bytes 16..3217
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

namespace AffineBernstein

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def coordinateVector (n : ℕ) (i : Fin n) : Space n :=
  EuclideanSpace.single i 1

/-- Coordinate Hessian. On the open domain it depends only on the restriction of `u`.
The order of the two differentiations is immaterial under the smoothness hypothesis. -/
def hessian {n : ℕ} (u : Space n → ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ (fun y => fderiv ℝ u y (coordinateVector n j)) x
    (coordinateVector n i)

/-- The coefficient U^{ij} = det(D²u) (D²u)^{-1}_{ij}. -/
def cofactorHessian {n : ℕ} (u : Space n → ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ :=
  (hessian u x).det • (hessian u x)⁻¹

/-- The classical determinant weight; in particular, this is not a generalized exponent. -/
def affineWeight {n : ℕ} (u : Space n → ℝ) (x : Space n) : ℝ :=
  Real.rpow (hessian u x).det (-(((n : ℝ) + 1) / ((n : ℝ) + 2)))

def AffineMaximalOn {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ) : Prop :=
  ∀ x ∈ Ω, ∑ i : Fin n, ∑ j : Fin n,
    cofactorHessian u x i j * hessian (affineWeight u) x i j = 0

/-- Length on [0,1] for g_x(v,v) = ‖v‖² + (Du_x v)², the metric induced
by the Euclidean graph embedding x ↦ (x,u(x)). The product norm on Lean's ordinary
product type is NOT used (it would be the maximum norm). -/
def graphPathLength {n : ℕ} (u : Space n → ℝ) (γ : ℝ → Space n) : ℝ≥0∞ :=
  ∫⁻ t in Icc (0 : ℝ) 1,
    ENNReal.ofReal (Real.sqrt
      (‖derivWithin γ (Icc (0 : ℝ) 1) t‖ ^ 2 +
       (fderiv ℝ u (γ t) (derivWithin γ (Icc (0 : ℝ) 1) t)) ^ 2))

/-- The intrinsic extended distance: infimum of lengths of C¹ paths in the domain.
Using a single C¹ path gives the same intrinsic distance as piecewise C¹ paths,
by smooth endpoint reparameterization and concatenation. -/
def graphEDist {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (x y : Space n) : ℝ≥0∞ :=
  ⨅ (γ : ℝ → Space n)
    (_ : ContDiffOn ℝ 1 γ (Icc (0 : ℝ) 1))
    (_ : MapsTo γ (Icc (0 : ℝ) 1) Ω)
    (_ : γ 0 = x) (_ : γ 1 = y), graphPathLength u γ

/-- Sequential completeness for the induced Euclidean path metric. This states
that every intrinsic Cauchy sequence of points in Ω has an intrinsic limit in Ω.
It imposes no growth condition and no completeness condition on the affine metric. -/
def EuclideanGraphComplete {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ) : Prop :=
  ∀ x : ℕ → Space n, (∀ i, x i ∈ Ω) →
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      graphEDist Ω u (x i) (x j) < ENNReal.ofReal ε) →
    ∃ a ∈ Ω, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N,
      graphEDist Ω u (x i) a < ENNReal.ofReal ε

/-- The graph, regarded as an affine subset of R^{n+1}. -/
def graph {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ) : Set (Space n × ℝ) :=
  {p | p.1 ∈ Ω ∧ p.2 = u p.1}

def standardParaboloid (n : ℕ) : Set (Space n × ℝ) :=
  {p | p.2 = ∑ i : Fin n, (p.1 i) ^ 2}



end AffineBernstein
end
end OAI


