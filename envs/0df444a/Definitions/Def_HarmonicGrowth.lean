-- Prove2me | Definitions.Def_HarmonicGrowth
-- name    : HarmonicGrowth
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:13.838493+00:00
-- url     : https://prove2.me/theorems/0882fe49-8def-41bd-bb2e-e56141a34247
-- statement:
--   A smooth Riemannian metric on R^n is given by a coefficient matrix field g(x) whose entries are C^∞ and which is positive definite at every point; Christoffel symbols, the Ricci tensor (with the convention that the round sphere has positive Ricci curvature), and the Laplace-Beltrami operator Δ_g u (the g-trace of the covariant Hessian) are written out explicitly in the single global Cartesian chart. RicciNonnegative means Ric_g(x)(v,v) ≥ 0 for all x and v. The intrinsic distance d_g(x,y) is the infimum of lengths ∫_0^1 sqrt(g(γ)(γ',γ')) dt over C^1 paths from x to y, and Complete means every d_g-Cauchy sequence converges in d_g to a point of R^n. EuclideanNearOrigin means g is the identity matrix on some Euclidean ball around the origin. ballVolume(g,R) is the Riemannian measure, valued in [0,∞], of the d_g-ball of radius R about 0, and omega(n) is the Euclidean unit-ball volume. PositiveSubunitAVR means ballVolume(g,R)/(omega(n) R^n) tends as R→∞ to some a with 0<a<1. HarmonicGrowth(g,k,u) says u is C^∞, Δ_g u = 0 everywhere, and there is C ≥ 0 with |u(x)| ≤ C(1+d_g(0,x))^k for all x. euclideanDimension(n,k) is C(n+k-1,k)+C(n+k-2,k-1). MainClaim is a defined proposition, not a proved theorem, asserting that there exist n, k and a smooth metric g on R^n with n even, n ≥ 8, k ≥ 2, such that g is complete, has nonnegative Ricci curvature, is Euclidean near the origin, has positive sub-unit asymptotic volume ratio, and admits euclideanDimension(n,k)+1 linearly independent harmonic functions of growth at most k. The source then assumes MainClaim as an axiom, mainStatement, and restates it as the theorem main.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HarmonicGrowth.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HarmonicGrowth.lean; bytes 16..4511
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff

namespace HarmonicCounterexample

abbrev Space (n : ℕ) := Fin n → ℝ
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- A genuine smooth positive definite covariant metric tensor on R^n. -/
structure SmoothMetric (n : ℕ) where
  coeff : Space n → Mat n
  smooth : ∀ i j, ContDiff ℝ ∞ (fun x => coeff x i j)
  positive : ∀ x, (coeff x).PosDef

/-- The coordinate directional derivative. -/
def coordDeriv {n : ℕ} (i : Fin n) (f : Space n → ℝ) (x : Space n) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- Levi-Civita connection in the single global Cartesian chart. -/
def christoffel {n : ℕ} (g : SmoothMetric n) (x : Space n)
    (k i j : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ l, (g.coeff x)⁻¹ k l *
    (coordDeriv i (fun y => g.coeff y j l) x +
     coordDeriv j (fun y => g.coeff y i l) x -
     coordDeriv l (fun y => g.coeff y i j) x)

/-- Ricci tensor, with the convention in which the round sphere has positive Ricci. -/
def ricci {n : ℕ} (g : SmoothMetric n) (x : Space n) (i j : Fin n) : ℝ :=
  (∑ k, (coordDeriv k (fun y => christoffel g y k i j) x -
    coordDeriv j (fun y => christoffel g y k i k) x)) +
  ∑ k, ∑ l, (christoffel g x k i j * christoffel g x l k l -
    christoffel g x l i k * christoffel g x k j l)

def RicciNonnegative {n : ℕ} (g : SmoothMetric n) : Prop :=
  ∀ (x v : Space n), 0 ≤ ∑ i, ∑ j, ricci g x i j * v i * v j

/-- Trace of the covariant Hessian, i.e. the Laplace-Beltrami operator. -/
def laplaceBeltrami {n : ℕ} (g : SmoothMetric n) (u : Space n → ℝ)
    (x : Space n) : ℝ :=
  ∑ i, ∑ j, (g.coeff x)⁻¹ i j *
    (coordDeriv i (coordDeriv j u) x - ∑ k, christoffel g x k i j * coordDeriv k u x)

/-- Riemannian length of a path on the unit parameter interval. -/
def pathLength {n : ℕ} (g : SmoothMetric n) (γ : ℝ → Space n) : ℝ :=
  ∫ t in (0 : ℝ)..1, Real.sqrt
    (∑ i, ∑ j, g.coeff (γ t) i j * deriv γ t i * deriv γ t j)

/-- Infimum of smooth path lengths, the intrinsic Riemannian distance. -/
def distance {n : ℕ} (g : SmoothMetric n) (x y : Space n) : ℝ :=
  sInf {L : ℝ | ∃ γ : ℝ → Space n,
    ContDiff ℝ 1 γ ∧ γ 0 = x ∧ γ 1 = y ∧ L = pathLength g γ}

/-- Sequential metric completeness, for the intrinsic distance, not the background one. -/
def Complete {n : ℕ} (g : SmoothMetric n) : Prop :=
  ∀ z : ℕ → Space n,
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N, distance g (z p) (z q) < ε) →
    ∃ x : Space n, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, distance g (z p) x < ε

def EuclideanNearOrigin {n : ℕ} (g : SmoothMetric n) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ x : Space n, (∑ i, x i ^ 2) < ε ^ 2 → g.coeff x = 1

/-- Riemannian measure of the intrinsic open ball, retaining infinite values. -/
def ballVolume {n : ℕ} (g : SmoothMetric n) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in {x : Space n | distance g 0 x < R},
    ENNReal.ofReal (Real.sqrt (g.coeff x).det) ∂volume

/-- The ordinary Euclidean unit ball volume, in Cartesian Lebesgue measure. -/
def omega (n : ℕ) : ℝ≥0∞ :=
  volume {x : Space n | (∑ i, x i ^ 2) < 1}

/-- The volume-ratio limit is finite, positive, and strictly below one. -/
def PositiveSubunitAVR {n : ℕ} (g : SmoothMetric n) : Prop :=
  ∃ a : ℝ, 0 < a ∧ a < 1 ∧
    Tendsto (fun R : ℝ => ballVolume g R / (omega n * ENNReal.ofReal (R ^ n)))
      atTop (𝓝 (ENNReal.ofReal a))

/-- Membership in the actual space H_k, with the bound required at every point. -/
def HarmonicGrowth {n : ℕ} (g : SmoothMetric n) (k : ℕ) (u : Space n → ℝ) : Prop :=
  ContDiff ℝ ∞ u ∧ (∀ x, laplaceBeltrami g u x = 0) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |u x| ≤ C * (1 + distance g 0 x) ^ k


def euclideanDimension (n k : ℕ) : ℕ :=
  (n + k - 1).choose k + (n + k - 2).choose (k - 1)

/-- The manuscript's unconditional main existence claim. -/
def MainClaim : Prop :=
  ∃ (n k : ℕ) (g : SmoothMetric n), Even n ∧ 8 ≤ n ∧ 2 ≤ k ∧
    Complete g ∧ RicciNonnegative g ∧ EuclideanNearOrigin g ∧ PositiveSubunitAVR g ∧
    ∃ u : Fin (euclideanDimension n k + 1) → (Space n → ℝ),
      LinearIndependent ℝ u ∧ ∀ i, HarmonicGrowth g k (u i)



axiom mainStatement : MainClaim

theorem main : MainClaim := mainStatement

end HarmonicCounterexample

end

end OAI


