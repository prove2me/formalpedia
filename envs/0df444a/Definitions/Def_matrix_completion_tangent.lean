-- Prove2me | Definitions.Def_matrix_completion_tangent
-- name    : matrix_completion_tangent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-13T22:55:42.18555+00:00
-- url     : https://prove2.me/theorems/8d07fe89-f8db-4a46-9854-fc6cf2752eec
-- statement:
--   This definition module provides tangent-space sampling, centered sampling fluctuations, operator norms, entry/Frobenius norms, and deterministic events used in the concentration arguments.
--
--   $$
--   P_T,\ P_{T^\perp},\ P_\Omega,\qquad
--   p^{-1}P_TP_\Omega P_T-P_T.
--   $$
--
--   Module overview: Tangent-space and certificate interfaces for the deterministic recovery lemma. The paper's tangent space is $T = {u x^\top + y v^\top}$, where $u$ and $v$ range through the singular vector spans of $M$. We expose the concrete coordinate projection used in Section 3, plus the sampling projection and the strict dual-certificate predicate.
--
--   Documented declarations:
--   1. Left multiplication by the orthogonal projector onto the column singular space of $S$.
--   2. Right multiplication by the orthogonal projector onto the row singular space of $S$.
--   3. The two-sided projection through both singular spaces.
--   4. Orthogonal projection $P_{T}$ onto the tangent space at $M$.
--   5. Orthogonal projection $P_{T^\perp}$ onto the normal space.
--   6. Spectral/operator norm of a real matrix acting between Euclidean spaces.
--   7. Maximum absolute entry of a matrix.
--   8. Coordinate matrix with a single $1$ in entry $(i,j)$ and zero elsewhere.
--
--   Role in the mission. Key declarations include leftSingularProjection, rightSingularProjection, twoSidedSingularProjection, tangentProjection, normalProjection, spectralNorm, entrySupNorm, coordinateMatrix, matrixInner, frobeniusNormSq, frobeniusNorm, samplingProjection, centeredSamplingFluctuation, CenteredSamplingSpectralBound, sampledRowEnergyMax, sampledColumnEnergyMax, VanishesOutside, SamplingOperatorInjectiveOnT, among others. These definitions provide shared vocabulary for the Exact Matrix Completion decomposition, so theorem statements can refer to sampling models, recovery events, tangent-space geometry, and concentration estimates without restating the infrastructure each time.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_bernoulli

/-!
Tangent-space and certificate interfaces for the deterministic recovery lemma.

The paper's tangent space is
`T = {u x^T + y v^T}`, where `u` and `v` range through the singular vector
spans of `M`.  We expose the concrete coordinate projection used in Section 3,
plus the sampling projection and the strict dual-certificate predicate.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Left multiplication by the orthogonal projector onto the column singular
space of `S`. -/
noncomputable def leftSingularProjection {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X : RealMatrix n1 n2) : RealMatrix n1 n2 :=
  fun i j => ∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * X a j

/-- Right multiplication by the orthogonal projector onto the row singular
space of `S`. -/
noncomputable def rightSingularProjection {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X : RealMatrix n1 n2) : RealMatrix n1 n2 :=
  fun i j => ∑ b : Fin n2, X i b * (∑ k : Fin r, S.v k b * S.v k j)

/-- The two-sided projection through both singular spaces. -/
noncomputable def twoSidedSingularProjection {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (S : SVD M r)
    (X : RealMatrix n1 n2) : RealMatrix n1 n2 :=
  fun i j =>
    ∑ a : Fin n1, ∑ b : Fin n2,
      (∑ k : Fin r, S.u k i * S.u k a) * X a b *
        (∑ l : Fin r, S.v l b * S.v l j)

/-- Orthogonal projection `P_T` onto the tangent space at `M`. -/
noncomputable def tangentProjection {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X : RealMatrix n1 n2) : RealMatrix n1 n2 :=
  leftSingularProjection S X + rightSingularProjection S X -
    twoSidedSingularProjection S X

/-- Orthogonal projection `P_{T^\perp}` onto the normal space. -/
noncomputable def normalProjection {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X : RealMatrix n1 n2) : RealMatrix n1 n2 :=
  X - tangentProjection S X

/-- Spectral/operator norm of a real matrix acting between Euclidean spaces. -/
noncomputable def spectralNorm {n1 n2 : Nat} (X : RealMatrix n1 n2) : Real :=
  ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X))‖

/-- Maximum absolute entry of a matrix. -/
noncomputable def entrySupNorm {n1 n2 : Nat} (X : RealMatrix n1 n2) : Real :=
  ⨆ i : Fin n1, ⨆ j : Fin n2, |X i j|

/-- Coordinate matrix with a single `1` in entry `(i,j)` and zero elsewhere. -/
def coordinateMatrix {n1 n2 : Nat} (i : Fin n1) (j : Fin n2) :
    RealMatrix n1 n2 :=
  fun a b => if a = i ∧ b = j then 1 else 0

/-- Frobenius inner product of two real matrices. -/
def matrixInner {n1 n2 : Nat} (X Y : RealMatrix n1 n2) : Real :=
  ∑ i : Fin n1, ∑ j : Fin n2, X i j * Y i j

/-- Squared Frobenius norm, used to state the least-squares certificate problem
without introducing square roots. -/
def frobeniusNormSq {n1 n2 : Nat} (X : RealMatrix n1 n2) : Real :=
  ∑ i : Fin n1, ∑ j : Fin n2, X i j ^ 2

/-- Frobenius norm of a matrix. -/
noncomputable def frobeniusNorm {n1 n2 : Nat} (X : RealMatrix n1 n2) : Real :=
  Real.sqrt (frobeniusNormSq X)

/-- Projection `P_Omega` that keeps observed entries and zeros unobserved ones. -/
noncomputable def samplingProjection {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (X : RealMatrix n1 n2) :
    RealMatrix n1 n2 :=
  fun i j => if (i, j) ∈ Omega then X i j else 0

/-- Centered sampling fluctuation `p^{-1}(P_Omega - p I)X`. -/
noncomputable def centeredSamplingFluctuation {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) : RealMatrix n1 n2 :=
  (p⁻¹) • (samplingProjection Omega X - p • X)

/-- Event that a centered sampling fluctuation has spectral norm at most a
given bound. -/
def CenteredSamplingSpectralBound {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) (bound : Real) : Prop :=
  spectralNorm (centeredSamplingFluctuation Omega p X) ≤ bound

/-- Maximum sampled row energy `max_i sum_j δ_ij X_ij^2`. -/
noncomputable def sampledRowEnergyMax {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (X : RealMatrix n1 n2) : Real :=
  ⨆ i : Fin n1, ∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0

/-- Maximum sampled column energy `max_j sum_i δ_ij X_ij^2`. -/
noncomputable def sampledColumnEnergyMax {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (X : RealMatrix n1 n2) : Real :=
  ⨆ j : Fin n2, ∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0

/-- `Y` vanishes on the complement of the observation set. -/
def VanishesOutside {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2))
    (Y : RealMatrix n1 n2) : Prop :=
  ∀ i j, (i, j) ∉ Omega → Y i j = 0

/-- The sampling operator is injective when restricted to the tangent space. -/
def SamplingOperatorInjectiveOnT {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) : Prop :=
  ∀ H : RealMatrix n1 n2,
    tangentProjection S H = H → samplingProjection Omega H = 0 → H = 0

/-- The tangent sampling operator `P_T P_Omega` is onto the tangent space. -/
def TangentSamplingOperatorSurjectiveOnT {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r) : Prop :=
  ∀ X : RealMatrix n1 n2,
    tangentProjection S X = X →
      ∃ Z : RealMatrix n1 n2,
        tangentProjection S Z = Z ∧
          tangentProjection S (samplingProjection Omega Z) = X

/-- Tangent-space concentration of the sampled operator around its Bernoulli
mean.  This is a pointwise Frobenius-norm form of
`p^{-1} ||P_T P_Omega P_T - p P_T|| <= epsilon`, restricted to matrices in `T`. -/
def TangentSamplingConcentration {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (p epsilon : Real) : Prop :=
  ∀ X : RealMatrix n1 n2,
    tangentProjection S X = X →
    frobeniusNorm
        (tangentProjection S (samplingProjection Omega X) - p • X) ≤
      epsilon * p * frobeniusNorm X

/-- Operator-norm size of the tangent sampling fluctuation.  This is the
quantity denoted `Z = p^{-1} ||P_T P_Omega P_T - p P_T||` in Theorem 4.2,
written as a supremum over tangent-space matrices of Frobenius norm at most 1. -/
noncomputable def tangentSamplingDeviation {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p : Real) : Real :=
  sSup {v : Real |
    ∃ X : RealMatrix n1 n2,
      tangentProjection S X = X ∧ frobeniusNorm X ≤ 1 ∧
        v = (p⁻¹) *
          frobeniusNorm
            (tangentProjection S (samplingProjection Omega X) - p • X)}

/-- Closed-form scale appearing in Theorem 4.1. -/
noncomputable def tangentSamplingDeviationScale
    (C β μ0 : Real) (n r m : Nat) : Real :=
  C * Real.sqrt
    ((μ0 * (n : Real) * (r : Real) * (β * Real.log (n : Real))) /
      (m : Real))

/-- Expectation scale before the final `β`-absorption in Theorem 4.2. -/
noncomputable def tangentSamplingExpectedDeviationScale
    (C μ0 : Real) (n r m : Nat) : Real :=
  C * Real.sqrt
    ((μ0 * (n : Real) * (r : Real) * Real.log (n : Real)) / (m : Real))

/-- Pointwise bound on the tangent sampling deviation. -/
def TangentSamplingDeviationBound {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (Omega : Finset (Fin n1 × Fin n2))
    (S : SVD M r) (p bound : Real) : Prop :=
  tangentSamplingDeviation Omega S p ≤ bound

/-- Coordinate-wise Frobenius bound for projected basis matrices
`P_T(e_i e_j^*)`. -/
def TangentCoordinateFrobeniusBound {n1 n2 r : Nat}
    {M : RealMatrix n1 n2} (S : SVD M r) (bound : Real) : Prop :=
  ∀ i j, frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ^ 2 ≤ bound

/-- Strict dual certificate from Lemma 3.1: it is supported on `Omega`, has
tangent projection equal to the sign matrix, and has normal spectral norm `< 1`. -/
def StrictDualCertificate {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (Y : RealMatrix n1 n2) : Prop :=
  VanishesOutside Omega Y ∧
    tangentProjection S Y = signMatrix S ∧
      spectralNorm (normalProjection S Y) < 1

/-- The minimum-Frobenius-norm certificate solving the affine constraint
`P_T Y = sign(M)` and supported on the observed set, matching (4.1). -/
def LeastSquaresDualCertificate {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (Omega : Finset (Fin n1 × Fin n2)) (S : SVD M r)
    (Y : RealMatrix n1 n2) : Prop :=
  VanishesOutside Omega Y ∧
    tangentProjection S Y = signMatrix S ∧
      ∀ Z : RealMatrix n1 n2,
        VanishesOutside Omega Z →
        tangentProjection S Z = signMatrix S →
        frobeniusNormSq Y ≤ frobeniusNormSq Z

end MatrixCompletion


