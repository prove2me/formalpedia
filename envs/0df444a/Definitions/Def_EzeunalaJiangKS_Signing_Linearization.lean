-- Prove2me | Definitions.Def_EzeunalaJiangKS_Signing_Linearization
-- name    : EzeunalaJiangKS_Signing_Linearization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T01:04:15.825988+00:00
-- url     : https://prove2.me/theorems/2a55fcab-8ff7-4cf2-a7a5-d789f7d8a962
-- title:
--   Constraint linearization, feedback, and Frobenius geometry
-- statement:
--   For pairs of Hermitian matrices define
--   $$L(U,V)=(X^{-1}UX^{-1}-\eta_x(V),Y^{-1}VY^{-1}-\eta_x(U)),\quad\mathcal T(U,V)=(X\eta_x(V)X,Y\eta_x(U)Y).$$
--   The chosen inverse solves the actual equation $L(Z)=F$ among Hermitian pairs when such a solution exists, and otherwise is zero. The pair Frobenius norm is the square root of the sum of squared absolute values of all entries of both matrices.
--
--   Invertibility and quantitative bounds are not encoded as assumptions. Infinite series use actual convergence in the finite-dimensional matrix topology, which agrees with the Frobenius topology. The matrix discrepancy norm remains the separate Euclidean operator norm.
-- source:
--   Ekene Ezeunala, Haotian Jiang, STOC 2027 submission #1226 (October 2026), §4.1, (12) and Claim 4.1, printed p. 9 (PDF p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1226.pdf

import Definitions.Def_EzeunalaJiangKS_Signing_Dual

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace EzeunalaJiangKS.Signing

attribute [local instance] Classical.propDecidable

def hermitianPair {d : ℕ} (Z : PairMat d) : Prop := Z.1.IsHermitian ∧ Z.2.IsHermitian
def positivePair {d : ℕ} (Z : PairMat d) : Prop := Z.1.PosSemidef ∧ Z.2.PosSemidef

def linearized {N d : ℕ} (A : Fin N → CMat d) (x : State N) (X Y : CMat d)
    (Z : PairMat d) : PairMat d :=
  (X⁻¹ * Z.1 * X⁻¹ - eta A x Z.2, Y⁻¹ * Z.2 * Y⁻¹ - eta A x Z.1)

def feedback {N d : ℕ} (A : Fin N → CMat d) (x : State N) (X Y : CMat d)
    (Z : PairMat d) : PairMat d := (X * eta A x Z.2 * X, Y * eta A x Z.1 * Y)

/-- Actual inverse equation, with zero junk value when no Hermitian solution exists. -/
def linearizedInverse {N d : ℕ} (A : Fin N → CMat d) (x : State N) (X Y : CMat d)
    (F : PairMat d) : PairMat d :=
  if h : ∃ Z, hermitianPair Z ∧ linearized A x X Y Z = F then Classical.choose h else (0, 0)

def frobeniusPair {d : ℕ} (Z : PairMat d) : ℝ :=
  Real.sqrt ((∑ i, ∑ j, ‖Z.1 i j‖^2) + ∑ i, ∑ j, ‖Z.2 i j‖^2)

end EzeunalaJiangKS.Signing


