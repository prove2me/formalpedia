-- Prove2me | Definitions.Def_AubinLipschitz_matrixProcess
-- name    : AubinLipschitz_matrixProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:53:31.032408+00:00
-- url     : https://prove2.me/theorems/6413afe1-5f77-404e-865c-ca14a9685714
-- title:
--   §5, Theorem 1 — the matrix of generalized second derivatives
-- statement:
--   For proper convex $U$, $V$, a linear operator $A_0:X\to Y$, and $(p_0,y_0,x_0,q_0)$, this is the process from $X\times Y^*$ to $X^*\times Y$ given by the matrix
--
--   $$
--   \begin{pmatrix}\partial^2U(x_0,p_0-A_0^*q_0) & A_0^*\\[2pt] -A_0 & \big(\partial^2V(A_0x_0+y_0,q_0)\big)^{-1}\end{pmatrix}.
--   $$
--
--   It is the linearization of the optimality system at $(x_0,q_0)$, and its surjectivity is the sole regularity hypothesis of the goal.
--
--   **Formalization Note** The paper prints $Ax_0$ in this matrix on p.32. Its (11)–(12), p.33, and Corollary 1, p.35, have $A_0x_0$, which is what the base point must be.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, Theorem 1, p.32

import Mathlib
import Definitions.Def_AubinLipschitz_blockProcess
import Definitions.Def_AubinLipschitz_invMap
import Definitions.Def_AubinLipschitz_secondDeriv

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, Theorem 1, p.32: the process
`[[∂²U(x₀, p₀ − A₀*q₀), A₀*], [−A₀, (∂²V(A₀x₀ + y₀, q₀))⁻¹]]`, from `X × Y*` to `X* × Y`.

**Formalization Note** The paper prints `Ax₀` for `A₀x₀` here (p.32, twice); its own (11)–(12),
p.33, and Corollary 1, p.35, have `A₀x₀`. -/
def matrixProcess {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : X → EReal) (V : Y → EReal) (A₀ : X →L[ℝ] Y)
    (p₀ : StrongDual ℝ X) (y₀ : Y) (x₀ : X) (q₀ : StrongDual ℝ Y) :
    X × StrongDual ℝ Y → Set (StrongDual ℝ X × Y) :=
  blockProcess (secondDeriv U x₀ (p₀ - q₀.comp A₀)) A₀ (invMap (secondDeriv V (A₀ x₀ + y₀) q₀))

end AubinLipschitz


