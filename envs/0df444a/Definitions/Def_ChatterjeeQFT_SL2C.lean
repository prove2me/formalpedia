-- Prove2me | Definitions.Def_ChatterjeeQFT_SL2C
-- name    : ChatterjeeQFT_SL2C
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-19T20:43:47.282274+00:00
-- url     : https://prove2.me/theorems/96939a01-f795-4316-892e-f9a4eb84d6e1
-- title:
--   $SL(2,\mathbb{C})$, the covering map $\kappa$ onto $SO^{\uparrow}(1,3)$, and pure boosts $V_p$
-- statement:
--   To each four-vector $x$ one attaches the $2 \times 2$ complex Hermitian matrix
--
--   $$M(x) \;=\; \begin{pmatrix} x^0 + x^3 & x^1 - i x^2 \\ x^1 + i x^2 & x^0 - x^3 \end{pmatrix},$$
--
--   a bijection between $\mathbb{R}^{1,3}$ and the Hermitian $2\times2$ matrices, under which
--   $\det M(x) = (x,x)$. For $A \in SL(2,\mathbb{C})$ the matrix $A M(x) A^{\dagger}$ is again
--   Hermitian, and $\kappa(A)$ is the induced transformation of $\mathbb{R}^{1,3}$, characterised by
--   $M(\kappa(A)x) = A M(x) A^{\dagger}$; the inverse map $H \mapsto$ (four-vector) is written out
--   explicitly so that $\kappa$ is a total function.
--
--   Writing $p^* = (m,0,0,0)$ for the rest four-momentum, the **pure boost** $V_p$ is the
--   positive-definite element of $SL(2,\mathbb{C})$ with $\kappa(V_p)p^* = p$. It is the
--   positive-definite square root of $M(p)/m$, and since $M(p)/m$ has determinant $1$ and trace
--   $2p^0/m$, the Cayley-Hamilton identity gives the closed formula
--
--   $$V_p \;=\; \frac{M(p)/m + I}{\sqrt{2 + 2p^0/m}},$$
--
--   which is the definition adopted here.
-- source:
--   S. Chatterjee, *Lectures on Quantum Field Theory* (Stanford, 2018-19, combined scribed lecture notes), https://souravchatterjee.su.domains/qft-lectures-combined.pdf, Lecture 25 (The model for free electrons), §25.2-§25.3, pp. 107-109.

import Mathlib
import Definitions.Def_ChatterjeeQFT_Minkowski

/-!
# `SL(2,C)`, the covering map onto the restricted Lorentz group, and pure boosts

Following S. Chatterjee, *Lectures on Quantum Field Theory*, Lecture 25.
-/

namespace ChatterjeeQFT

open Matrix

/-- The Hermitian matrix attached to a four-vector,
`M(x) = [[x⁰ + x³, x¹ - i x²], [x¹ + i x², x⁰ - x³]]`. -/
def hermOfVec (x : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x 0 : ℂ) + (x 3 : ℂ), (x 1 : ℂ) - Complex.I * (x 2 : ℂ);
     (x 1 : ℂ) + Complex.I * (x 2 : ℂ), (x 0 : ℂ) - (x 3 : ℂ)]

/-- The four-vector attached to a `2 × 2` complex matrix; it inverts `hermOfVec` on Hermitian
matrices. -/
noncomputable def vecOfHerm (H : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℝ :=
  ![((H 0 0 + H 1 1) / 2).re, ((H 0 1 + H 1 0) / 2).re,
    ((H 1 0 - H 0 1) / (2 * Complex.I)).re, ((H 0 0 - H 1 1) / 2).re]

/-- The action `κ(A)` of `A ∈ SL(2,C)` on `R^{1,3}`, determined by `M(κ(A)x) = A M(x) A†`. -/
noncomputable def kappa (A : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  vecOfHerm (A * hermOfVec x * Aᴴ)

/-- The rest four-momentum `p* = (m, 0, 0, 0)`. -/
def restMomentum (m : ℝ) : Fin 4 → ℝ := ![m, 0, 0, 0]

/-- The pure boost `V_p ∈ SL(2,C)` taking `p*` to `p`: the positive-definite square root of
`M(p)/m`, given explicitly by `V_p = (M(p)/m + I) / √(2 + 2p⁰/m)`. -/
noncomputable def pureBoost (m : ℝ) (p : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt (2 + 2 * p 0 / m) : ℝ) : ℂ)⁻¹ • ((m : ℂ)⁻¹ • hermOfVec p + 1)

end ChatterjeeQFT


