-- Prove2me | Definitions.Def_BertsekasRiccatiMap
-- name    : BertsekasRiccatiMap
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-08T00:36:28.4059+00:00
-- url     : https://prove2.me/theorems/d32cdfce-96e5-42bb-a81e-a58831118d83
-- title:
--   The Riccati operator, controllability, and observability
-- statement:
--   This module fixes the discrete-time Riccati operator of Bertsekas, Vol. I, §4.1, together with the controllability and observability notions of Definition 4.1.1.
--
--   **The Riccati operator.** For matrices $A \in \mathbb{R}^{n\times n}$, $B \in \mathbb{R}^{n\times m}$, $Q \in \mathbb{R}^{n\times n}$ and $R \in \mathbb{R}^{m\times m}$, one step of the discrete-time Riccati equation (Eq. (4.8), with time reversed so that iteration moves forward) sends a matrix $P$ to
--
--   $$F(P) \;=\; A^{\top}\Bigl(P - P B \bigl(B^{\top} P B + R\bigr)^{-1} B^{\top} P\Bigr) A \;+\; Q .$$
--
--   A fixed point of $F$ is a solution of the algebraic Riccati equation.
--
--   **Controllability.** The pair $(A,B)$ is controllable when the $n \times nm$ controllability matrix has full row rank:
--
--   $$\operatorname{rank}\bigl[\, B, \; AB, \; A^2 B, \; \dots, \; A^{n-1} B \,\bigr] \;=\; n .$$
--
--   Equivalently, any state can be steered to the origin in at most $n$ steps.
--
--   **Observability.** The pair $(A,C)$, with $C \in \mathbb{R}^{q \times n}$, is observable when $(A^{\top}, C^{\top})$ is controllable — the definition the source adopts. Its meaning is that the initial state can be inferred from the outputs $Cx_k$ in the absence of control.
--
--   These three notions are exactly what the asymptotic theory of the linear-quadratic regulator is stated in terms of: controllability bounds the Riccati iterates from above, observability makes the limit positive definite, and the operator itself carries the iteration.
--
--   **Formalization Note** The matrix inverse is Mathlib's total inverse, which returns the zero matrix on a singular argument; under the hypotheses of the asymptotic theorem $B^{\top} P B + R$ is positive definite along the relevant iterates, so the formula is the intended one there. The controllability matrix is indexed by pairs (power, column), which is the block matrix $[B, AB, \dots, A^{n-1}B]$ up to a permutation of columns — irrelevant to its rank.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 4.1, Eq. (4.8); D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Definition 4.1.1

import Mathlib

open Matrix

/-- One step of the discrete-time Riccati equation of Bertsekas, "Dynamic
Programming and Optimal Control", Vol. I, 3rd ed., Section 4.1 (Eq. (4.8),
time-reversed indexing):
`P ↦ Aᵀ (P - P B (Bᵀ P B + R)⁻¹ Bᵀ P) A + Q`. -/
noncomputable def BertsekasRiccatiMap {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Aᵀ * (P - P * B * (Bᵀ * P * B + R)⁻¹ * Bᵀ * P) * A + Q

/-- Definition 4.1.1 of Bertsekas, Vol. I, 3rd ed.: the pair `(A, B)`, with `A`
an `n × n` matrix and `B` an `n × m` matrix, is controllable if the `n × nm`
controllability matrix `[B, AB, A²B, …, A^{n-1}B]` has full rank `n`. -/
noncomputable def BertsekasControllablePair {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  (Matrix.of fun (i : Fin n) (p : Fin n × Fin m) =>
    (A ^ (p.1 : ℕ) * B) i p.2).rank = n

/-- Definition 4.1.1 of Bertsekas, Vol. I, 3rd ed.: the pair `(A, C)`, with `A`
an `n × n` matrix and `C` a `q × n` matrix, is observable if the pair
`(Aᵀ, Cᵀ)` is controllable. -/
noncomputable def BertsekasObservablePair {n q : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin q) (Fin n) ℝ) : Prop :=
  BertsekasControllablePair Aᵀ Cᵀ


