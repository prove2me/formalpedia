-- Prove2me | Definitions.Def_ConjGrad_Termination_IsCDRun
-- name    : ConjGrad_Termination_IsCDRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:47:50.959289+00:00
-- url     : https://prove2.me/theorems/127089b9-be24-4a26-8ea6-867ba4599b04
-- title:
--   A run of the method of conjugate directions (cd-method), eq. (4:1)–(4:2)
-- statement:
--   Let $A$ be a real $n \times n$ matrix and $k \in \mathbb{R}^n$. The **method of conjugate directions** (cd-method) of Hestenes and Stiefel selects an initial estimate $x_0$ and an arbitrary initial direction $p_0$, and then repeatedly updates the estimate along the current direction and chooses a new direction conjugate to all earlier ones. Because the directions are chosen freely, the method is described by a property of sequences rather than by a formula.
--
--   Sequences of estimates $x_0, x_1, \dots$, residuals $r_0, r_1, \dots$ and directions $p_0, p_1, \dots$ in $\mathbb{R}^n$ form a **run of the cd-method** for the system $Ax = k$ when, for all $i \ge 0$:
--
--   1. $r_i = k - Ax_i$ is the residual of $x_i$;
--   2. the estimate is updated by (4:1a)–(4:1b):
--   $$a_i = \frac{(p_i, r_i)}{(p_i, Ap_i)}, \qquad x_{i+1} = x_i + a_i p_i;$$
--   3. the next direction is conjugate to all previous ones, (4:2):
--   $$(p_{i+1}, Ap_j) = 0 \qquad (j = 0, 1, \dots, i).$$
--
--   The update (4:1c), $r_{i+1} = r_i - a_i A p_i$, follows from 1 and 2. The cg-method is one run of this kind; the Gauss elimination method is another (Section 12 of the paper).
--
--   **Formalization Note** Vectors are `Fin n → ℝ`, indices 0-based, and the sequences are infinite (`ℕ → Fin n → ℝ`). A run that the paper stops after finitely many steps extends to an infinite run by zero directions, since $a_i = 0$ when $p_i = 0$ (Lean's division by zero). No nonzero condition is placed on the directions here; the theorems that need one state it.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), https://doi.org/10.6028/jres.049.044, p. 412, Section 4, initial step, general routine, eq. (4:1a)–(4:1c) and (4:2)

import Mathlib

open Matrix

namespace ConjGrad.Termination

/-- A run of the method of conjugate directions (cd-method) of Hestenes–Stiefel 1952, §4,
p. 412, for the system `Ax = k`: sequences of estimates `x i`, residuals `r i` and directions
`p i` (indices 0-based) such that
* every residual is the residual of its estimate, `rᵢ = k − Axᵢ` (the initial step and the
  paper's "the residual rᵢ = k − Axᵢ"; (4:1c) follows);
* the estimate is updated by (4:1a)–(4:1b): `xᵢ₊₁ = xᵢ + aᵢpᵢ` with `aᵢ = (pᵢ,rᵢ)/(pᵢ,Apᵢ)`;
* each new direction is conjugate to all previous ones, (4:2): `(pᵢ₊₁, Apⱼ) = 0` for
  `j = 0, …, i`.
The initial direction `p₀` is arbitrary, as in the paper. -/
structure IsCDRun {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n → ℝ)
    (x r p : ℕ → Fin n → ℝ) : Prop where
  /-- `rᵢ = k − Axᵢ` -/
  residual : ∀ i, r i = k - A *ᵥ x i
  /-- (4:1a), (4:1b) -/
  step : ∀ i, x (i + 1) = x i + ((p i ⬝ᵥ r i) / (p i ⬝ᵥ (A *ᵥ p i))) • p i
  /-- (4:2) -/
  conj : ∀ i, ∀ j ≤ i, p (i + 1) ⬝ᵥ (A *ᵥ p j) = 0

end ConjGrad.Termination


