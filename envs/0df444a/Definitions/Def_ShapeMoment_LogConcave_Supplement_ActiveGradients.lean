-- Prove2me | Definitions.Def_ShapeMoment_LogConcave_Supplement_ActiveGradients
-- name    : ShapeMoment_LogConcave_Supplement_ActiveGradients
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:07:16.804205+00:00
-- url     : https://prove2.me/theorems/7c324e8f-6c96-45f5-92ea-00720058b9c9
-- title:
--   §3.2, p. 10 — support S(x), restricted row span L(S), gradients and the active vectors of (Rev-Cvx)
-- statement:
--   Notation used in the last paragraph of Theorem 3.6, for a point $x\in\mathbb R^n$, an $m\times n$ real matrix $A$ and differentiable functions $f_1,\dots,f_P:\mathbb R^n\to\mathbb R$.
--
--   1. **Gradient.** $\nabla g(x)\in\mathbb R^n$ is the vector of partial derivatives, $[\nabla g(x)]_j=Dg(x)(e_j)$, where $e_j$ is the $j$th unit vector.
--   2. **Support.** $S(x)=\{j\in[1,n]: x_j>0\}$.
--   3. **Restriction.** For $v\in\mathbb R^n$ and $S\subseteq[1,n]$, $[v]_S\in\mathbb R^S$ keeps the coordinates indexed by $S$.
--   4. **Restricted row span.** $A_S=[A_j]_{j\in S}$ is the submatrix of the columns indexed by $S$, and
--   $$\mathcal L(S)=\operatorname{span}\{(A_S^1)^\top,\dots,(A_S^m)^\top\}\subseteq\mathbb R^S$$
--   is the span of its rows.
--   5. **Active vectors.** $\{\nabla f_p(x): f_p(x)=0\}\cup\{e_j: x_j=0\}\subseteq\mathbb R^n$, the gradients of the tight constraints $f_p\le 0$ together with the unit vectors of the tight sign constraints $x_j\ge 0$.
--
--   These are the objects in which the "in addition" clause of Theorem 3.6 is stated.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`; the gradient is taken through the Fréchet derivative applied to the unit vectors, which is the usual gradient for any norm. The derivative of a non-differentiable function is $0$ in Lean; the theorem using these objects assumes every $f_p$ differentiable, as the source does.
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 10, notation before Theorem 3.6 (S(x), A_S, L(S), [∇f_p(x)]_S, e_j)

import Mathlib

namespace ShapeMoment.LogConcave.Supplement

/-- The gradient `∇g(x)` as the vector of partial derivatives
`(∂g/∂x_j)(x) = Dg(x)(e_j)`. -/
noncomputable def grad {n : ℕ} (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => fderiv ℝ g x (Pi.single j 1)

/-- The support `S(x) = {j : x_j > 0}`. -/
def supportSet {n : ℕ} (x : Fin n → ℝ) : Set (Fin n) := {j | 0 < x j}

/-- The restriction `[v]_S` of a vector to the coordinates in `S`. -/
def restrictTo {n : ℕ} (S : Set (Fin n)) (v : Fin n → ℝ) : S → ℝ := fun j => v j

/-- `L(S)`: the real span of the rows of `A_S`, the submatrix of `A` with the
columns indexed by `S`. -/
def rowSpanOn {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Set (Fin n)) :
    Submodule ℝ (S → ℝ) :=
  Submodule.span ℝ (Set.range fun i : Fin m => restrictTo S (A i))

/-- The vectors `{∇f_p(x) : f_p(x) = 0} ∪ {e_j : x_j = 0}` in `ℝⁿ`. -/
def activeVectors {n P : ℕ} (f : Fin P → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {v | (∃ p, f p x = 0 ∧ v = grad (f p) x) ∨
    (∃ j, x j = 0 ∧ v = Pi.single j 1)}

end ShapeMoment.LogConcave.Supplement


