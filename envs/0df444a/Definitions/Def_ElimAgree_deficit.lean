-- Prove2me | Definitions.Def_ElimAgree_deficit
-- name    : ElimAgree_deficit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:15:29.812688+00:00
-- url     : https://prove2.me/theorems/3b908017-af84-469d-913c-6cc9e102da9e
-- title:
--   Logarithmic deficit $J_\lambda(R)$ of a rectangle
-- statement:
--   Let $\lambda$ be a law on $\alpha\times\beta$ with one-party marginals $\lambda_X(A)=\sum_{x\in A}\sum_y\lambda(x,y)$ and $\lambda_Y(B)=\sum_{y\in B}\sum_x\lambda(x,y)$. For a rectangle $R=A\times B$,
--   $$J_\lambda(R)=\lambda(R)\,\ln\frac{\sqrt{\lambda_X(A)\,\lambda_Y(B)}}{\lambda(R)},$$
--   with value $0$ when $\lambda(R)=0$. It is nonnegative, because $\lambda(R)\le\min\{\lambda_X(A),\lambda_Y(B)\}$.
--
--   The deficit measures how far a rectangle's mass falls below the geometric mean of its marginals; hypothesis (3.1) of Theorem 3.1 is phrased with it.
--
--   **Formalization Note** The zero case is written explicitly. The marginals are those of $\lambda$ itself, not of a product law.
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), §3.1, p.7 (PDF p.9)

import Mathlib

namespace ElimAgree

variable {α β : Type} [Fintype α] [Fintype β]

/-- The mass `λ(A × B)` of a rectangle under a law `λ` on `α × β`. -/
def lawRect (lam : α × β → ℝ) (A : Finset α) (B : Finset β) : ℝ :=
  ∑ x ∈ A, ∑ y ∈ B, lam (x, y)

/-- Alice's marginal `λ_X(A) = Σ_{x ∈ A} Σ_y λ(x, y)`. -/
def margX (lam : α × β → ℝ) (A : Finset α) : ℝ :=
  ∑ x ∈ A, ∑ y, lam (x, y)

/-- Bob's marginal `λ_Y(B) = Σ_{y ∈ B} Σ_x λ(x, y)`. -/
def margY (lam : α × β → ℝ) (B : Finset β) : ℝ :=
  ∑ y ∈ B, ∑ x, lam (x, y)

/-- The logarithmic deficit of a rectangle (Ben Daniel, *Can Many Instances Be Cheaper Than One?
The Price of Agreement in Elimination*, manuscript, STOC 2027 submission, §3.1, p.7):
`J_λ(R) = λ(R) ln( √(λ_X(A) λ_Y(B)) / λ(R) )` for `R = A × B`, with value `0` when `λ(R) = 0`.
The marginals are `λ`'s own marginals. -/
noncomputable def deficit (lam : α × β → ℝ) (A : Finset α) (B : Finset β) : ℝ :=
  if lawRect lam A B = 0 then 0
  else lawRect lam A B *
    Real.log (Real.sqrt (margX lam A * margY lam B) / lawRect lam A B)

end ElimAgree


