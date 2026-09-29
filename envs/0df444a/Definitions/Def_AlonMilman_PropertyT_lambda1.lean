-- Prove2me | Definitions.Def_AlonMilman_PropertyT_lambda1
-- name    : AlonMilman_PropertyT_lambda1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:29:23.653844+00:00
-- url     : https://prove2.me/theorems/5ca24deb-692b-449a-9706-816135865fa0
-- title:
--   λ₁ of a real symmetric matrix: its second-smallest eigenvalue, counted with multiplicity
-- statement:
--   Let $Q$ be a real symmetric $n \times n$ matrix whose rows and columns are indexed by a finite set $V$ with $n = |V| \ge 2$. List its eigenvalues in increasing order, each repeated according to its multiplicity:
--
--   $$\lambda_0 \le \lambda_1 \le \lambda_2 \le \cdots \le \lambda_{n-1}.$$
--
--   The quantity $\lambda_1(Q)$ is the second entry of this list, that is, the second-smallest eigenvalue of $Q$ counted with multiplicity.
--
--   For the matrix $Q = Q_G$ of a graph $G$, Alon and Milman write the spectrum as $0 = \lambda_0 < \lambda_1 = \lambda_1(G) \le \lambda_2 \le \cdots \le \lambda_{n-1}$, and $\lambda_1(G)$ is the algebraic connectivity of $G$ that the whole paper is about. This definition supplies that number for every graph matrix used in the mission.
--
--   **Formalization Note** Lean's `Matrix.IsHermitian.eigenvalues₀` lists the eigenvalues of a Hermitian matrix in decreasing order, so $\lambda_1$ is the entry with index $n-2$. When $Q$ is not symmetric or $n < 2$ the definition returns the placeholder value $0$; every statement of the mission applies it only to symmetric matrices with $n \ge 2$.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 76, Section 2 (eigenvalues of Q)

import Mathlib

namespace AlonMilman.PropertyT

open Classical in
/-- `λ₁(Q)`: the second-smallest eigenvalue, counted with multiplicity, of a real symmetric
matrix `Q` indexed by a finite type with at least two elements (Alon–Milman 1985, p. 76:
"Let 0 = λ₀ < λ₁ = λ₁(G) ≤ λ₂ ≤ ··· ≤ λ_{n−1} be the eigenvalues of Q, each appearing in
accordance with its multiplicity").  Mathlib's `eigenvalues₀` lists the eigenvalues in
decreasing order, so the second-smallest one has index `card − 2`.  Junk value: `0` when `Q`
is not symmetric or when the index type has fewer than two elements. -/
noncomputable def lambda1 {n : Type} [Fintype n] [DecidableEq n] (Q : Matrix n n ℝ) : ℝ :=
  if h : Q.IsHermitian ∧ 2 ≤ Fintype.card n then
    h.1.eigenvalues₀ ⟨Fintype.card n - 2, by have := h.2; omega⟩
  else 0

end AlonMilman.PropertyT


