-- Prove2me | Definitions.Def_BrouwerLaplacian_IsOrthProj
-- name    : BrouwerLaplacian_IsOrthProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:22.430825+00:00
-- url     : https://prove2.me/theorems/3444d1a5-4ec9-4fa5-8ab9-14a905d815e5
-- title:
--   Orthogonal projection matrix of rank $k$
-- statement:
--   A real $n\times n$ matrix $P$ is an **orthogonal projection of rank $k$** if
--
--   1. $P^{\mathsf T}=P$ (symmetric),
--   2. $P^2=P$ (idempotent), and
--   3. $\operatorname{rank}P=k$.
--
--   Equivalently, $P$ is the matrix of the orthogonal projection of $\mathbb R^n$ onto a $k$-dimensional subspace. Section 5 of the paper works throughout with orthogonal projections of rank $k$ that also satisfy $P\mathbf 1=0$, i.e. whose image is orthogonal to the all-ones vector.
--
--   **Formalization Note** The extra condition $P\mathbf 1=0$ is not part of this predicate; every statement that needs it carries it as a separate hypothesis, as the paper does.
-- source:
--   P. K. Kothari, S. Tudose, On Brouwer's Laplacian conjecture, arXiv:2606.12197v1, §5, pp.4–8 (Lemmas 5.1, 5.2, 5.3, 5.5, 5.6)

import Mathlib

namespace BrouwerLaplacian

/-- **Orthogonal projection of rank `k`.**
Kothari, Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197v1, §5, pp.4–8
("orthogonal projection P of rank k", Lemmas 5.1, 5.2, 5.3, 5.5, 5.6).

`IsOrthProj P k` says that the real `n × n` matrix `P` is symmetric (`Pᵀ = P`), idempotent
(`P² = P`), and has rank `k`, i.e. `P` is the matrix of the orthogonal projection of `ℝⁿ` onto a
`k`-dimensional subspace.

**Formalization Note.** For real matrices `IsHermitian` is symmetry. The condition `P𝟙 = 0`,
which every use in the paper adds, is kept as a separate hypothesis
`P *ᵥ (fun _ => 1) = 0`, as in the paper. -/
def IsOrthProj {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : Prop :=
  P.IsHermitian ∧ P * P = P ∧ P.rank = k

end BrouwerLaplacian


