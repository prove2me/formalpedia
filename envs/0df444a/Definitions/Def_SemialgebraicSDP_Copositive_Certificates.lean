-- Prove2me | Definitions.Def_SemialgebraicSDP_Copositive_Certificates
-- name    : SemialgebraicSDP_Copositive_Certificates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:59.703891+00:00
-- url     : https://prove2.me/theorems/9c9edc07-b5d2-4ca4-84c5-d3bc8a96543b
-- title:
--   §7.5, pp. 317–318 — feasibility of the SDPs (7.7) and condition (7.6) $M = P + N$
-- statement:
--   Let $n$ be a natural number and $M = (m_{ij})$ a real $n \times n$ matrix. This module defines two certificates of copositivity from §7.5 of the paper.
--
--   1. **Feasibility of the SDPs (7.7)** (p. 318). There exist $n$ real symmetric $n\times n$ matrices $\Lambda^1, \dots, \Lambda^n \in \mathcal S^n$ (with entries $\Lambda^i_{jk} = \Lambda^i_{kj}$) such that
--   $$
--   \begin{aligned}
--   M - \Lambda^i &\succeq 0, && i = 1, \dots, n,\\
--   \Lambda^i_{ii} &= 0, && i = 1, \dots, n,\\
--   \Lambda^i_{jj} + \Lambda^j_{ji} + \Lambda^j_{ij} &= 0, && i \ne j,\\
--   \Lambda^i_{jk} + \Lambda^j_{ki} + \Lambda^k_{ij} &\ge 0, && i, j, k \text{ pairwise distinct}.
--   \end{aligned}
--   $$
--   Here $A \succeq 0$ means that $A$ is symmetric and $x^T A x \ge 0$ for all $x \in \mathbb R^n$.
--   2. **Condition (7.6)** (p. 317). $M$ decomposes as the sum of a positive semidefinite and an elementwise nonnegative matrix:
--   $$
--   M = P + N, \qquad P \succeq 0, \qquad n_{ij} \ge 0 \text{ for all } i, j.
--   $$
--
--   Both are semidefinite feasibility problems in the entries of $\Lambda$, respectively $P$ and $N$; Theorem 7.7 shows that the first certifies copositivity of $M$ and is at least as strong as the second.
--
--   **Formalization Note** $\Lambda$ is a family `Λ : Fin n → Matrix (Fin n) (Fin n) ℝ` and $\Lambda^i_{jk}$ is `Λ i j k`: the superscript selects the matrix, the subscripts its entry. The page's index condition "$i \ne j \ne k$" is read as $i, j, k$ pairwise distinct; given the symmetry of each $\Lambda^i$ and the third constraint, the additional constraints of the literal reading ($i = k \ne j$) hold automatically with equality, so both readings define the same feasible set. Positive semidefiniteness is Mathlib's `Matrix.PosSemidef`. The letter $P$ in (7.6) denotes a matrix and is unrelated to the form $P(z)$.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, p. 318, Theorem 7.7 (the SDPs (7.7)), and p. 317, condition (7.6)

import Mathlib

namespace SemialgebraicSDP.Copositive

/-- Feasibility of the SDPs (7.7) of Theorem 7.7 (Parrilo 2003, p. 318): there are `n`
symmetric matrices `Λⁱ ∈ Sⁿ` (`Λ i j k` is the entry `Λⁱ_jk`) with
* `M − Λⁱ ⪰ 0` for `i = 1, …, n`;
* `Λⁱ_ii = 0` for `i = 1, …, n`;
* `Λⁱ_jj + Λʲ_ji + Λʲ_ij = 0` for `i ≠ j`;
* `Λⁱ_jk + Λʲ_ki + Λᵏ_ij ≥ 0` for `i ≠ j ≠ k`, read as `i, j, k` pairwise distinct. -/
def Feasible77 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ Λ : Fin n → Matrix (Fin n) (Fin n) ℝ,
    (∀ i, (Λ i).IsSymm) ∧
    (∀ i, (M - Λ i).PosSemidef) ∧
    (∀ i, Λ i i i = 0) ∧
    (∀ i j, i ≠ j → Λ i j j + Λ j j i + Λ j i j = 0) ∧
    (∀ i j k, i ≠ j → j ≠ k → i ≠ k → 0 ≤ Λ i j k + Λ j k i + Λ k i j)

/-- Condition (7.6) (p. 317): `M = P + N` with `P ⪰ 0` and `N` elementwise nonnegative
(`nᵢⱼ ≥ 0`). -/
def Cond76 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ P N : Matrix (Fin n) (Fin n) ℝ, M = P + N ∧ P.PosSemidef ∧ ∀ i j, 0 ≤ N i j

end SemialgebraicSDP.Copositive


