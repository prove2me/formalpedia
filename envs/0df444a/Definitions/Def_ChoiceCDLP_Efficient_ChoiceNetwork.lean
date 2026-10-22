-- Prove2me | Definitions.Def_ChoiceCDLP_Efficient_ChoiceNetwork
-- name    : ChoiceCDLP_Efficient_ChoiceNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T06:58:46.323976+00:00
-- url     : https://prove2.me/theorems/a0e126c9-227e-485c-9a4f-006b59971d86
-- title:
--   Network choice model: 0–1 incidence matrix, purchase probabilities P_j(S), revenue R(S) and consumption Q(S) = AP(S)
-- statement:
--   **The network revenue-management model under customer choice.** A network has $m$ legs and offers $n$ products $N = \{1, \dots, n\}$ (in Lean, `Fin m` and `Fin n`). Product $j$ earns revenue $r_j$. The **incidence matrix** $A = [a_{ij}]_{m \times n}$ has $a_{ij} = 1$ if leg $i$ is used by product $j$ and $a_{ij} = 0$ otherwise.
--
--   An **offer set** is a subset $S \subseteq N$ of products made available. Given $S$, an arriving customer buys product $j$ with probability $P_j(S) \ge 0$, where $P_j(S) = 0$ if $j \notin S$, and buys nothing with probability $P_0(S) \ge 0$; by total probability
--   $$\sum_{j \in S} P_j(S) + P_0(S) = 1 .$$
--
--   From these the model builds the **expected revenue** of an arriving customer and the vector of **capacity consumption probabilities**
--   $$R(S) = \sum_{j \in S} r_j P_j(S), \qquad Q(S) = A\,P(S) \in \mathbb{R}^m ,$$
--   where $P(S) = (P_1(S), \dots, P_n(S))^\top$; $Q_i(S)$ is the probability of using a unit of capacity on leg $i$ when $S$ is offered.
--
--   **Formalization Note.** The choice probabilities are generic (no parametric choice model is imposed), as in the paper. The arrival probability $\lambda$, capacities and horizon are not part of this structure: they are parameters of the CDLP definition. Revenues $r_j$ are arbitrary reals. This duplicates the model of the sibling mission *…I: The CDLP Is Asymptotically Optimal*, which is drafted concurrently and cannot be imported.
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 291, §3 (model, choice probabilities) and p. 292, §3.2 (R(S), Q(S) = AP(S))

import Mathlib

namespace ChoiceCDLP.Efficient

/-- The network revenue-management model under customer choice (Liu–van Ryzin 2008, §3, p. 291,
and §3.2, p. 292): `m` legs, `n` products `N = {1, …, n}` (here `Fin n`), revenues `r j`, a 0–1
leg–product incidence matrix `A`, and, for each offer set `S ⊆ N`, purchase probabilities
`P S j` and a no-purchase probability `P0 S` with `P S j = 0` for `j ∉ S` and
`∑_{j ∈ S} P S j + P0 S = 1`. -/
structure ChoiceNetwork (m n : ℕ) where
  /-- revenue `r_j` of product `j` -/
  r : Fin n → ℝ
  /-- incidence matrix `A = [a_ij]`: `a_ij = 1` if leg `i` is used by product `j`, else `0` -/
  A : Matrix (Fin m) (Fin n) ℝ
  A_zero_or_one : ∀ i j, A i j = 0 ∨ A i j = 1
  /-- purchase probability `P_j(S)` of product `j` when offer set `S` is offered -/
  P : Finset (Fin n) → Fin n → ℝ
  /-- no-purchase probability `P_0(S)` -/
  P0 : Finset (Fin n) → ℝ
  P_nonneg : ∀ S j, 0 ≤ P S j
  P0_nonneg : ∀ S, 0 ≤ P0 S
  P_eq_zero_of_not_mem : ∀ S j, j ∉ S → P S j = 0
  sum_P_add_P0 : ∀ S, (∑ j ∈ S, P S j) + P0 S = 1

variable {m n : ℕ}

/-- Expected revenue from an arriving customer when `S` is offered:
`R(S) = ∑_{j ∈ S} r_j P_j(S)` (p. 292). -/
def revenue (N : ChoiceNetwork m n) (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, N.r j * N.P S j

/-- Capacity-consumption probability vector `Q(S) = A P(S)` (p. 292), with
`P(S) = (P_1(S), …, P_n(S))ᵀ`. -/
def consumption (N : ChoiceNetwork m n) (S : Finset (Fin n)) : Fin m → ℝ :=
  Matrix.mulVec N.A (N.P S)

end ChoiceCDLP.Efficient


