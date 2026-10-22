-- Prove2me | Definitions.Def_ChoiceCDLP_Asymptotic_ChoiceNetwork
-- name    : ChoiceCDLP_Asymptotic_ChoiceNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T06:20:25.671441+00:00
-- url     : https://prove2.me/theorems/e1f4f23c-64d3-4dae-8cb9-2f005a127ad1
-- title:
--   Choice-based network RM instance: 0/1 incidence matrix A, revenues r, arrival probability λ ∈ [0,1], choice probabilities P_j(S); R(S), Q(S), P_0(S)
-- statement:
--   A **choice-based network revenue management instance** with $m$ legs and $n$ products consists of
--
--   - an incidence matrix $A = [a_{ij}]_{m\times n}$ with $a_{ij} \in \{0,1\}$, where $a_{ij} = 1$ means that product $j$ uses leg $i$; its $j$th column $A_j$ is the incidence vector of product $j$;
--   - a revenue $r_j \in \mathbb{R}$ for each product $j$ (no sign is assumed);
--   - an arrival probability $\lambda \in [0,1]$ per period, the same in every period;
--   - choice probabilities $P_j(S)$ for every offer set $S \subseteq N = \{1,\dots,n\}$ and every product $j$, with $P_j(S) \ge 0$, $P_j(S) = 0$ for $j \notin S$, and $\sum_{j\in S} P_j(S) \le 1$; the same choice model is used in every period.
--
--   Derived quantities: the no-purchase probability $P_0(S) = 1 - \sum_{j \in S} P_j(S)$, so that $\sum_{j\in S}P_j(S) + P_0(S) = 1$; the expected revenue per arriving customer
--   $$R(S) = \sum_{j \in S} r_j P_j(S);$$
--   and the capacity-consumption vector $Q(S) = A P(S)$, i.e. $Q_i(S) = \sum_{j} a_{ij} P_j(S)$.
--
--   These are the data of the paper's model (§3) on which both the dynamic program (1) and the choice-based deterministic linear program (CDLP) (2) are built.
--
--   **Formalization Note.** Legs are `Fin m`, products `Fin n`, offer sets `Finset (Fin n)`. The incidence matrix has entries in `ℕ` restricted to `{0,1}`; revenues, $\lambda$ and probabilities are real. $R$, $Q$ carry no factor $\lambda$; the factor $\lambda$ appears in the CDLP and the DP, as in the paper.
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 291, §3 (model); p. 292, §3.2 (R(S), Q(S) = AP(S))

import Mathlib

namespace ChoiceCDLP.Asymptotic

/-- A choice-based network revenue management instance (Liu and van Ryzin 2008, §3, p. 291):
`m` legs, `n` products, a `0/1` leg–product incidence matrix `A`, product revenues `r`,
a per-period arrival probability `lam` (the paper's `λ`), and a generic choice model
`P S j = P_j(S)` giving the probability that an arriving customer buys product `j` when the
offer set is `S`. Time homogeneity (one `λ`, one `P` for every period) is built in. -/
structure ChoiceNetwork (m n : ℕ) where
  /-- Incidence matrix: `A i j = 1` iff leg `i` is used by product `j`. -/
  A : Matrix (Fin m) (Fin n) ℕ
  A_zero_or_one : ∀ i j, A i j = 0 ∨ A i j = 1
  /-- Revenue `r_j` of product `j` (no sign is assumed). -/
  r : Fin n → ℝ
  /-- Arrival probability `λ` in each period. -/
  lam : ℝ
  lam_nonneg : 0 ≤ lam
  lam_le_one : lam ≤ 1
  /-- Choice probabilities `P_j(S)`. -/
  P : Finset (Fin n) → Fin n → ℝ
  P_nonneg : ∀ S j, 0 ≤ P S j
  P_eq_zero_of_not_mem : ∀ S j, j ∉ S → P S j = 0
  sum_P_le_one : ∀ S, ∑ j ∈ S, P S j ≤ 1

/-- No-purchase probability `P_0(S) = 1 - ∑_{j ∈ S} P_j(S)` (total probability, p. 291). -/
def ChoiceNetwork.P0 {m n : ℕ} (N : ChoiceNetwork m n) (S : Finset (Fin n)) : ℝ :=
  1 - ∑ j ∈ S, N.P S j

/-- Expected revenue of offer set `S` per arriving customer, `R(S) = ∑_{j ∈ S} r_j P_j(S)`
(p. 292). -/
def ChoiceNetwork.R {m n : ℕ} (N : ChoiceNetwork m n) (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, N.r j * N.P S j

/-- Capacity consumption rate vector `Q(S) = A P(S)`, i.e. `Q_i(S) = ∑_j a_ij P_j(S)`
(p. 292). -/
def ChoiceNetwork.Q {m n : ℕ} (N : ChoiceNetwork m n) (S : Finset (Fin n)) (i : Fin m) : ℝ :=
  ∑ j, (N.A i j : ℝ) * N.P S j

end ChoiceCDLP.Asymptotic


