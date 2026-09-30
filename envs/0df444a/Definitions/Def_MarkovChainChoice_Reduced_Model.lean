-- Prove2me | Definitions.Def_MarkovChainChoice_Reduced_Model
-- name    : MarkovChainChoice_Reduced_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:28:29.704125+00:00
-- url     : https://prove2.me/theorems/75772c8c-ba5a-4576-867a-7e94bc1ec903
-- title:
--   Markov chain choice model: arrival probabilities λ, transition probabilities ρ, and the (Balance) solution (P_S, R_S)
-- statement:
--   There are $n$ products indexed by $N = \{1,\dots,n\}$. In the **Markov chain choice model**, a customer arrives to purchase product $j$ with probability $\lambda_j$. If the product she visits is available for purchase she buys it; otherwise she transitions from product $j$ to product $i$ with probability $\rho_{j,i}$, and leaves the system without a purchase with probability $1-\sum_{i\in N}\rho_{j,i}$. Throughout, the model satisfies the standing assumptions
--   $$\lambda_j > 0 \quad\text{and}\quad \sum_{i\in N}\rho_{j,i} < 1 \qquad \text{for all } j \in N.$$
--
--   For an offer set $S \subseteq N$, let $P_{j,S}$ be the expected number of times a customer visits product $j$ while it is available (its purchase probability) and $R_{j,S}$ the expected number of times she visits $j$ while it is unavailable. The pair $(P_S, R_S)$ is the solution of the **(Balance)** equations
--   $$P_{j,S} + R_{j,S} = \lambda_j + \sum_{i\in N}\rho_{i,j}R_{i,S}\ \ \forall j\in N,\qquad P_{j,S} = 0\ \ \forall j\notin S,\qquad R_{j,S} = 0\ \ \forall j\in S.$$
--
--   These objects are the common vocabulary of every result of the paper; the choice-based and reduced linear programs of network revenue management are written in terms of them.
--
--   **Formalization Note** Products are `Fin n` and offer sets `Finset (Fin n)`. The model is a structure whose fields are $\lambda$, $\rho$ (with `rho j i` $=\rho_{j,i}$, the transition from $j$ to $i$) and the standing assumptions; the nonnegativity $\rho_{j,i}\ge 0$ is not written in the paper but is implied by $\rho_{j,i}$ being a probability, and is added as a field. `IsBalance M S P R` is the (Balance) system. `purchase M S` $=P_S$ and `visitNot M S` $=R_S$ are the two components of a solution chosen by `Classical.epsilon`; that this choice is *the* unique nonnegative solution is the separate milestone `balance_unique_nonneg`.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, pp. 1324–1325, Section 2, (Balance) and the standing assumption on p. 1325

import Mathlib

namespace MarkovChainChoice.Reduced

/-- The Markov chain choice model on the products `N = {1, …, n}` (encoded as `Fin n`),
Feldman–Topaloglu (Oper. Res. 65(5), 2017), §2, pp. 1324–1325.
`lam j = λ_j` is the probability that a customer arrives to purchase product `j`;
`rho j i = ρ_{j,i}` is the probability that a customer who finds product `j` unavailable
transitions to product `i`. The fields `lam_pos` and `rho_row_lt_one` are the paper's standing
assumption (p. 1325): `λ_j > 0` and `∑_{i ∈ N} ρ_{j,i} < 1` for all `j ∈ N`. The field
`rho_nonneg` is implicit in the paper (the `ρ_{j,i}` are probabilities). -/
structure Model (n : ℕ) where
  lam : Fin n → ℝ
  rho : Fin n → Fin n → ℝ
  lam_pos : ∀ j, 0 < lam j
  rho_nonneg : ∀ j i, 0 ≤ rho j i
  rho_row_lt_one : ∀ j, ∑ i, rho j i < 1

variable {n : ℕ}

/-- The (Balance) equations (p. 1324) for the offer set `S`:
`P_j + R_j = λ_j + ∑_{i ∈ N} ρ_{i,j} R_i` for all `j`, `P_j = 0` for `j ∉ S`,
`R_j = 0` for `j ∈ S`. -/
def IsBalance (M : Model n) (S : Finset (Fin n)) (P R : Fin n → ℝ) : Prop :=
  (∀ j, P j + R j = M.lam j + ∑ i, M.rho i j * R i) ∧
  (∀ j, j ∉ S → P j = 0) ∧
  (∀ j, j ∈ S → R j = 0)

/-- A solution `(P_S, R_S)` of the (Balance) equations for the offer set `S`, chosen by
`Classical.epsilon`. Under the model's standing assumptions the solution exists and is unique
(Feldman–Topaloglu, p. 1325), so this is *the* solution of the paper. -/
noncomputable def balanceSol (M : Model n) (S : Finset (Fin n)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  Classical.epsilon (fun PR : (Fin n → ℝ) × (Fin n → ℝ) => IsBalance M S PR.1 PR.2)

/-- `P_{j,S}`: the purchase probability of product `j` when the offer set is `S`. -/
noncomputable def purchase (M : Model n) (S : Finset (Fin n)) : Fin n → ℝ :=
  (balanceSol M S).1

/-- `R_{j,S}`: the expected number of visits to product `j` while it is unavailable,
when the offer set is `S`. -/
noncomputable def visitNot (M : Model n) (S : Finset (Fin n)) : Fin n → ℝ :=
  (balanceSol M S).2

end MarkovChainChoice.Reduced


