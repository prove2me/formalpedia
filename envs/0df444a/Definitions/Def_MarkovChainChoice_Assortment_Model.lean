-- Prove2me | Definitions.Def_MarkovChainChoice_Assortment_Model
-- name    : MarkovChainChoice_Assortment_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:08:53.495804+00:00
-- url     : https://prove2.me/theorems/76e1e209-3d96-4391-a90f-3786cb8bb142
-- title:
--   Markov chain choice model, the (Balance) equations, purchase probabilities $P_{j,S}$ and the (Assortment) objective
-- statement:
--   **Markov chain choice model.** There are $n$ products $N=\{1,\dots,n\}$. A customer arrives to purchase product $j$ with probability $\lambda_j$. If the product she visits is offered she buys it; otherwise she moves from product $j$ to product $i$ with probability $\rho_{j,i}$, and leaves without buying with probability $1-\sum_{i\in N}\rho_{j,i}$. Throughout, $\lambda_j>0$ and $\sum_{i\in N}\rho_{j,i}<1$ for all $j\in N$, and all $\rho_{j,i}\ge 0$.
--
--   **(Balance).** For an offer set $S\subseteq N$, a pair of vectors $(P,R)\in\mathbb R^n\times\mathbb R^n$ satisfies the (Balance) equations when
--
--   $$
--   P_j+R_j=\lambda_j+\sum_{i\in N}\rho_{i,j}R_i\quad\forall j\in N,\qquad P_j=0\quad\forall j\notin S,\qquad R_j=0\quad\forall j\in S.
--   $$
--
--   $P_{j,S}$ is the expected number of visits to product $j$ while it is available (the probability that product $j$ is purchased), and $R_{j,S}$ the expected number of visits to product $j$ while it is unavailable; $(P_S,R_S)$ denotes the solution of (Balance).
--
--   **(Assortment).** Given revenues $r_j\in\mathbb R$, the expected revenue of the offer set $S$ is $\sum_{j\in N}P_{j,S}\,r_j$, and the assortment problem is
--
--   $$
--   \max_{S\subseteq N}\ \sum_{j\in N}P_{j,S}\,r_j .
--   $$
--
--   An optimal assortment is an offer set whose revenue is at least that of every other offer set.
--
--   These are the objects of all the assortment results of the paper: every statement about optimal assortments is a statement about the (Balance) solution.
--
--   **Formalization Note.** Products are `Fin n` (0-based), offer sets are `Finset (Fin n)`, and `rho j i` is $\rho_{j,i}$ (transition *from* $j$ *to* $i$). The fields `lam_pos` and `rho_row_lt_one` are the paper's standing assumption (p. 1325); `rho_nonneg` is implicit in the paper, since the $\rho_{j,i}$ are probabilities. `balanceSol M S` is a solution of (Balance) chosen by `Classical.epsilon`; that the solution exists, is unique and is nonnegative is the separate milestone `balance_unique_nonneg`, so `purchase M S` and `visitNot M S` are the paper's $P_S$ and $R_S$. Revenues carry no sign assumption.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, pp. 1324–1326, Section 2 (Balance) and Section 3 (Assortment); DOI 10.1287/opre.2017.1628

import Mathlib

namespace MarkovChainChoice.Assortment

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

/-- The expected revenue `∑_{j ∈ N} P_{j,S} r_j` of the offer set `S`, the objective of
(Assortment) (p. 1326). -/
noncomputable def revenue (M : Model n) (r : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ j, purchase M S j * r j

/-- `S` is an optimal solution of (Assortment) `max_{S ⊆ N} ∑_{j ∈ N} P_{j,S} r_j` (p. 1326). -/
def IsOptimalAssortment (M : Model n) (r : Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ T : Finset (Fin n), revenue M r T ≤ revenue M r S

end MarkovChainChoice.Assortment


