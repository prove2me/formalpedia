-- Prove2me | Definitions.Def_MarkovChainChoice_Shared_Model
-- name    : MarkovChainChoice_Shared_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:13:29.160988+00:00
-- url     : https://prove2.me/theorems/04469b5d-99c6-4ede-9ef8-8ae59e80547e
-- title:
--   Markov chain choice model: arrival probabilities λ and transition probabilities ρ
-- statement:
--   There are $n$ products indexed by $N = \{1,\dots,n\}$. In the **Markov chain choice model**, a customer arrives into the system to purchase product $j$ with probability $\lambda_j$. If that product is available she purchases it; otherwise she transitions to product $i$ with probability $\rho_{j,i}$ and checks whether product $i$ is available, and with probability $1-\sum_{i\in N}\rho_{j,i}$ she leaves without a purchase. The customer moves between products according to this Markov chain until she reaches an available product or the no-purchase option. Throughout, the model satisfies the standing assumptions
--   $$\lambda_j > 0 \quad\text{and}\quad \sum_{i\in N}\rho_{j,i} < 1 \qquad \text{for all } j \in N.$$
--
--   These are the primitive data of every result of the paper: the purchase probabilities, the assortment problem and the single-resource dynamic program are all built from $(\lambda,\rho)$.
--
--   **Formalization Note** Products are `Fin n`. `lam j` $=\lambda_j$ and `rho j i` $=\rho_{j,i}$ (the transition *from* $j$ *to* $i$). The fields `lam_pos` and `rho_row_lt_one` are the paper's standing assumption (p. 1325). The field `rho_nonneg` ($\rho_{j,i}\ge 0$) is not written in the paper but is implied by $\rho_{j,i}$ being a probability. The condition $\sum_j \lambda_j \le 1$ is not part of the model; it is a hypothesis of the single-resource results that need it.
--
--   **Shared definition.** Serves chunks `02-single-resource` (§2, pp. 1324–1325; previously `MarkovChainChoice.SingleResource.Model`) and `04-dimension-reduction` (§2, pp. 1324–1325; previously `MarkovChainChoice.DimReduction.Model`). Both copies had the same structure (`lam`, `rho`, `lam_pos`, `rho_nonneg`, `rho_row_lt_one`) and the same conventions: products `Fin n` (0-based), `rho j i` $=\rho_{j,i}$ from $j$ to $i$, the p. 1325 standing assumption as fields, $\rho_{j,i}\ge 0$ implicit, and $\sum_j\lambda_j\le 1$ not imposed.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, pp. 1324–1325, Section 2 (model description and the standing assumption on p. 1325); shared by chunks 02-single-resource and 04-dimension-reduction

import Mathlib

namespace MarkovChainChoice.Shared

/-- The Markov chain choice model on the products `N = {1, …, n}` (`Fin n`), Feldman–Topaloglu 2017,
§2, p. 1324–1325. `lam j = λ_j` is the probability that an arriving customer first considers product
`j`; `rho j i = ρ_{j,i}` is the probability that a customer who visits an unavailable product `j`
transitions next to product `i`. The fields `lam_pos` and `rho_row_lt_one` are the paper's standing
assumption "λ_j > 0 and Σ_{i∈N} ρ_{j,i} < 1 for all j ∈ N" (p. 1325); `rho_nonneg` is implicit in
reading `ρ_{j,i}` as a probability. -/
structure Model (n : ℕ) where
  /-- `lam j = λ_j`, the arrival probability for product `j`. -/
  lam : Fin n → ℝ
  /-- `rho j i = ρ_{j,i}`, the transition probability from product `j` to product `i`. -/
  rho : Fin n → Fin n → ℝ
  lam_pos : ∀ j, 0 < lam j
  rho_nonneg : ∀ j i, 0 ≤ rho j i
  rho_row_lt_one : ∀ j, ∑ i, rho j i < 1

end MarkovChainChoice.Shared


