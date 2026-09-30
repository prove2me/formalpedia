-- Prove2me | Definitions.Def_MarkovChainChoice_Shared_Balance
-- name    : MarkovChainChoice_Shared_Balance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:14:12.354912+00:00
-- url     : https://prove2.me/theorems/ca4d6545-a101-41dc-819c-de73ae97be46
-- title:
--   The (Balance) equations and the purchase probabilities $P_{j,S}$ of the Markov chain choice model
-- statement:
--   Fix a Markov chain choice model $(\lambda,\rho)$ on $N=\{1,\dots,n\}$ and an offer set $S\subseteq N$. Let $P_{j,S}$ be the expected number of times a customer visits product $j$ while it is available for purchase, and $R_{j,S}$ the expected number of times she visits product $j$ while it is not available. The vectors $P_S=(P_{1,S},\dots,P_{n,S})$ and $R_S=(R_{1,S},\dots,R_{n,S})$ solve the **(Balance)** equations
--   $$P_{j,S} + R_{j,S} = \lambda_j + \sum_{i\in N}\rho_{i,j}R_{i,S}\quad \forall j\in N,\qquad P_{j,S}=0\quad\forall j\notin S,\qquad R_{j,S}=0\quad\forall j\in S.$$
--   Since a customer visits an available product at most once, $P_{j,S}$ is the probability that a customer purchases product $j$ when $S$ is offered.
--
--   This definition supplies the purchase probabilities used by the assortment problem and by the single-resource dynamic program.
--
--   **Formalization Note** `IsBalance M S P R` is the system above; note the index order $\rho_{i,j}$ (flow *into* $j$). `balanceSol M S` is a solution chosen by `Classical.epsilon`, and `purchase M S` $=P_S$, `visitNot M S` $=R_S$ are its components. That this solution exists, is unique and is nonnegative is the separate theorem `balance_unique_nonneg`, so under the model's standing assumptions `purchase M S` is the paper's $P_S$.
--
--   **Shared definition.** Serves chunks `02-single-resource` ((Balance), p. 1324; previously `MarkovChainChoice.SingleResource.Balance`) and `04-dimension-reduction` ((Balance), p. 1324; previously `MarkovChainChoice.DimReduction.Balance`). Both copies define `IsBalance`, `balanceSol` (a `Classical.epsilon` choice), `purchase` and `visitNot` with identical bodies and the same inflow index order $\rho_{i,j}$.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1324, Section 2, (Balance); shared by chunks 02-single-resource and 04-dimension-reduction

import Mathlib
import Definitions.Def_MarkovChainChoice_Shared_Model

namespace MarkovChainChoice.Shared

variable {n : ℕ}

/-- The (Balance) equations of Feldman–Topaloglu 2017, p. 1324, for the offer set `S`:
`P_j + R_j = λ_j + Σ_{i∈N} ρ_{i,j} R_i` for all `j`, `P_j = 0` for `j ∉ S`, `R_j = 0` for `j ∈ S`. -/
def IsBalance (M : Model n) (S : Finset (Fin n)) (P R : Fin n → ℝ) : Prop :=
  (∀ j, P j + R j = M.lam j + ∑ i, M.rho i j * R i) ∧
    (∀ j, j ∉ S → P j = 0) ∧ (∀ j, j ∈ S → R j = 0)

/-- The pair `(P_S, R_S)`: a solution of the (Balance) equations for `S`, chosen by
`Classical.epsilon`. Under the model's standing assumptions the solution exists and is unique
(§2, p. 1325), so this is *the* solution. -/
noncomputable def balanceSol (M : Model n) (S : Finset (Fin n)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  Classical.epsilon (fun PR : (Fin n → ℝ) × (Fin n → ℝ) => IsBalance M S PR.1 PR.2)

/-- `purchase M S j = P_{j,S}`, the probability that a customer purchases product `j` when the
offer set is `S`. -/
noncomputable def purchase (M : Model n) (S : Finset (Fin n)) : Fin n → ℝ :=
  (balanceSol M S).1

/-- `visitNot M S j = R_{j,S}`, the expected number of visits to product `j` while it is not
available, when the offer set is `S`. -/
noncomputable def visitNot (M : Model n) (S : Finset (Fin n)) : Fin n → ℝ :=
  (balanceSol M S).2

end MarkovChainChoice.Shared


