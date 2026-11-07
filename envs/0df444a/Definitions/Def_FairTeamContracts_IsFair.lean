-- Prove2me | Definitions.Def_FairTeamContracts_IsFair
-- name    : FairTeamContracts_IsFair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:56.560283+00:00
-- url     : https://prove2.me/theorems/301f1d40-d459-4825-b30c-a251109c14eb
-- title:
--   Definition 2.2 — fair team contract (envy-freeness under swaps of shares)
-- statement:
--   A feasible team contract $(S,\alpha)$ is **fair** if every agent is envy-free under the swap of contracts: for every pair $i,j\in S$, let $(S,\hat\alpha)$ be the (not necessarily feasible) contract with $\hat\alpha_i=\alpha_j$, $\hat\alpha_j=\alpha_i$ and $\hat\alpha_k=\alpha_k$ for $k\in S\setminus\{i,j\}$; then there is an equilibrium $E\in\mathcal E_{S,\hat\alpha}$ with
--
--   $$\alpha_i\cdot f(S)-c_i\ \ge\ \alpha_j\cdot f(E)-c_i\cdot\mathbf 1[i\in E],$$
--
--   $$\alpha_j\cdot f(S)-c_j\ \ge\ \alpha_i\cdot f(E)-c_j\cdot\mathbf 1[j\in E].\qquad(1)$$
--
--   In words, both agents of each pair are weakly better off under the original contract than at some common equilibrium after swapping their shares, with the team fixed and all agents re-optimizing their effort.
--
--   **Formalization Note** "Feasible team contract" is part of the predicate. The swapped contract is $\alpha\circ(i\ j)$. The pair may have $i=j$; then the swap is trivial and (1) holds with $E=S$, so this changes nothing. The equilibrium is quantified existentially, as in the paper.
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Definition 2.2, p.9

import Mathlib
import Definitions.Def_FairTeamContracts_IsTeamContract
import Definitions.Def_FairTeamContracts_IsFeasible
import Definitions.Def_FairTeamContracts_IsPNE

namespace FairTeamContracts

/-- **Definition 2.2 (Fair Team Contracts)** (Chen, Castiglioni, Li, *Fair Team Contracts*,
arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Definition 2.2, p.9). A (feasible) team contract
`(S, α)` is fair if for any pair of agents `i, j ∈ S`, with `(S, α̂)` the contract (not necessarily
feasible) where `α̂ᵢ = αⱼ`, `α̂ⱼ = αᵢ` and `α̂ₖ = αₖ` for `k ∈ S∖{i, j}`, there exists an equilibrium
`E ∈ E_{S,α̂}` such that (1) holds:
`αᵢ · f(S) − cᵢ ≥ αⱼ · f(E) − cᵢ · 1[i ∈ E]` and `αⱼ · f(S) − cⱼ ≥ αᵢ · f(E) − cⱼ · 1[j ∈ E]`.

**Formalization Note.** "(feasible) team contract" is the clause `IsTeamContract S α ∧
IsFeasible f c S α`. The swapped contract is `α ∘ Equiv.swap i j`. The pair quantifier allows
`i = j`; then the swap is the identity, `E = S` is an equilibrium by feasibility and (1) holds,
so this changes nothing. The equilibrium is existentially quantified, as on the page. -/
def IsFair {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (S : Finset (Fin n))
    (α : Fin n → ℝ) : Prop :=
  IsTeamContract S α ∧ IsFeasible f c S α ∧
  ∀ i ∈ S, ∀ j ∈ S, ∃ E : Finset (Fin n), IsPNE f c S (α ∘ Equiv.swap i j) E ∧
    α i * f S - c i ≥ α j * f E - (if i ∈ E then c i else 0) ∧
    α j * f S - c j ≥ α i * f E - (if j ∈ E then c j else 0)

end FairTeamContracts


