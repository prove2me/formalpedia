-- Prove2me | Definitions.Def_FairTeamContracts_IsPNE
-- name    : FairTeamContracts_IsPNE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:51.861972+00:00
-- url     : https://prove2.me/theorems/e1fb4c4d-e64b-46f5-9f78-26b54cc46c5c
-- title:
--   Definition 2.1 — pure Nash equilibrium $E\subseteq S$ of effort
-- statement:
--   Given a team contract $(S,\alpha)$ with costs $c$, a set $E\subseteq S$ of agents forms a **pure Nash equilibrium** for exerting costly effort if
--
--   $$\alpha_i\cdot f(E)-c_i\ \ge\ \alpha_i\cdot f(E\setminus\{i\})\qquad\forall i\in E,$$
--
--   $$\alpha_i\cdot f(E\cup\{i\})-c_i\ <\ \alpha_i\cdot f(E)\qquad\forall i\in S\setminus E.$$
--
--   The set of such $E$ is $\mathcal E_{S,\alpha}$. The strict inequality encodes the paper's tie-breaking rule: an indifferent agent exerts effort.
--
--   **Formalization Note** $E$ ranges over subsets of the team only.
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Definition 2.1, p.8

import Mathlib

namespace FairTeamContracts

/-- **Definition 2.1 (Pure Nash Equilibrium)** (Chen, Castiglioni, Li, *Fair Team Contracts*,
arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Definition 2.1, p.8). Given a team contract
`(S, α)`, the set of agents `E ⊆ S` forms a pure Nash equilibrium for exerting costly effort if
`αᵢ · f(E) − cᵢ ≥ αᵢ · f(E∖{i})` for all `i ∈ E`, and
`αᵢ · f(E ∪ {i}) − cᵢ < αᵢ · f(E)` for all `i ∈ S∖E`.
The set `E_{S,α}` of the paper is `{E | IsPNE f c S α E}`.

**Formalization Note.** The strict inequality for agents outside `E` encodes the paper's
tie-breaking rule (indifferent agents exert effort). `E` ranges over subsets of the team `S` only. -/
def IsPNE {n : ℕ} (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (S : Finset (Fin n))
    (α : Fin n → ℝ) (E : Finset (Fin n)) : Prop :=
  E ⊆ S ∧
  (∀ i ∈ E, α i * f E - c i ≥ α i * f (E.erase i)) ∧
  (∀ i ∈ S \ E, α i * f (insert i E) - c i < α i * f E)

end FairTeamContracts


