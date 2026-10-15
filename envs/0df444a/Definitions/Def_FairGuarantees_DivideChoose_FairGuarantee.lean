-- Prove2me | Definitions.Def_FairGuarantees_DivideChoose_FairGuarantee
-- name    : FairGuarantees_DivideChoose_FairGuarantee
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:38.476096+00:00
-- url     : https://prove2.me/theorems/3d673112-4249-41f8-8983-8ad157a3dd54
-- title:
--   Definition 3, p. 12 — Fair Guarantee in a subdomain D* ⊆ D(Ω)
-- statement:
--   Fix the manna $\Omega$, a number $n$ of agents and a subdomain $\mathcal D^*\subseteq\mathcal D(\Omega)$. A mapping $\Gamma:u\mapsto\Gamma(u;n)$ is a **Fair Guarantee** in $\mathcal D^*$ if for every profile $(u_i)_{i=1}^n\in(\mathcal D^*)^n$ there is a partition $\Pi=(S_i)_{i=1}^n\in\mathcal P_n(\Omega)$ such that
--   $$u_i(S_i)\ge\Gamma(u_i;n)\quad\text{for all } i .$$
--
--   A Fair Guarantee is a utility level that can be granted to all agents simultaneously, whatever the other agents' utilities.
--
--   **Formalization Note** The subdomain is a set of functions `Set (E d) → ℝ`; $\Gamma$ takes a utility and the number of agents. The definition fixes $n$ and includes the paper's manna, subdomain, and positive agent-count conditions.
-- source:
--   Bogomolnaia & Moulin, Guarantees in Fair Division, arXiv:1911.10009v3, p. 12, §3.4 Definition 3

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting

namespace FairGuarantees.DivideChoose

variable {d : ℕ}

/-- Definition 3, p. 12: given the manna `Ω` and a subdomain `D∗ ⊆ D(Ω)`, a mapping
`Γ : u ↦ Γ(u; n)` is a Fair Guarantee in `D∗` (for `n` agents) when every profile
`(u_i)_{i=1}^n ∈ (D∗)^n` admits an `n`-partition `(S_i)` of `Ω` with `u_i(S_i) ≥ Γ(u_i; n)`
for all `i`. -/
def IsFairGuarantee (Ω : Set (E d)) (Dstar : Set (Set (E d) → ℝ))
    (Γ : (Set (E d) → ℝ) → ℕ → ℝ) (n : ℕ) : Prop :=
  IsManna Ω ∧ Dstar ⊆ {u | IsUtility Ω u} ∧ 0 < n ∧
    ∀ u : Fin n → Set (E d) → ℝ, (∀ i, u i ∈ Dstar) →
      ∃ P : Fin n → Set (E d), IsPartition Ω Ω n P ∧ ∀ i, Γ (u i) n ≤ u i (P i)

end FairGuarantees.DivideChoose


