-- Prove2me | Definitions.Def_FreeReplExchange_IsMICSet
-- name    : FreeReplExchange_IsMICSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:17:34.943432+00:00
-- url     : https://prove2.me/theorems/c18a5d04-768b-469d-8c3f-6541f0fab762
-- title:
--   Myopic incentive compatibility of a proposal set, (7)
-- statement:
--   Fix a participating set $P$, an allocation $x$ and a set $\mathcal P$ of proposals. For a profile $\sigma$ of accept/reject decisions on $\mathcal P$, let $x'(\sigma)$ be the allocation obtained by executing at $x$ the proposals both of whose participants accept. The set $\mathcal P$ is **myopically incentive compatible (MIC)** with respect to $x$ if accepting every proposal is a best response for each participant regardless of the others' decisions:
--   $$\tilde u_i\bigl(x'(\sigma^\star_i,\sigma_{-i})\bigr)\ge \tilde u_i\bigl(x'(\sigma_i,\sigma_{-i})\bigr)\qquad\text{for all }\sigma_i,\sigma_{-i}\text{ and all }i\in P.$$
--
--   This is the per-round incentive notion that determines which proposal sets a protocol may post; Proposition 1 and Theorem 11 characterize it.
--
--   **Formalization Note** A decision profile assigns every agent a decision on every proposal; $\sigma_i$ is agent $i$'s row and $\sigma^\star_i$ the constant row "accept". This is the game-theoretic definition, not its characterization.
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), Desideratum 3, p.15 (PDF p.17), eq. (7)

import Mathlib
import Definitions.Def_FreeReplExchange_util
import Definitions.Def_FreeReplExchange_Exchange

namespace FreeReplExchange

open Classical in
/-- The allocation `x′(σ)` of Desideratum 3: execute at `x` exactly the proposals of `Props` both
of whose participants accept under the decision profile `δ` (`δ k p` is agent `k`'s decision on
`p`). -/
noncomputable def outcome {A : Type*} [DecidableEq A] {m : ℕ} (x : A → Fin m → Bool)
    (Props : Finset (Exchange A m)) (δ : A → Exchange A m → Bool) : A → Fin m → Bool :=
  exec x (Props.filter fun p => δ p.i p && δ p.j p)

/-- Myopic incentive compatibility of a proposal set, Desideratum 3, (7), Yang–Kandasamy,
*Pairwise Exchanges of Freely Replicable Goods with Negative Externalities*, arXiv:2603.12403
(held version, sha256 3ae07967…), p.15 (PDF p.17): accepting every proposal is a best response for
each participant regardless of the others' decisions,
`ũ_i(x′(σ⋆_i, σ_{−i})) ≥ ũ_i(x′(σ_i, σ_{−i}))` for all `σ_i, σ_{−i}` and all `i ∈ P`.

**Formalization Note.** This is the game-theoretic definition (7), not the characterization of
Proposition 1. A decision profile `δ : A → Exchange A m → Bool` assigns every agent a decision on
every proposal; `σ_i` is `δ i` and `σ_{−i}` the other rows. Replacing row `i` by the constant
`true` is `σ⋆_i`. Desideratum 3 applies the notion to sets of well-formed proposals among `P` at an
allocation `x ≥ x^(0)`; those premises are hypotheses of the theorems that use it. -/
def IsMICSet {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ} (U : A → A → Fin m → ℝ)
    (P : Finset A) (x : A → Fin m → Bool) (Props : Finset (Exchange A m)) : Prop :=
  ∀ i ∈ P, ∀ δ : A → Exchange A m → Bool,
    util U i (outcome x Props δ) ≤ util U i (outcome x Props (Function.update δ i fun _ => true))

end FreeReplExchange


