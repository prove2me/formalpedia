-- Prove2me | Definitions.Def_PersuadeFly_Instance
-- name    : PersuadeFly_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:10.19834+00:00
-- url     : https://prove2.me/theorems/96819f22-164f-404b-9587-83fa0e2b3195
-- title:
--   A persuasion instance $\mathcal I=(\Omega,A,u,v,\mathcal B_0)$
-- statement:
--   A **persuasion instance** is a tuple $\mathcal I=(\Omega,A,u,v,\mathcal B_0)$ where $\Omega$ is a finite set of states, $A$ a finite set of actions, $u:\Omega\times A\to\mathbb R$ the receiver's utility, $v:\Omega\times A\to[0,1]$ the sender's utility, and $\mathcal B_0\subseteq\Delta(\Omega)$ the set known to contain the unknown state distribution $\mu^*$.
--
--   Every other object of the mission is built on an instance.
--
--   **Formalization Note** $\Delta(\Omega)$ is the standard simplex of nonnegative functions on $\Omega$ summing to $1$. The paper's standing assumptions $|\Omega|\ge2$, $|A|\ge2$ are hypotheses of every theorem.
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, §2, p.12

import Mathlib

namespace PersuadeFly

/-- **A persuasion instance** `I = (Ω, A, u, v, B₀)`. Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, §2, p.12: the receiver's utility
`u : Ω × A → ℝ`, the sender's utility `v : Ω × A → [0, 1]`, and the set `B₀ ⊆ Δ(Ω)` known to contain
the unknown state distribution `μ*`.

**Formalization Note** `Δ(Ω)` is Mathlib's `stdSimplex ℝ Ω` (nonnegative functions summing to 1).
The standing assumptions `|Ω| ≥ 2`, `|A| ≥ 2` of p.12 are `[Nontrivial Ω] [Nontrivial A]` binders of
every theorem. -/
structure Instance (Ω A : Type) [Fintype Ω] where
  /-- The receiver's utility `u(ω, a)`. -/
  u : Ω → A → ℝ
  /-- The sender's utility `v(ω, a)`. -/
  v : Ω → A → ℝ
  v_nonneg : ∀ ω a, 0 ≤ v ω a
  v_le_one : ∀ ω a, v ω a ≤ 1
  /-- The sender's prior knowledge: `μ* ∈ B₀`. -/
  B0 : Set (Ω → ℝ)
  B0_subset : B0 ⊆ stdSimplex ℝ Ω

end PersuadeFly


