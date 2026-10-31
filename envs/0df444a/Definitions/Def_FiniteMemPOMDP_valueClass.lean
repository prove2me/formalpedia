-- Prove2me | Definitions.Def_FiniteMemPOMDP_valueClass
-- name    : FiniteMemPOMDP_valueClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:52.94182+00:00
-- url     : https://prove2.me/theorems/73206b91-548a-4e0d-996d-b032be083682
-- title:
--   Value partition $\mathcal K_1,\dots,\mathcal K_I$
-- statement:
--   Let $\sigma$ be a strategy and $p^*\in\Delta(\mathcal K)$. Two states $k,k'\in\operatorname{supp}(p^*)$ are equivalent if $\gamma^k_\infty(\sigma)=\gamma^{k'}_\infty(\sigma)$; the classes $\mathcal K_1,\dots,\mathcal K_I$ form the **value partition**, and $\gamma^i_\infty$ is the common value on $\mathcal K_i$.
--
--   `valueClass Γ p σ c` is the class of value $c$: the states $k$ with $p^*(k)>0$ and $\gamma^k_\infty(\sigma)=c$.
--
--   **Formalization Note** Classes are indexed by their value $c\in\mathbb R$ instead of $i\in[1..I]$; for a real $c$ that is not a value the class is empty.
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Definition 6.1, p.15; §6.3, p.17

import Mathlib
import Definitions.Def_FiniteMemPOMDP_gammaInf

namespace FiniteMemPOMDP

variable {K A S : Type} [Fintype K] [DecidableEq K] [Fintype A] [Fintype S] [Nonempty A]
  [Nonempty S]

/-- **The value partition `K_1, …, K_I`.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Definition 6.1, p.15: "Let ∼ be the
equivalence relationship on supp(p∗) defined by k ∼ k′ if and only if γ^k_∞(σ) = γ^{k′}_∞(σ).
Let {K1, . . . , KI} be the corresponding value partition." §6.3, p.17: "the map k ↦ γ^k_∞(σ) is
constant on Ki, and we denote its value by γ^i_∞."

`valueClass Γ p σ c` is the set of states `k ∈ supp(p)` with `γ^k_∞(σ) = c`.

**Formalization Note** The classes are indexed by their value `c ∈ ℝ` instead of by
`i ∈ [1 .. I]`: the class `K_i` of the paper is `valueClass Γ p σ γ^i_∞`, and for a real `c`
that is not a value `γ^k_∞(σ)` with `k ∈ supp(p)` the class is empty. -/
noncomputable def valueClass (Γ : POMDP K A S) (p : stdSimplex ℝ K) (σ : List (A × S) → A)
    (c : ℝ) : Finset K := by
  classical
  exact Finset.univ.filter fun k => 0 < p.1 k ∧ gammaInf Γ (pointBelief k) σ = c

end FiniteMemPOMDP


