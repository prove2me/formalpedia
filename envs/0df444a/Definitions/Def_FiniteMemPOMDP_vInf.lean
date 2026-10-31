-- Prove2me | Definitions.Def_FiniteMemPOMDP_vInf
-- name    : FiniteMemPOMDP_vInf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:31:57.685278+00:00
-- url     : https://prove2.me/theorems/914b07e1-ef03-4268-8b17-b81675616b5a
-- title:
--   Long-run value $v_\infty(p_1)$
-- statement:
--   The **value** of the POMDP from the initial belief $p_1$ is the supremum of the long-run payoff over all pure strategies:
--
--   $$v_\infty(p_1)=\sup_{\sigma\in\Sigma}\gamma^{p_1}_\infty(\sigma),$$
--
--   where $\Sigma$ is the set of all maps $\sigma:\bigcup_{m\ge1}\mathcal H_m\to\mathcal A$.
--
--   **Formalization Note** The supremum ranges over all functions `List (A × S) → A`; this set is nonempty and the payoffs are at most $1$, so the real supremum is genuine (checked in the verification file).
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, §2.1, p.2

import Mathlib
import Definitions.Def_FiniteMemPOMDP_gammaInf

namespace FiniteMemPOMDP

variable {K A S : Type} [Fintype K] [Fintype A] [Fintype S] [Nonempty A] [Nonempty S]

/-- **The long-run value `v∞(p1)`.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, §2.1, p.2:
"v∞(p1) := sup_{σ∈Σ} γ^{p1}_∞(σ)", where Σ is the set of (pure) strategies
"σ: ∪m≥1 Hm → A".

`vInf Γ p` is the supremum of `gammaInf Γ p σ` over **all** pure strategies
`σ : List (A × S) → A`.

**Formalization Note** The index type is nonempty (`A` is nonempty, so constant strategies exist)
and `gammaInf ≤ 1`, so the real `⨆` is the true supremum, not a junk value (checked in the
mission's verification file). -/
noncomputable def vInf (Γ : POMDP K A S) (p : stdSimplex ℝ K) : ℝ :=
  ⨆ σ : List (A × S) → A, gammaInf Γ p σ

end FiniteMemPOMDP


