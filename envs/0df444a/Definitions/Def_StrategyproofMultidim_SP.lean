-- Prove2me | Definitions.Def_StrategyproofMultidim_SP
-- name    : StrategyproofMultidim_SP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:13:15.17625+00:00
-- url     : https://prove2.me/theorems/43b9459d-a8e1-4ec7-b824-74fef7bbd3f4
-- title:
--   Strategyproofness (SP)
-- statement:
--   A mechanism is **strategyproof** if truth-telling is optimal for every buyer whatever the others report: for every positive profile $v$, every buyer $i$ and every positive misreport $v_i'$,
--   $$u(\mu_i(v);v_i)\ \ge\ u(\mu_i(v_i',v_{-i});v_i).$$
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), Definition 1, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_StrategyproofMultidim_util
import Definitions.Def_StrategyproofMultidim_PosProfile

namespace StrategyproofMultidim

/-- **Strategyproofness (SP)** (Definition 1, p.7).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.7: "Definition 1. A mechanism μ satisfies strategyproofness (SP) if ∀ i ∈ N,
∀ v, v′ ∈ 𝒱 such that v₋ᵢ = v′₋ᵢ, u(μᵢ(v); vᵢ) ≥ u(μᵢ(v′); vᵢ)."

For every positive profile `v`, buyer `i` and positive misreport `x`, buyer `i`'s utility (at
the true valuation `vᵢ`) from reporting `x` is at most that from reporting `vᵢ`.

**Formalization Note.** `v′` with `v′₋ᵢ = v₋ᵢ` is `Function.update v i x`. -/
def SP {n m : ℕ} (μ : Mechanism n m) : Prop :=
  ∀ v, PosProfile v → ∀ (i : Fin n) (x : Fin m → ℝ), (∀ k, 0 < x k) →
    util μ (Function.update v i x) i (v i) ≤ util μ v i (v i)

end StrategyproofMultidim


