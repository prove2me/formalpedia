-- Prove2me | Definitions.Def_StrategyproofMultidim_EFF
-- name    : StrategyproofMultidim_EFF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:19.245844+00:00
-- url     : https://prove2.me/theorems/4f1a0845-1a41-4e1b-a144-a2cec669d402
-- title:
--   Efficiency (EFF)
-- statement:
--   A mechanism is **efficient** if at every positive profile $v$ its decision matrix is in $\mathcal D$ and maximizes total value:
--   $$\sum_{i\in N} d_i(v)^{\top}v_i=\max_{\hat d\in\mathcal D}\sum_{i\in N}\hat d_i^{\top}v_i .$$
--
--   **Formalization Note** The maximum is written as feasibility of $d(v)$ together with $\sum_i d_i(v)^\top v_i\ge\sum_i \hat d_i^\top v_i$ for every feasible $\hat d$.
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), Definition 6, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_StrategyproofMultidim_Mechanism
import Definitions.Def_StrategyproofMultidim_PosProfile
import Definitions.Def_StrategyproofMultidim_IsFeasible
import Definitions.Def_StrategyproofMultidim_bundleValue

namespace StrategyproofMultidim

/-- **Efficiency (EFF)** (Definition 6, p.15).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.15: "Definition 6. A mechanism μᵉ is efficient (EFF) if for all v ∈ 𝒱,
∑ᵢ∈N dᵢ^{μᵉ} vᵢ = max_{d̂∈𝒟} ∑ᵢ∈N d̂ᵢvᵢ."

At every positive profile the chosen decision matrix is feasible and its total value
`∑ᵢ dᵢᵀvᵢ` is at least that of every feasible decision matrix, i.e. it attains the maximum over
`𝒟`.

**Formalization Note.** "= max over 𝒟" is written as feasibility of `μ.q v` plus `≥` against
every feasible `e`; the two are equivalent. -/
def EFF {n m : ℕ} (μ : Mechanism n m) : Prop :=
  ∀ v, PosProfile v → IsFeasible (μ.q v) ∧
    ∀ e : Fin n → Fin m → Bool, IsFeasible e →
      ∑ t, bundleValue (e t) (v t) ≤ ∑ t, bundleValue (μ.q v t) (v t)

end StrategyproofMultidim


