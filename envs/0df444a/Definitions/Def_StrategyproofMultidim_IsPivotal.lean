-- Prove2me | Definitions.Def_StrategyproofMultidim_IsPivotal
-- name    : StrategyproofMultidim_IsPivotal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:13:18.27411+00:00
-- url     : https://prove2.me/theorems/874183f9-a033-4cc2-a9c4-66a858b455e2
-- title:
--   The Pivotal mechanism (Definition 7)
-- statement:
--   A mechanism is **the Pivotal mechanism** if for every positive profile $v$ and buyer $i$:
--
--   1. its decisions are efficient: $\sum_{t\in N} d_t(v)^{\top}v_t=\max_{\hat d\in\mathcal D}\sum_{t\in N}\hat d_t^{\top}v_t$;
--   2. buyer $i$ pays the externality it imposes on the others:
--   $$p_i(v)=\max_{\hat d\in\mathcal D}\sum_{t\neq i}\hat d_t^{\top}v_t-\sum_{t\neq i}d_t(v)^{\top}v_t .$$
--
--   Any tie-breaking among efficient decisions is allowed.
--
--   **Formalization Note** The maximum in (2) is expressed by saying that $p_i(v)+\sum_{t\neq i}d_t(v)^\top v_t$ is the greatest element of $\{\sum_{t\neq i}\hat d_t^\top v_t:\hat d\in\mathcal D\}$. The sign of the payment is that of Definition 7; the sufficiency proof of Theorem 4 on p.15 prints it reversed.
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), Definition 7, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_StrategyproofMultidim_EFF

namespace StrategyproofMultidim

/-- **The Pivotal mechanism** (Definition 7, p.15).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.15: "Definition 7. A mechanism μᴾ is said to be the Pivotal mechanism if for all
i ∈ N and all v ∈ 𝒱, ∑ₜ∈N dₜ^{μᴾ} vₜ = max_{d̂∈𝒟} ∑ₜ∈N d̂ₜvₜ and
pᵢ^{μᴾ}(v) = max_{d̂∈𝒟} ∑_{t∈N, t≠i} d̂ₜvₜ − ∑_{t∈N, t≠i} dₜ^{μᴾ} vₜ."

`IsPivotal μ`: the decisions are efficient (`EFF`), and at every positive profile each buyer
`i` pays the maximal total value the other buyers could obtain over feasible decision matrices,
minus the value the other buyers obtain at `μ`'s decision. The first is written as: the number
`pᵢ(v) + ∑_{t≠i} dₜ(v)ᵀvₜ` is the greatest element of `{∑_{t≠i} d̂ₜᵀvₜ : d̂ ∈ 𝒟}`.

**Formalization Note.** Any tie-breaking among efficient decisions is allowed. The sign of the
payment is Definition 7's; the sufficiency proof of Theorem 4 (p.15) prints it reversed. -/
def IsPivotal {n m : ℕ} (μ : Mechanism n m) : Prop :=
  EFF μ ∧ ∀ v, PosProfile v → ∀ i,
    IsGreatest {s : ℝ | ∃ e : Fin n → Fin m → Bool, IsFeasible e ∧
        s = ∑ t ∈ Finset.univ.erase i, bundleValue (e t) (v t)}
      (μ.t i v + ∑ t ∈ Finset.univ.erase i, bundleValue (μ.q v t) (v t))

end StrategyproofMultidim


