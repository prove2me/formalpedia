-- Prove2me | Definitions.Def_StrategyproofMultidim_AN
-- name    : StrategyproofMultidim_AN
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:13:16.484878+00:00
-- url     : https://prove2.me/theorems/fc804a8f-818e-43fe-a174-b9738595f661
-- title:
--   Anonymity in welfare (AN)
-- statement:
--   For a permutation $\pi$ of the buyers, the relabelled profile is $\pi v:=(v_{\pi^{-1}(t)})_{t=1}^n$, so that row $\pi(i)$ of $\pi v$ is $v_i$. A mechanism satisfies **anonymity in welfare** if for every positive profile $v$, every buyer $i$ and every permutation $\pi$,
--   $$u(\mu_i(v);v_i)=u(\mu_{\pi i}(\pi v);(\pi v)_{\pi i}),$$
--   i.e. a buyer's utility does not depend on its identity.
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), Definition 3, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_StrategyproofMultidim_util
import Definitions.Def_StrategyproofMultidim_PosProfile

namespace StrategyproofMultidim

/-- **Anonymity in welfare (AN)** (Definition 3, p.7).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.7: "Definition 3. A mechanism μ satisfies anonymity in welfare (AN) if ∀ i ∈ N,
∀ v ∈ 𝒱 and all bijections π : N ↦ N, u(μᵢ(v); vᵢ) = u(μ_{πi}(πv); (πv)_{πi}) where
πv := (v_{π⁻¹(t)})ⁿₜ₌₁."

Relabelling the buyers by a permutation `π` does not change any buyer's utility: buyer `i` at
`v` gets the same utility as buyer `π i` at the relabelled profile `πv`, whose row `π i` is `vᵢ`.

**Formalization Note.** `πv` is `fun t => v (π.symm t)`, so `(πv)_{πi} = vᵢ`; the utility on
the right is therefore evaluated at the true valuation `v i`. -/
def AN {n m : ℕ} (μ : Mechanism n m) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (v : Fin n → Fin m → ℝ), PosProfile v → ∀ i,
    util μ v i (v i) = util μ (fun t => v (π.symm t)) (π i) (v i)

end StrategyproofMultidim


