-- Prove2me | Definitions.Def_StrategyproofMultidim_IsMechanism
-- name    : StrategyproofMultidim_IsMechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:18.327295+00:00
-- url     : https://prove2.me/theorems/e161742c-cd66-44bb-b884-01381bd0266f
-- title:
--   $\mu$ maps $\mathcal V$ into $\mathcal D\times\mathbb R^N_+$
-- statement:
--   A mechanism $\mu=(d,p)$ is a function $\mu:\mathcal V\to\mathcal D\times\mathbb R^N_+$: at every positive profile $v$ the decision matrix $d(v)$ sells each object to at most one buyer, and every price $p_i(v)$ is non-negative.
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), §3, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_StrategyproofMultidim_Mechanism
import Definitions.Def_StrategyproofMultidim_PosProfile
import Definitions.Def_StrategyproofMultidim_IsFeasible

namespace StrategyproofMultidim

/-- **`μ` maps `𝒱` into `𝒟 × ℝᴺ₊`** (§3, p.5).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.5: "μ : 𝒱 ⟶ 𝒟 × ℝᴺ₊."

At every positive profile the decision matrix is feasible (each object to at most one buyer) and
every price is non-negative.

**Formalization Note.** Column sums at most 1 (see `IsFeasible`). Only positive profiles are
constrained. -/
def IsMechanism {n m : ℕ} (μ : Mechanism n m) : Prop :=
  ∀ v, PosProfile v → IsFeasible (μ.q v) ∧ ∀ i, 0 ≤ μ.t i v

end StrategyproofMultidim


