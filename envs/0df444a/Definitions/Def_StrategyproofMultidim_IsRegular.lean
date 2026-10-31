-- Prove2me | Definitions.Def_StrategyproofMultidim_IsRegular
-- name    : StrategyproofMultidim_IsRegular
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:19.453925+00:00
-- url     : https://prove2.me/theorems/1e19e10a-67b7-44bf-9461-2d9ea5b00716
-- title:
--   Regular mechanism
-- statement:
--   The paper studies only **regular** mechanisms, which satisfy:
--
--   1. any buyer who is not allotted any object pays zero price: if $d_i^k(v)=0$ for all $k$, then $p_i(v)=0$;
--   2. for every positive profile $v$, buyer $i$ and object $k$ there is $\epsilon>0$ such that changing $v_i^k$ alone to any positive $w$ with $|w-v_i^k|<\epsilon$ does not change buyer $i$'s decisions $d_i^l$ on the other objects $l\neq k$.
--
--   Property (ii) is essential for the threshold characterization (Theorem 2).
--
--   **Formalization Note** $\epsilon$ may depend on $v,i,k$; the perturbed value is required to be positive so that the perturbed profile stays in $\mathcal V$.
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), §3, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_StrategyproofMultidim_Mechanism
import Definitions.Def_StrategyproofMultidim_PosProfile

namespace StrategyproofMultidim

/-- **Regular mechanism** (§3, p.6), a standing assumption on every mechanism of the paper.
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.6: "In this paper, we focus on regular direct mechanisms which satisfy two specific
properties: (i): any buyer who is not allotted any object pays zero price, and (ii): for any
buyer i, any object k and any valuation v, there exists an ϵᵢᵏ(v) > 0 such that for any
wᵢᵏ ∈ (vᵢᵏ − ϵᵢᵏ(v), vᵢᵏ + ϵᵢᵏ(v)), dᵢ⁻ᵏ(v) = dᵢ⁻ᵏ((wᵢᵏ, vᵢ⁻ᵏ), v₋ᵢ)."

(i) at a positive profile, a buyer who wins no object pays `0`; (ii) at a positive profile `v`,
for every buyer `i` and object `k` there is `ε > 0` such that replacing `vᵢᵏ` alone by any
positive `w` with `|w − vᵢᵏ| < ε` leaves buyer `i`'s decisions on every other object `l ≠ k`
unchanged (`dᵢ⁻ᵏ` is buyer `i`'s decision vector without coordinate `k`, p.6).

**Formalization Note.** `ε` may depend on `v`, `i`, `k`. The perturbed value is required to be
positive so that the perturbed profile stays in `𝒱`. -/
def IsRegular {n m : ℕ} (μ : Mechanism n m) : Prop :=
  (∀ v, PosProfile v → ∀ i, (∀ k, μ.q v i k = false) → μ.t i v = 0) ∧
  (∀ v, PosProfile v → ∀ i k, ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℝ, 0 < w → |w - v i k| < ε →
    ∀ l, l ≠ k → μ.q (Function.update v i (Function.update (v i) k w)) i l = μ.q v i l)

end StrategyproofMultidim


