-- Prove2me | Definitions.Def_TIEMaximin_Shares
-- name    : TIEMaximin_Shares
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:38:32.422935+00:00
-- url     : https://prove2.me/theorems/6baaab22-978c-4de1-abd3-3a2a3e4749dd
-- title:
--   Truncated proportional share and maximin share
-- statement:
--   For an agent with additive item values $u$, the **truncated proportional share** among $n$ agents is
--
--   $$\mathrm{TPS}_n(u,M)=\max\Bigl\{t\ge 0:\ \frac1n\sum_{g\in M}\min\{u(g),t\}=t\Bigr\},$$
--
--   and the **maximin share** is $\mathrm{MMS}_n(u,M)=\max_{A}\min_{j}u(A_j)$, the maximum over all allocations $A$ of the least-valued bundle.
--
--   Both shares depend only on the agent's own valuation; the mission's goal bounds realized values from below by one sixth of these shares.
--
--   **Formalization Note** The TPS is the published `AnyPriceShare.Bidding.tps` at entitlement $1/n$ over all goods, a supremum over the same equation without the constraint $t\ge0$. For $n\ge1$ and $u\ge0$ the two sets differ only by negative solutions, which exist only for $m=n$, and $0$ lies in both, so the suprema coincide; `lemma_2_5` states that the value is the greatest element of the set above. The MMS is the published `LittleCharity.MMS.mms` with the additive set function. Statements assume $n\ge1$.
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Definitions 2.3, 2.4, eq. (2), p.7

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_LittleCharity_MMS_Setting

namespace TIEMaximin

/-- **Truncated proportional share** (Definition 2.4, eq. (2), p.7):
`TPS_n(u, M) = max { t ≥ 0 : (1/n) · Σ_{g∈M} min{u(g), t} = t }` for an agent with item values `u`.

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Definition 2.4, eq. (2), p.7.

**Formalization Note.** This is the published `AnyPriceShare.Bidding.tps` with entitlement
`β = 1/n` over all goods: `sSup {z | (1/n) · Σ_g min(u g, z) = z}`. That set has no `z ≥ 0`
constraint; for `n ≥ 1` and `u ≥ 0` it differs from the paper's set only by negative `z`, which solve
the equation only when `m = n`, and `0` is in both sets, so both suprema coincide. The set is
bounded by `u(M)/n`, so the supremum is a maximum (Lemma 2.5). Statements assume `0 < n` and `u ≥ 0`. -/
noncomputable def tps (n : ℕ) {m : ℕ} (u : Fin m → ℝ) : ℝ :=
  AnyPriceShare.Bidding.tps (1 / (n : ℝ)) u Finset.univ

/-- **Maximin share** (Definition 2.3, p.7): `MMS_n(u, M) = max_{A∈𝒜} min_{j∈N} u(A_j)` for an
agent with additive item values `u`, partitioning all goods into `n` bundles.

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Definition 2.3, p.7.

**Formalization Note.** This is the published `LittleCharity.MMS.mms` with the additive set
function `S ↦ Σ_{g∈S} u g`, `k = n` bundles and `S = M` (all goods); the maximum is a supremum over
the finitely many maps `Fin m → Fin n`. Statements assume `0 < n`. -/
noncomputable def mmsOf (n : ℕ) {m : ℕ} (u : Fin m → ℝ) : ℝ :=
  LittleCharity.MMS.mms (fun S => ∑ g ∈ S, u g) n Finset.univ

end TIEMaximin


