-- Prove2me | Definitions.Def_MWMSLagrange_ubOnHand
-- name    : MWMSLagrange_ubOnHand
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:00:38.424069+00:00
-- url     : https://prove2.me/theorems/f53c2dce-551e-4004-a9da-febea4c8636b
-- title:
--   Base-stock inventory $I_{i,t}$ with unlimited warehouses
-- statement:
--   Under the base-stock policy with order-up-to levels $y_{i,t}$ and unlimited warehouse inventory, store $i$ orders $(y_{i,t}-I_{i,t})^+$ in period $t$, so its post-order level is $\max(y_{i,t},I_{i,t})$ and
--
--   $$I_{i,1}=0,\qquad I_{i,t+1}=\big(\max(y_{i,t},I_{i,t})-D_{i,t}\big)^+ .$$
--
--   This is the inventory $I_{i,t}$ in the complementary slackness conditions (3.7), in $f_j$ (p.24) and in Lemma 7.
--
--   **Formalization Note** Time is indexed by $\mathbb N$ from $0$; values beyond the horizon are $0$ and unused.
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), pp.12–13 (base-stock policy), (3.7) "I_{i,t} here denotes the inventory level corresponding to policy {y*_{i,t}(λ*)}"

import Mathlib

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), pp.12–13 and p.21: the
on-hand inventory `I_{i,t}` of store `i` under the base-stock policy with (possibly
non-stationary) order-up-to levels `y_{i,t}` in the system where warehouses have unlimited
inventory: `I_{i,1} = 0` and `I_{i,t+1} = (max(y_{i,t}, I_{i,t}) − D_{i,t})^+`.

**Formalization Note.** The store orders `(y_{i,t} − I_{i,t})^+`, so its post-order level is
`max(y_{i,t}, I_{i,t})`; inventory is never removed (`y^π ≥ I^π` in (2.1)). Time is `ℕ` with
`0` the first period; values at indices `t > T` are `0` and are never used. This is the
`I_{i,t}` of (3.7), of `f_j` (p.24) and of Lemma 7. -/
noncomputable def ubOnHand {N T : ℕ} (y : Fin N → Fin T → ℝ) (ω : Fin N × Fin T → ℝ)
    (i : Fin N) : ℕ → ℝ
  | 0 => 0
  | t + 1 =>
    if ht : t < T then max (max (y i ⟨t, ht⟩) (ubOnHand y ω i t) - ω (i, ⟨t, ht⟩)) 0 else 0

end MWMSLagrange


