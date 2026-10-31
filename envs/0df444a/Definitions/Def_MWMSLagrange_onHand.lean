-- Prove2me | Definitions.Def_MWMSLagrange_onHand
-- name    : MWMSLagrange_onHand
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:36.683731+00:00
-- url     : https://prove2.me/theorems/8d834e78-9b95-4c5c-a931-6f9ade8629e2
-- title:
--   On-hand inventory $I_{i,t}$ under shipments $z$
-- statement:
--   Given shipments $z_{i,j,t}(\omega)\ge0$ from warehouse $j$ to store $i$ in period $t$, the on-hand inventory of store $i$ at the beginning of period $t$ evolves under lost sales and zero lead time as
--
--   $$I_{i,1}=0,\qquad I_{i,t+1}=\Big(I_{i,t}+\sum_{j\in\mathcal M_i}z_{i,j,t}-D_{i,t}\Big)^+ .$$
--
--   This is the first constraint of (2.1), $I_{i,t+1}=(y_{i,t}-D_{i,t})^+$, with $y_{i,t}$ the post-delivery level.
--
--   **Formalization Note** Time is indexed by $\mathbb N$ from $0$ (the paper's period 1); values beyond the horizon are $0$ and unused.
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), §2, pp.7–8, (2.1) first constraint

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_Instance_Mset

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), §2, pp.7–8, (2.1): the
on-hand inventory `I_{i,t}` of store `i` at the beginning of period `t` under the shipments
`z_{i,j,t}` on the demand path `ω`: `I_{i,1} = 0` and, with lost sales,
`I_{i,t+1} = (I_{i,t} + ∑_{j ∈ 𝓜_i} z_{i,j,t} − D_{i,t})^+`.

**Formalization Note.** Shipments are a function `z t ω i j` (from warehouse `j` to store `i`
in period `t` on path `ω`); the paper's `y^π_{i,t} = I_{i,t} + ∑_j z_{i,j,t}` and
`ρ^π_{i,j,t} = z_{i,j,t} / ∑_j z_{i,j,t}` are recovered from it. Time is `ℕ` with `0` the
first period; `onHand I z ω i t` for `t < T` is the paper's `I_{i,t+1}`. Values at indices
`t > T` are `0` and are never used. -/
noncomputable def onHand {M N T : ℕ} (I : Instance M N)
    (z : Fin T → (Fin N × Fin T → ℝ) → Fin N → Fin M → ℝ) (ω : Fin N × Fin T → ℝ)
    (i : Fin N) : ℕ → ℝ
  | 0 => 0
  | t + 1 =>
    if ht : t < T then
      max (onHand I z ω i t + ∑ j ∈ I.Mset i, z ⟨t, ht⟩ ω i j - ω (i, ⟨t, ht⟩)) 0
    else 0

end MWMSLagrange


