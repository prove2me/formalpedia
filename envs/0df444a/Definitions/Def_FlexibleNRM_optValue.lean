-- Prove2me | Definitions.Def_FlexibleNRM_optValue
-- name    : FlexibleNRM_optValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:26:35.079799+00:00
-- url     : https://prove2.me/theorems/471cf457-f5dc-47f8-b7ec-1d6a5a19a8b8
-- title:
--   The optimal value function $J_t(x)$, Eq. (2)
-- statement:
--   The value functions are given by the dynamic program
--   $$J_t(x)=\max_{S\subseteq\mathcal J}\Big\{\sum_{j\in\mathcal J}\phi_{jt}(S)\,\mathbf 1_{(\mathcal F(x+e_j)\ne\emptyset)}\big[f_j+J_{t+1}(x+e_j)-J_{t+1}(x)\big]\Big\}+J_{t+1}(x),$$
--   with the boundary condition $J_{T+1}=0$. The optimal total expected revenue is $J_1(0)$.
--
--   **Formalization Note** This is the second line of (2); the first line is misprinted. The recursion returns $0$ for every $t>T$ and is read only at $t\ge1$.
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, Eq. (2), p.8; proof of Theorem 4.1, p.18

import Mathlib
import Definitions.Def_FlexibleNRM_assortmentValue

namespace FlexibleNRM

/-- The **optimal value function** `J_t(x)`, the second line of Eq. (2):
`J_t(x) = max_{S ⊆ J} { ∑_j φ_jt(S) 1(F(x + e_j) ≠ ∅) [f_j + J_{t+1}(x + e_j) − J_{t+1}(x)] }
  + J_{t+1}(x)`, with `J_{T+1} = 0`.
The optimal total expected revenue is `J_1(0)` (proof of Theorem 4.1, p.18).

Zhu, Topaloglu, manuscript of November 16, 2022, Eq. (2), p.8.

**Formalization Note** The first line of (2) is misprinted (its bracket shows `F(x + e_j)` with no
indicator, and a sum over `j ∈ S`), so this is the second line, which the paper uses everywhere
else. The recursion runs on `T + 1 − t`, returns `0` for every `t > T`, and is read only at
`t ≥ 1`. The maximum over `S ⊆ J` is a `Finset.sup'` over all `Finset (Fin n)`. -/
noncomputable def optValue {n m r : ℕ} (N : Network n m r) (t : ℕ) (x : Fin n → ℕ) : ℝ :=
  if _h : t ≤ N.T then
    Finset.univ.sup' Finset.univ_nonempty
        (fun S => assortmentValue N t (fun z => optValue N (t + 1) z) x S) +
      optValue N (t + 1) x
  else 0
termination_by N.T + 1 - t
decreasing_by all_goals omega

end FlexibleNRM


