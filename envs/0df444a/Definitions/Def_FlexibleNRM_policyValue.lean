-- Prove2me | Definitions.Def_FlexibleNRM_policyValue
-- name    : FlexibleNRM_policyValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:26:48.455204+00:00
-- url     : https://prove2.me/theorems/cd8c7c5e-d8ad-467c-9bea-35d14e42b8c1
-- title:
--   The value functions $U_t(x)$ of a policy, Eq. (11)
-- statement:
--   Let $S_t(x)$ be the assortment that a policy offers at period $t$ in state $x$. Its value functions are
--   $$U_t(x)=\sum_{j\in\mathcal J}\phi_{jt}(S_t(x))\,\mathbf 1_{(\mathcal F(x+e_j)\ne\emptyset)}\big[f_j+U_{t+1}(x+e_j)-U_{t+1}(x)\big]+U_{t+1}(x),$$
--   with the boundary condition $U_{T+1}=0$. For the approximate policy, the total expected revenue is $U_1(0)$.
--
--   **Formalization Note** The definition takes any assignment of assortments to periods and states.
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, Eq. (11), p.16; proof of Theorem 4.1, p.18

import Mathlib
import Definitions.Def_FlexibleNRM_assortmentValue

namespace FlexibleNRM

/-- The **value functions of a policy**, Eq. (11):
`U_t(x) = ∑_j φ_jt(S_t(x)) 1(F(x + e_j) ≠ ∅) [f_j + U_{t+1}(x + e_j) − U_{t+1}(x)] + U_{t+1}(x)`,
with `U_{T+1} = 0`. For the approximate policy, the total expected revenue is `U_1(0)` (proof of
Theorem 4.1, p.18).

Zhu, Topaloglu, manuscript of November 16, 2022, Eq. (11), p.16.

**Formalization Note** Defined for any `Sapp : ℕ → (Fin n → ℕ) → Finset (Fin n)`, where `Sapp t x`
is the assortment offered at period `t` in state `x`. The recursion runs on `T + 1 − t` and returns
`0` for every `t > T`. -/
noncomputable def policyValue {n m r : ℕ} (N : Network n m r)
    (Sapp : ℕ → (Fin n → ℕ) → Finset (Fin n)) (t : ℕ) (x : Fin n → ℕ) : ℝ :=
  if _h : t ≤ N.T then
    assortmentValue N t (fun z => policyValue N Sapp (t + 1) z) x (Sapp t x) +
      policyValue N Sapp (t + 1) x
  else 0
termination_by N.T + 1 - t
decreasing_by all_goals omega

end FlexibleNRM


