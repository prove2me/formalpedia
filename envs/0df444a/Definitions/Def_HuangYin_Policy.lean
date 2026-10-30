-- Prove2me | Definitions.Def_HuangYin_Policy
-- name    : HuangYin_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:39:23.46638+00:00
-- url     : https://prove2.me/theorems/82f890d4-b15b-4f43-8577-951c4ae0ff2b
-- title:
--   Two-period selling policies
-- statement:
--   A selling policy is one of two kinds:
--
--   1. a **probabilistic (opaque) policy** $(p_1,p_2,\xi_1,\xi_2)$: in period $t$ the firm sells the opaque product at price $p_t$ and offers product $H$ with probability $\xi_t$;
--   2. a **transparent policy** $(m_1,m_2,p_1,p_2)$: in period $t$ the firm sells product $m_t$ openly at price $p_t$.
--
--   **Formalization Note** A policy that is opaque in one period and transparent in the other is not included: the paper compares these two families only.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), §3.2, p. 9, and §3.3, p. 11

import Mathlib
import Definitions.Def_HuangYin_Product

namespace HuangYin

/-- **A two-period selling policy** (§3.2, p. 9, and §3.3, p. 11; unnumbered).
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020).

* `opaque p1 p2 ξ1 ξ2` — probabilistic selling (§3.2): in period `t` the firm sells the opaque
  product at price `pt` and offers product `H` with probability `ξt`;
* `transparent m1 m2 p1 p2` — transparent selling (§3.3): in period `t` the firm sells product
  `mt` openly at price `pt`.

**Formalization Note.** Mixed sequences (opaque in one period, transparent in the other) are not
policies: the paper compares the two families only. -/
inductive Policy
  | opaque (p1 p2 ξ1 ξ2 : ℝ)
  | transparent (m1 m2 : Product) (p1 p2 : ℝ)

end HuangYin


