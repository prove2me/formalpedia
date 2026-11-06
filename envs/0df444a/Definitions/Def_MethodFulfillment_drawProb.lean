-- Prove2me | Definitions.Def_MethodFulfillment_drawProb
-- name    : MethodFulfillment_drawProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:48.046488+00:00
-- url     : https://prove2.me/theorems/555e83ec-92be-4431-8ac4-afed42b2c2f3
-- title:
--   Method draw of step 1 of Algorithm 1
-- statement:
--   When an order of type $q$ arrives in period $t$, step 1 of Algorithm 1 draws a method $m\in M(q)$ with probability
--   $$\frac{y^t_m}{p_t(q)}=\frac{y_m}{p_a(q)},\qquad y^t_m=\frac{y_m\,p_t(q)}{p_a(q)}\ \text{ by (10)} .$$
--   When no order arrives, the empty method is drawn with probability one.
--
--   **Formalization Note** When $p_a(q)=0$ the division returns $0$; then $p_t(q)=0$ for every $t$, so the order type never arrives and this value is never used.
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), Algorithm 1, p.13; (10), p.11

import Mathlib
import Definitions.Def_MethodFulfillment_Instance
import Definitions.Def_MethodFulfillment_pa

namespace MethodFulfillment

/-- The draw of step 1 of Algorithm 1 (Amil, Makhdoumi & Wei, manuscript, PDF sha256 197c13b9…,
Algorithm 1, p.13, with (10), p.11): when `q` arrives, method `m ∈ M(q)` is drawn with probability
`y^t_m / p_t(q) = y_m / pa(q)`; when no order arrives, the empty method is "drawn" with
probability one.

**Formalization Note.** By (10), `y^t_m / p_t(q) = (y_m p_t(q) / pa(q)) / p_t(q) = y_m / pa(q)`,
which does not depend on `t`. When `pa q = 0` the division returns `0`; then `p t q = 0` for every
`t`, so the type `q` never arrives and the value is never used. -/
noncomputable def drawProb {I K Q : Type} [DecidableEq I] [DecidableEq K] {T : ℕ}
    (P : Instance I K Q T) (y : Q → Finset (I × K) → ℝ) : Option Q → Finset (I × K) → ℝ
  | none, m => if m = ∅ then 1 else 0
  | some q, m => if m ∈ P.methods q then y q m / pa P q else 0

end MethodFulfillment


