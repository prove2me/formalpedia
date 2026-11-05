-- Prove2me | Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_exerciseT
-- name    : BauerleRiederMDP_AmericanPut_BinomialMarket_exerciseT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:31.385214+00:00
-- url     : https://prove2.me/theorems/cd33695b-7ac6-43d7-ab09-92bc5253d50a
-- title:
--   Operator $\mathcal T_f$ of a stationary exercise rule $f=1_A$
-- statement:
--   In the stopping problem of the put written as a Markov Decision Model (exercise earns $(K-x)^+$ and ends the problem, continuation earns nothing and moves by $Q^X$), the operator of the stationary decision rule $f=1_A$ is
--   $$\mathcal T_f v(x)=\begin{cases}(K-x)^+, & x\in A,\\ \beta\big(q\,v(xu)+(1-q)\,v(xd)\big), & x\notin A.\end{cases}$$
--   Theorem 11.1.3 d) uses it for $f^*=1_{E^*}$.
--
--   **Formalization Note** A decision rule $f:E\to\{0,1\}$ is represented by its exercise set $A=\{f=1\}$.
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, §11.1, p.332, PDF 340 (the stopping MDP) and Theorem 11.1.3 d), p.337, PDF 345

import Mathlib
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_q
import Definitions.Def_BauerleRiederMDP_AmericanPut_BinomialMarket_beta
import Definitions.Def_fd04_putPayoff
open FinancialDerivatives.FD04 (putPayoff)

namespace BauerleRiederMDP.AmericanPut

open Classical in
/-- The **operator `𝒯_f` of a stationary exercise rule** `f = 1_A` in the stopping problem of the put
(Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 11.1.3 d), p.337,
PDF 345, with `f* = 1_{E*}`; the stopping problem as a Markov Decision Model, §10.1 and §11.1, p.332, PDF 340:
action `1` exercises and earns `g(x) = (K − x)⁺`, action `0` continues with `c ≡ 0` and the kernel
`Q^X(·|x) = q δ_{xu} + (1 − q) δ_{xd}`):
`𝒯_f v(x) = (K − x)⁺` if `f(x) = 1` (i.e. `x ∈ A`), and `𝒯_f v(x) = β(q v(xu) + (1 − q) v(xd))` if `f(x) = 0`.

**Formalization Note.** A decision rule `f : E → {0, 1}` is represented by its exercise set `A = {f = 1}`.
After exercise the process moves to the absorbing cemetery state with reward `0`, which is why no
continuation term appears on `A`. -/
noncomputable def BinomialMarket.exerciseT (M : BinomialMarket) (K : ℝ) (A : Set ℝ) (v : ℝ → ℝ)
    (x : ℝ) : ℝ :=
  if x ∈ A then putPayoff K x else M.beta * (M.q * v (x * M.u) + (1 - M.q) * v (x * M.d))

end BauerleRiederMDP.AmericanPut


