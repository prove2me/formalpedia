-- Prove2me | Definitions.Def_UnbiasedTimeAvg_coupledChain
-- name    : UnbiasedTimeAvg_coupledChain
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:34.846144+00:00
-- url     : https://prove2.me/theorems/4a47954f-2d41-4741-8093-39cd9114da21
-- title:
--   The coupled chains $X_{i,m}$
-- statement:
--   For integers $m$ and $i\ge -m$, the paper defines (2.2)
--   $$X_{i,m}:=G_{i+m}\big(X_0;U_{-m},U_{-m+1},\dots,U_{i-1}\big),$$
--   the chain started from the deterministic point $X_0=x_0$ at time $-m$ and observed at time $i$. Thus $X_{i,0}=X_i$ is the chain of (1.1), $X_{-m,m}=X_0$ and $X_{i+1,m}=g(X_{i,m},U_i)$ (2.3). For $i,m\ge0$ the chains $X_{i}$ and $X_{i,m}$ share the last $i$ noise variables $U_0,\dots,U_{i-1}$; this coupling is what Assumption A1 quantifies.
--
--   **Formalization Note** `coupledChain g x₀ U i m` is the driven chain started at time $-m$ after $(i+m)$ steps. Only $i\ge -m$ is meaningful; for $i<-m$ the value is $x_0$ (zero steps), a case no statement uses.
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), §2.1, (2.2)–(2.3), p.4

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_drivenChain

namespace UnbiasedTimeAvg

/-- **The coupled chains `X_{i,m}`.** Kahalé, arXiv:2209.09581v1, (2.2), p.4: for `m ∈ ℤ` and
`i ≥ −m`, `X_{i,m} := G_{i+m}(X₀; U_{−m}, U_{−m+1}, …, U_{i−1})`.

`coupledChain g x₀ U i m` is the chain started from `x₀` at time `−m`, observed at time `i`, i.e.
after `i + m` steps driven by `U_{−m}, …, U_{i−1}`. In particular `X_{i,0} = X_i` (the chain of
(1.1)), `X_{−m,m} = x₀` and `X_{i+1,m} = g(X_{i,m}, U_i)` ((2.3), p.4).

**Formalization Note.** `i` and `m` are integers. The value is only meaningful for `i ≥ −m`, the
range of (2.2); for `i < −m` the number of steps `(i + m).toNat` is `0` and the value is `x₀`, a
case no statement of the mission uses. The chain `X_i`, `i ∈ ℕ`, is `coupledChain g x₀ U i 0`. -/
def coupledChain {Ω F F' : Type*} (g : F → F' → F) (x₀ : F) (U : ℤ → Ω → F') (i m : ℤ) :
    Ω → F :=
  drivenChain g x₀ U (-m) (i + m).toNat

end UnbiasedTimeAvg


