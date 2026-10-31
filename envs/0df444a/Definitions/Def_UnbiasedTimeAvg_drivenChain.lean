-- Prove2me | Definitions.Def_UnbiasedTimeAvg_drivenChain
-- name    : UnbiasedTimeAvg_drivenChain
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:18:37.523078+00:00
-- url     : https://prove2.me/theorems/0345becd-916f-449a-a9b4-a3bd002c2fa5
-- title:
--   The chain driven by i.i.d. noise from an integer starting time
-- statement:
--   Let $F$ and $F'$ be measurable spaces, $g:F\times F'\to F$ a map, $x_0\in F$ a deterministic starting point, and $(U_i)_{i\in\mathbb Z}$ a family of $F'$-valued random variables on a probability space $\Omega$. Following §2.1 of the paper, set $G_0(x):=x$ and
--   $$G_{i+1}(x;u_0,\dots,u_i):=g\big(G_i(x;u_0,\dots,u_{i-1}),u_i\big).$$
--   For an integer starting time $s$ and $n\ge0$, the **driven chain** is
--   $$\mathrm{drivenChain}(s,n)(\omega)=G_n\big(x_0;U_s(\omega),U_{s+1}(\omega),\dots,U_{s+n-1}(\omega)\big),$$
--   the state reached after $n$ updates $x\mapsto g(x,U_t)$ at the times $t=s,\dots,s+n-1$.
--
--   It is the common building block of the chain $X_i$ (start at time $0$) and of its copies started in the past.
--
--   **Formalization Note** The recursion is on the number of steps $n\in\mathbb N$; the noise is indexed by $\mathbb Z$ so that a chain can be started at any integer time.
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), §2.1, p.4 (definition of G_i)

import Mathlib

namespace UnbiasedTimeAvg

/-- **The chain driven by the noise sequence, started from `x₀` at integer time `s`.**
N. Kahalé, *Unbiased time-average estimators for Markov chains*, arXiv:2209.09581v1, §2.1, p.4:
`G₀(x) := x`, `G_{i+1}(x; u₀, …, u_i) := g(G_i(x; u₀, …, u_{i−1}), u_i)`.

`drivenChain g x₀ U s n ω` is `G_n(x₀; U_s(ω), U_{s+1}(ω), …, U_{s+n−1}(ω))`: start at `x₀` and
apply the update `x ↦ g(x, U_t(ω))` at the times `t = s, s + 1, …, s + n − 1`. With `s = 0` this
is the chain `X_n` of (1.1) and (2.1), p.4; with `s = −m` it is the copy `X_{n−m,m}` of (2.2).

**Formalization Note.** The noise is indexed by all of `ℤ` (the paper extends `(U_i, i ≥ 0)` to
`i ∈ ℤ`, p.4), so a chain can be started at any integer time. The initial value `x₀` is
deterministic, as on p.2. -/
def drivenChain {Ω F F' : Type*} (g : F → F' → F) (x₀ : F) (U : ℤ → Ω → F') (s : ℤ) :
    ℕ → Ω → F
  | 0 => fun _ => x₀
  | n + 1 => fun ω => g (drivenChain g x₀ U s n ω) (U (s + n) ω)

end UnbiasedTimeAvg


