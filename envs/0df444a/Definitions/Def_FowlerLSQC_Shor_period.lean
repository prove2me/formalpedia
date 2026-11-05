-- Prove2me | Definitions.Def_FowlerLSQC_Shor_period
-- name    : FowlerLSQC_Shor_period
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:35:18.938141+00:00
-- url     : https://prove2.me/theorems/5a056cb4-d152-451c-8abb-1f6e29832426
-- title:
--   Period $r$ of $f(k)=m^k \bmod N$
-- statement:
--   Let $N\ge1$ and let $m$ be an integer with $\gcd(m,N)=1$. The **period** of the function
--   $$
--   f(k)=m^k \bmod N
--   $$
--   is the least $r>0$ with $m^r\equiv1\pmod N$, the multiplicative order of $m$ modulo $N$. Then $f(k)=f(k')$ if and only if $k\equiv k'\pmod r$.
--
--   Finding $r$ is the task of the quantum part of Shor's algorithm; the factors of $N$ and the analysis of the measured outcomes are stated in terms of it.
--
--   **Formalization Note** The period is Mathlib's `orderOf` of the residue of $m$ in $\mathbb Z/N\mathbb Z$. If $m$ is not coprime to $N$ the Lean value is $0$; every statement of the mission assumes $\gcd(m,N)=1$, as the book does.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, Ch. 7, p.75 (PDF p.93)

import Mathlib

namespace FowlerLSQC.Shor

/-- The period `r` of `f(k) = m^k mod N`, Fowler, *Towards Large-Scale Quantum Computation*,
arXiv:quant-ph/0506126v1, Ch. 7, p.75 (PDF 93): "the period r of f(k) = m^k mod N, where
1 < m < N, gcd(m, N) = 1". It is the least `r > 0` with `m^r ≡ 1 (mod N)`, the multiplicative order
of `m` modulo `N`.

**Formalization Note** The period is Mathlib's `orderOf` of the residue `(m : ZMod N)` in the
multiplicative monoid of `ℤ/Nℤ`. When `gcd(m, N) = 1` and `N ≥ 1` it is positive and is the least
period of `k ↦ m^k mod N` (since `m^k mod N = m^(k') mod N ↔ k ≡ k' (mod r)` for a unit). When `m`
is not coprime to `N` the value is the junk `0`; every statement of this mission assumes
`gcd(m, N) = 1`, as the book does. -/
noncomputable def period (N m : ℕ) : ℕ := orderOf (m : ZMod N)

end FowlerLSQC.Shor


