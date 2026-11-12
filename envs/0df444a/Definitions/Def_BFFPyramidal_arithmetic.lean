-- Prove2me | Definitions.Def_BFFPyramidal_arithmetic
-- name    : BFFPyramidal_arithmetic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-13T18:25:41.877898+00:00
-- url     : https://prove2.me/theorems/d9a71d56-3357-4d48-9494-1c3502f8ae4b
-- title:
--   Greatest prime factor, divisor closure, and the totient measure
-- statement:
--   Three arithmetic notions used in the multiplicity bound.
--
--   For a natural number $m$, the **greatest prime factor** $P(m)$ is the largest prime dividing $m$, with the convention $P(0) = P(1) = 0$ (the supremum of an empty set of primes). This is the function written $P$ in Berger–Felzenbaum–Fraenkel; the *least* prime factor, written $p$ there and appearing in the definition of a pyramidal group, is a different function (Mathlib's `Nat.minFac`).
--
--   For a finite set $R$ of positive integers, the **divisor closure** is
--   $$ D(R) \;=\; \{\, d : d \mid m \text{ for some } m \in R \,\}, \qquad D(\emptyset) = \emptyset . $$
--
--   The **totient measure** of a finite set $S$ of naturals is
--   $$ \mu(S) \;=\; \sum_{m \in S} \varphi(m), $$
--   the measure determined by $\mu(\{m\}) = \varphi(m)$, where $\varphi$ is Euler's totient function. The two interact through Gauss's identity $\sum_{d \mid m}\varphi(d) = m$, which says precisely that $\mu(D(\{m\})) = m$.
--
--   **Formalization note.** $D$ and $\mu$ are `Finset` operations: `Finset.biUnion` of `Nat.divisors`, and a `Finset.sum` of `Nat.totient`. Since `Nat.divisors 0 = ∅`, a member $0$ of $R$ contributes nothing, whereas in the source every $d$ divides $0$; the two readings agree on sets of positive integers, which is the only case used here, the members of $R$ being orders of subgroups. Because $D(R)$ is a set, equal orders are collapsed — $\mu(D(R))$ depends on the set of orders, not on their multiplicities.
-- source:
--   Berger--Felzenbaum--Fraenkel 1987, Remark on the multiplicity of a partition of a group into cosets, Fund. Math. 128 (1987) 139-144, https://doi.org/10.4064/fm-128-3-139-144, p. 139 (the function $P$) and p. 141, eqs. (9)-(10), with eq. (13) Gauss's identity

import Mathlib

namespace BFFPyramidal

/-- The greatest prime factor `P m` of a natural number `m`, as the supremum of its set of
prime factors. Since that set is empty for `m = 0` and `m = 1`, the convention here is
`P 0 = P 1 = 0`.

Note that this is the *greatest* prime factor, written `P` in Berger–Felzenbaum–Fraenkel; the
*least* prime factor, written `p` there, is Mathlib's `Nat.minFac` and is what the definition of
a pyramidal group uses. -/
def maxPrimeFac (m : ℕ) : ℕ := m.primeFactors.sup id

/-- The **divisor closure** `D R = {d : d ∣ m for some m ∈ R}` of a finite set of naturals;
equation (10) of Berger–Felzenbaum–Fraenkel, with `D ∅ = ∅`.

Caveat on the boundary: Mathlib's `Nat.divisors 0 = ∅`, so a member `0` of `R` contributes
nothing, whereas in the source every `d` divides `0`. The two readings agree on sets of
*positive* integers, which is the only case in which `D` is used here — in the applications the
members of `R` are orders of subgroups. -/
def divisorClosure (R : Finset ℕ) : Finset ℕ := R.biUnion Nat.divisors

/-- The measure `μ S = ∑_{m ∈ S} φ m` determined by `μ {m} = φ m`, where `φ` is Euler's totient;
equation (9) of Berger–Felzenbaum–Fraenkel. Gauss's identity `∑_{d ∣ m} φ d = m` says exactly
that `μ (D {m}) = m`. -/
def muMeasure (S : Finset ℕ) : ℕ := ∑ m ∈ S, Nat.totient m

end BFFPyramidal


