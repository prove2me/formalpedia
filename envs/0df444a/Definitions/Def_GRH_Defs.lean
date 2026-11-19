-- Prove2me | Definitions.Def_GRH_Defs
-- name    : GRH_Defs
-- status  : Definition
-- author  : @LG
-- created : 2026-11-18T17:50:09.390963+00:00
-- url     : https://prove2.me/theorems/5ba2e95c-bcf8-42fe-acbd-a8a44287c932
-- title:
--   Prime counting in arithmetic progressions $\pi(x; q, a)$
-- statement:
--   Let $q$ and $a$ be natural numbers and $x$ a real number. The **prime-counting function of the arithmetic progression** $a \bmod q$ is
--
--   $$\pi(x;\, q, a) \;=\; \#\{\, p \le x \;:\; p \text{ prime and } p \equiv a \pmod q \,\}.$$
--
--   For $q = 1$ this is the usual prime-counting function $\pi(x)$; for general $q$ it counts the primes up to $x$ in the residue class $a$, and is the counting function appearing in the GRH-conditional prime number theorem for arithmetic progressions.
--
--   **Formalization Note.** The definition imposes no coprimality or positivity conditions: it is a finite filter over $p < \lfloor x \rfloor + 1$. For $x < 0$ the value is $0$; for $q = 0$ the congruence means $p = a$. Coprimality $\gcd(a,q)=1$ and $q \ge 1$ enter the theorem statements that use it, not the definition.
-- source:
--   https://en.wikipedia.org/wiki/Generalized_Riemann_hypothesis (section 'Consequences of GRH', item on the effective Dirichlet theorem, defining $\pi(x,a,d)$ as the number of primes $\le x$ in the progression $n d + a$; oldid 1378052002).

import Mathlib

set_option autoImplicit false

namespace GRH

/-- `primeCountingAP q a x` is `π(x; q, a)`: the number of primes `p ≤ x` lying in the
residue class `a mod q`. For `x < 0` the value is `0`. -/
noncomputable def primeCountingAP (q a : ℕ) (x : ℝ) : ℕ :=
  (Finset.filter (fun p => p.Prime ∧ p ≡ a [MOD q]) (Finset.range (⌊x⌋₊ + 1))).card

end GRH


