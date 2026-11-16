-- Prove2me | Definitions.Def_CubicProductLB_Supplement_signedModP
-- name    : CubicProductLB_Supplement_signedModP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:35:57.238201+00:00
-- url     : https://prove2.me/theorems/2da997e5-a6db-46e9-81c8-d61b7a13164d
-- title:
--   The signed MOD-$q$ target $F_{q,n}$ over $\mathbb F_p$
-- statement:
--   For a coefficient field $\mathbb F_p$ and a target modulus $q$, the **signed MOD-$q$ target** is
--   $$F_{q,n}(x) = \begin{cases} -1, & q \mid w(x),\\ 1, & q \nmid w(x),\end{cases}$$
--   with values in $\mathbb F_p$. It takes the value $-1$ at the all-ones point.
--
--   **Formalization Note** No hypothesis on $p$ or $q$ is built in; the theorems assume $p>3$ prime, $q>1$ odd and $\gcd(p,q)=1$.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Eq. (397), p.51

import Mathlib
import Definitions.Def_CubicProductLB_Supplement_negCountP

namespace CubicProductLB.Supplement

/-- The signed MOD-`q` target over `F_p`: `F_{q,n}(x) = -1` if `q ∣ w(x)` and `1` otherwise
(Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Eq. (397), p.51).

**Formalization Note** `p` is the characteristic of the coefficient field and `q` the target modulus
(the notation of Section 15). Neither carries a hypothesis here; the theorems add `p` prime, `3 < p`,
`q` odd, `1 < q`, `gcd(p, q) = 1`. -/
def signedModP (p q n : ℕ) (x : Fin n → ZMod p) : ZMod p :=
  if q ∣ negCountP x then -1 else 1

end CubicProductLB.Supplement


