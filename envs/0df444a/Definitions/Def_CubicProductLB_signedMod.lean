-- Prove2me | Definitions.Def_CubicProductLB_signedMod
-- name    : CubicProductLB_signedMod
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:14:40.121289+00:00
-- url     : https://prove2.me/theorems/c74c5b7e-9ad7-4831-9d66-2f97244e3a41
-- title:
--   The signed modular target $F_{p,n}$
-- statement:
--   For a modulus $p$, the **signed modular target** on $x \in \mathbb F_3^n$ is
--   $$F_{p,n}(x) = \begin{cases} -1, & p \mid w(x), \\ 1, & p \nmid w(x). \end{cases}$$
--   It is nowhere zero. Note the sign: the value is $-1$ when $p$ divides $w(x)$, in particular at the all-ones point, where $w = 0$.
--
--   **Formalization Note** The modulus carries no hypothesis in the definition; the theorems assume $p$ prime and $p > 3$.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Eq. (2), p.3

import Mathlib
import Definitions.Def_CubicProductLB_negCount

namespace CubicProductLB

/-- The signed modular target `F_{p,n}`: `-1` if `p ∣ w(x)` and `1` otherwise
(Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Eq. (2), p.3).

**Formalization Note** `p` carries no hypothesis here; the theorems add `p` prime, `3 < p`. -/
def signedMod (p n : ℕ) (x : Fin n → ZMod 3) : ZMod 3 :=
  if p ∣ negCount x then -1 else 1

end CubicProductLB


