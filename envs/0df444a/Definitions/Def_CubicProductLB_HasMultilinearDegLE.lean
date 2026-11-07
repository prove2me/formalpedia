-- Prove2me | Definitions.Def_CubicProductLB_HasMultilinearDegLE
-- name    : CubicProductLB_HasMultilinearDegLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:14:03.86226+00:00
-- url     : https://prove2.me/theorems/78d53256-1b40-438b-a785-c231aebec4be
-- title:
--   Multilinear degree at most $d$ on $X_n$
-- statement:
--   A function $f$ has **multilinear degree at most $d$ on $X_n$** if there is a multilinear polynomial $Q$ over $\mathbb F_3$, that is, one all of whose monomials are square-free, with total degree at most $d$ and with $Q(x) = f(x)$ for every $x \in X_n$. Since $x_j^2 = 1$ on $X_n$, every polynomial has a unique such representative.
--
--   This is a condition on the function on $X_n$, not on a listing: a listed monomial of high degree is allowed when the listing reduces to low degree, for example $x_1^2 x_2^2 x_3^2 x_4^2$ has multilinear degree $0$.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Definition 1 and the paragraph after it, pp.3–4

import Mathlib
import Definitions.Def_CubicProductLB_signCube

namespace CubicProductLB

/-- `f` has multilinear degree at most `d` on `X_n`: its multilinear representative on the sign
cube has total degree at most `d` (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Definition 1 and the paragraph after it, pp.3–4).

**Formalization Note** This is a condition on the function on `X_n`, not on a listing: a listed
monomial of degree `7` is allowed when the listing reduces to degree at most `d`. The representative
is unique, so `∃` here is the page's "the" representative. Values of `f` off `X_n` are ignored. -/
def HasMultilinearDegLE {n : ℕ} (d : ℕ) (f : (Fin n → ZMod 3) → ZMod 3) : Prop :=
  ∃ Q : MvPolynomial (Fin n) (ZMod 3),
    (∀ m ∈ Q.support, ∀ i, m i ≤ 1) ∧ Q.totalDegree ≤ d ∧
      ∀ x ∈ signCube n, MvPolynomial.eval x Q = f x

end CubicProductLB


