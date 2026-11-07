-- Prove2me | Definitions.Def_IntQuotHNP_RationalValues
-- name    : IntQuotHNP_RationalValues
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:26.3282+00:00
-- url     : https://prove2.me/theorems/543796b2-2cee-4d92-99d8-061f8c0d07fb
-- title:
--   §4.2 — $|a|_p$, values of rational functions, nonconstant functions, simple poles
-- statement:
--   For a residue $a$, $|a|_p=\min\{[a]_p,\,p-[a]_p\}$. A rational function over a field is evaluated as the quotient of its reduced numerator and denominator, where the denominator does not vanish. It is **nonconstant** if it is no constant function. It **has only simple poles, including at infinity**, if all its finite poles have order one over an algebraic closure and its pole at infinity has order at most one.
--
--   **Formalization Note** Finite poles are the roots of the reduced denominator with their multiplicities, so they are all simple exactly when `RatFunc.denom` is separable. The pole order at infinity is $\deg\mathrm{num}-\deg\mathrm{denom}$ when positive, so it is at most one exactly when $\deg\mathrm{num}\le\deg\mathrm{denom}+1$. Evaluation is meaningful where the denominator is nonzero, and each statement using it carries that hypothesis.
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), §4.2, p.25 (PDF p.26)

import Mathlib

namespace IntQuotHNP

/-- **The centred absolute value `|a|_p = min{[a]_p, p − [a]_p}`** (§4.2).
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), §4.2, p.25 (PDF p.26): "Here |a|_p = min{[a]_p, p − [a]_p}."

**Formalization Note.** `[a]_p` of a residue `a ∈ ZMod p` is `a.val`. -/
def absP (p : ℕ) (a : ZMod p) : ℕ :=
  min a.val (p - a.val)

/-- **The value of a rational function at a point** (§4.2).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), §4.2, p.25 (PDF p.26): "A rational
function is a quotient of polynomials, evaluated where its denominator is nonzero."

`ratEval f z = num(z)/denom(z)` for the reduced numerator and denominator of `f`.

**Formalization Note.** `RatFunc.num`, `RatFunc.denom` are coprime with monic denominator. The value
is meaningful where `f.denom.eval z ≠ 0` ("`f` is defined at `z`"); every statement using it carries
that hypothesis. -/
noncomputable def ratEval {K : Type*} [Field K] (f : RatFunc K) (z : K) : K :=
  f.num.eval z / f.denom.eval z

/-- **A nonconstant rational function** (§4.2, Lemma 4.6).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Lemma 4.6, p.25 (PDF p.26):
"is nonconstant".

`f` is not the constant rational function `c` for any `c ∈ K`. -/
def IsNonconstant {K : Type*} [Field K] (f : RatFunc K) : Prop :=
  ∀ c : K, f ≠ RatFunc.C c

/-- **A rational function with only simple poles, including at infinity** (§4.2, Lemma 4.6).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), §4.2, p.25 (PDF p.26): "A finite
pole of order h at β means that, after cancellation, the function has the form (z − β)^{−h}g(z) with
g defined and nonzero at β. Pole orders are considered over an algebraic closure. At infinity, use
t = 1/z and take the pole order of f(1/t) at t = 0. A pole of order one is called simple."

1. Finite poles are the roots of the reduced denominator, with their multiplicities, over an
   algebraic closure; they are all simple exactly when the reduced denominator is separable.
2. The pole order at infinity is `deg num − deg denom` when positive; it is at most one exactly when
   `deg num ≤ deg denom + 1`.

**Formalization Note.** `Polynomial.Separable` (coprime to its derivative) is equivalent to having
no repeated root in an algebraic closure. -/
def HasOnlySimplePoles {K : Type*} [Field K] (f : RatFunc K) : Prop :=
  f.denom.Separable ∧ f.num.natDegree ≤ f.denom.natDegree + 1

end IntQuotHNP


