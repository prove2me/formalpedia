-- Prove2me | Definitions.Def_VpVnp_Approximates
-- name    : VpVnp_Approximates
-- status  : Definition
-- author  : @LG
-- created : 2026-11-23T23:36:43.647803+00:00
-- url     : https://prove2.me/theorems/384ee39f-05de-4895-82c8-ad1c44cf4a1f
-- title:
--   Approximating circuits over formal Laurent series (border complexity)
-- statement:
--   Border complexity, in the form of the source's Definition 1.3 (Definition N.1). Let $k$ be a field and $k((\varepsilon))$ the field of formal Laurent series in a formal variable $\varepsilon$. A circuit over $k((\varepsilon))$ **approximates** a polynomial $f \in k[V]$ if it computes a polynomial of the form $f + \varepsilon g$, where every coefficient of $g$ lies in the power series ring $k[[\varepsilon]]$.
--
--   The predicate $\mathrm{Approximates}(f,s)$ asserts that $f$ is approximated by a circuit with at most $s$ gates: there is a polynomial $q$ over $k((\varepsilon))$ in the same variables such that
--
--   1. $q$ has a circuit with at most $s$ gates over $k((\varepsilon))$, in the same gate model as for exact computation; and
--   2. for every monomial exponent vector $d$ and every integer $i \leq 0$, the coefficient of $\varepsilon^{i}$ in the coefficient of $d$ in $q$ equals the coefficient of $d$ in $f$ when $i = 0$, and is $0$ when $i < 0$.
--
--   Over the real numbers this captures limits: substituting a small positive real for $\varepsilon$ gives circuits over $\mathbb R$ with the same number of gates computing $f + \varepsilon g$, and these tend to $f$ coefficient by coefficient as $\varepsilon \to 0$, even though constants such as $1/\varepsilon$ diverge. The formal-series formulation expresses the same notion over an arbitrary field, and it is what the class $\overline{\mathrm{VP}}$ and the border form of the mission's lower bound are built from.
--
--   **Formalization Note.** Coefficients are Mathlib's `LaurentSeries F`, indexed by $\mathbb Z$; no condition is imposed on positive powers of $\varepsilon$, so $g$ is arbitrary above degree $0$. The gate count is the one of `VpVnp.Computes` over the base ring $k((\varepsilon))$, so variables and constants of that field count as gates.
-- source:
--   Claude (Anthropic), VP != VNP over every field (2026), https://github.com/anthropics/formal-math/tree/main/vp-vnp — paper.pdf Definition 1.3, p. 2 and Definition N.1, p. 62; Lean vp-vnp/Statement.lean, def Statement.Approximates

import Mathlib
import Definitions.Def_VpVnp_Circuit

open MvPolynomial

universe u

namespace VpVnp

/-- `f` is approximated by a circuit with at most `s` gates: a circuit over the Laurent series in `ε`
computes some `q = f + ε * g`, where the coefficients of `g` are power series in `ε`. Here `a.coeff i` is
the coefficient of `ε ^ i` in the series `a`. -/
def Approximates {F : Type u} {V : Type} [Field F] (f : MvPolynomial V F) (s : ℕ) : Prop :=
  ∃ q : MvPolynomial V (LaurentSeries F), Computes q s ∧
    ∀ (d : V →₀ ℕ) (i : ℤ), i ≤ 0 → (coeff d q).coeff i = if i = 0 then coeff d f else 0

end VpVnp


