-- Prove2me | Definitions.Def_KarpLiptonOM_Ppoly
-- name    : KarpLiptonOM_Ppoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:15.190999+00:00
-- url     : https://prove2.me/theorems/0f74ed58-491c-4bf5-9b50-ae746141301a
-- title:
--   $\mathrm{P/poly}$ (polynomial advice)
-- statement:
--   A language $L$ is in $\mathrm{P/poly}$ if there are a polynomial $p$, strings $a_n \in \{0,1\}^{p(n)}$ for every $n$ (arbitrary, non-uniform advice), and a polynomial-time predicate $D$ such that
--   $$
--   x \in L \iff D\bigl(x, a_{|x|}\bigr) \quad \text{for every } x .
--   $$
--   This is the paper's $\mathrm{OGTD}[\mathrm{poly}, *, \mathrm P]$, the generator–decoder form of P/poly, equivalent to polynomial-size circuits.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.4, p.24 (P/poly = OGTD[poly, ∗, P])

import Mathlib
import Definitions.Def_KarpLiptonOM_PolyPred2

namespace KarpLiptonOM

/-- `P/poly` in advice form (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.4, p.24: "`P/poly = OGTD[poly, ∗, P]`", with the generator
class poly "of all polynomially length bounded functions `n ↦ a_n`"): `L ∈ P/poly` iff there are a
polynomial `p`, advice strings `a_n` of length `p(n)` and a polynomial-time `D` with
`x ∈ L ↔ D(x, a_|x|)`.

**Formalization Note** The advice function `a` is arbitrary (non-uniform); its length is exactly a
polynomial `p(n)`, as in the paper's convention §A.2.1. -/
def Ppoly : Set (Set (List Bool)) :=
  {L | ∃ (p : Polynomial ℕ) (a : ℕ → List Bool) (D : List Bool → List Bool → Prop),
    PolyPred2 D ∧ (∀ n, (a n).length = p.eval n) ∧ ∀ x : List Bool, x ∈ L ↔ D x (a x.length)}

end KarpLiptonOM


