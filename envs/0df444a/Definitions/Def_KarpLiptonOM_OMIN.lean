-- Prove2me | Definitions.Def_KarpLiptonOM_OMIN
-- name    : KarpLiptonOM_OMIN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:24.213206+00:00
-- url     : https://prove2.me/theorems/4be7a6fe-31fb-417e-aebf-550601e1c7d5
-- title:
--   OMIN: decoding the minimum of an input-oblivious order (Definition A.2.9)
-- statement:
--   A language $L$ is in $\mathrm{OMIN}$ if there are a polynomial $p$, a predicate $U(1^n, u, w)$ computable in time polynomial in $n$ such that
--   $$
--   u <_n w \;:\iff\; U(1^n, u, w) = 1
--   $$
--   is a strict linear order on $\{0,1\}^{p(n)}$ for every $n$, and a polynomial-time decoder $D$ such that
--   $$
--   L(x) = D\bigl(x, \mu_{|x|}\bigr) \quad \text{for every } x, \qquad \mu_n = \min{<_n} .
--   $$
--   The order depends only on the input length, and its minimum is an advice string from which $L$ is decoded.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Definition A.2.9, p.23

import Mathlib
import Definitions.Def_KarpLiptonOM_PolyPred2
import Definitions.Def_KarpLiptonOM_PolyPred3
import Definitions.Def_KarpLiptonOM_IsStrictLinearOn
import Definitions.Def_KarpLiptonOM_IsMinOn

namespace KarpLiptonOM

/-- `L ∈ OMIN` (Definition A.2.9, Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), p.23): a polynomial `p`, a predicate `U(1ⁿ, u, w)` computable
in time polynomial in `n` such that `u <ₙ w :⇔ U(1ⁿ, u, w) = 1` is a strict linear order on
`{0,1}^{p(n)}` for every `n`, and a polynomial-time decoder `D` with `L(x) = D(x, µ_|x|)` for every
`x`, where `µₙ = min <ₙ`.

**Formalization Note** `U` is a polynomial-time ternary predicate applied to `(1ⁿ, u, w)` with
`|u| = |w| = p(n)`, i.e. computable in time polynomial in `n`; `p ≥ 1` as in the paper's convention. -/
def OMIN : Set (Set (List Bool)) :=
  {L | ∃ (p : Polynomial ℕ) (U : List Bool → List Bool → List Bool → Prop)
      (D : List Bool → List Bool → Prop), PolyPred3 U ∧ PolyPred2 D ∧ (∀ n, 1 ≤ p.eval n) ∧
    (∀ n : ℕ, IsStrictLinearOn (p.eval n) (U (List.replicate n true))) ∧
    ∀ (x μ : List Bool), IsMinOn (p.eval x.length) (U (List.replicate x.length true)) μ →
      (x ∈ L ↔ D x μ)}

end KarpLiptonOM


