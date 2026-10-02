-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_NegSI
-- name    : DiscreteConvex_EconomicEquilibrium_NegSI
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:58:16.488873+00:00
-- url     : https://prove2.me/theorems/4787de34-43dc-49e3-a68f-3398c53ee7a8
-- title:
--   Single improvement axiom ($-$M$^\natural$-SI[Z]) (Eq. 11.20)
-- statement:
--   Axiom **($-$M$^\natural$-SI[Z])** (Eq. (11.20)): for $p \in \mathbb R^K$ and $x, y \in \mathbb Z^K$ with $-\infty < U[-p](x) < U[-p](y)$,
--   $$U[-p](x) < \max_{i \in \operatorname{supp}^+(x-y)\cup\{0\}}\ \max_{j \in \operatorname{supp}^-(x-y)\cup\{0\}} U[-p](x - \chi_i + \chi_j).$$
--
--   **Formalization Note.** Formalized as the equivalent existential form "$\exists i, j,\ U[-p](x) < U[-p](x-\chi_i+\chi_j)$", since both extended index sets are always nonempty (each contains the sentinel $0$, represented as `none : Option K` via chunk 06's `CharVecOpt`) and finite, so "$a < \max S$" and "$\exists s \in S,\ a < s$" coincide.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.331, Eq. (11.20).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.331, Eq. (11.20)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVecOpt
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppNeg
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_PriceShift

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.331, Eq. (11.20), axiom (−M♮-SI[Z]): the single
improvement / ascent property of M♮-concave functions, in `DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

open DiscreteConvex.MConvexFunctions

/-- Axiom **(−M♮-SI[Z])** (Eq. (11.20)): for `p ∈ Rᴷ` and `x, y ∈ Zᴷ` with
`−∞ < U[−p](x) < U[−p](y)`, there exist `i ∈ supp⁺(x-y) ∪ {0}` and `j ∈ supp⁻(x-y) ∪ {0}` (with
`χ₀ = 0`, represented as `Option K` via `CharVecOpt`, `none` standing for `0`) such that
`U[−p](x) < U[−p](x - χ_i + χ_j)`. Formalized as the equivalent existential form of
"`U[−p](x) < max_i max_j U[−p](x-χ_i+χ_j)`", since both extended index sets are always nonempty
(they contain `0`/`none`) and finite. -/
def NegSI {K : Type*} [Fintype K] [DecidableEq K] (U : (K → ℤ) → WithBot ℝ) : Prop :=
  ∀ p : K → ℝ, ∀ x y : K → ℤ, ⊥ < PriceShift U p x → PriceShift U p x < PriceShift U p y →
    ∃ i : Option K, (i = none ∨ ∃ k ∈ SuppPos x y, i = some k) ∧
    ∃ j : Option K, (j = none ∨ ∃ k ∈ SuppNeg x y, j = some k) ∧
      PriceShift U p x <
        PriceShift U p (fun w => x w - CharVecOpt i w + CharVecOpt j w)

end DiscreteConvex.EconomicEquilibrium


