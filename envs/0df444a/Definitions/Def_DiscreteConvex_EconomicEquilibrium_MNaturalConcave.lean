-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_MNaturalConcave
-- name    : DiscreteConvex_EconomicEquilibrium_MNaturalConcave
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:58:13.279601+00:00
-- url     : https://prove2.me/theorems/9da1b463-3a62-4130-81f2-6ce2758f15a9
-- title:
--   M$^\natural$-concave utility function (Eq. 11.17)
-- statement:
--   $U : \mathbb Z^K \to \mathbb R \cup \{-\infty\}$ with $\operatorname{dom} U \ne \emptyset$ is **M$^\natural$-concave** if it satisfies the exchange axiom **($-$M$^\natural$-EXC[Z])** (Eq. (11.17)): for $x, y \in \operatorname{dom} U$ and $i \in \operatorname{supp}^+(x-y)$,
--   $$U(x) + U(y) \le \max\Big(U(x-\chi_i) + U(y+\chi_i),\ \max_{j \in \operatorname{supp}^-(x-y)}\big[U(x-\chi_i+\chi_j) + U(y+\chi_i-\chi_j)\big]\Big),$$
--   where a maximum over an empty set is $-\infty$ (the book's stated convention, realized here by `Finset.sup`'s default value $\bot$ on `WithBot ℝ`). This is the direct definition of M$^\natural$-concavity the book licenses at the start of section 11.3 by recalling Theorem 6.2 (the corresponding equivalence for M$^\natural$-convex functions).
--
--   **Formalization Note.** Reuses chunk 06's `CharVec`, `SuppPos`, `SuppNeg` (generic in the ground-set type, so directly applicable here with $K$ in place of $V$).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.330, Eq. (11.17).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.330, Eq. (11.17)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppNeg
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_UDom

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.330, Eq. (11.17), axiom (−M♮-EXC[Z]): the direct
definition of an M♮-concave function (licensed by Theorem 6.2, as the book itself recalls at the
start of section 11.3), in `DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

open DiscreteConvex.MConvexFunctions

/-- `U : Zᴷ → R ∪ {−∞}` with `dom U ≠ ∅` is **M♮-concave** if it satisfies the exchange axiom
**(−M♮-EXC[Z])** (Eq. (11.17)): for `x, y ∈ dom U` and `i ∈ supp⁺(x-y)`,
`U(x) + U(y) ≤ max(U(x - χ_i) + U(y + χ_i), max_{j ∈ supp⁻(x-y)}[U(x - χ_i + χ_j) + U(y + χ_i -
χ_j)])`, where a maximum over an empty set is `−∞` (matching the book's stated convention, and
realized here by `Finset.sup`'s default value `⊥` on `WithBot ℝ`). -/
def MNaturalConcave {K : Type*} [Fintype K] [DecidableEq K] (U : (K → ℤ) → WithBot ℝ) : Prop :=
  (UDom U).Nonempty ∧
  ∀ x ∈ UDom U, ∀ y ∈ UDom U, ∀ i ∈ SuppPos x y,
    U x + U y ≤ max (U (fun w => x w - CharVec i w) + U (fun w => y w + CharVec i w))
      ((SuppNeg x y).sup (fun j =>
        U (fun w => x w - CharVec i w + CharVec j w) +
          U (fun w => y w + CharVec i w - CharVec j w)))

end DiscreteConvex.EconomicEquilibrium


