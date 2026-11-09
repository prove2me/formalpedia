-- Prove2me | Definitions.Def_HybridXorLift_hybridQ
-- name    : HybridXorLift_hybridQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:34.413276+00:00
-- url     : https://prove2.me/theorems/8ac36695-b8b4-4f9c-b745-ab43ef919023
-- title:
--   Hybrid query complexity $Q(g;q)$
-- statement:
--   For a partial Boolean function $g$ on the index set $\iota$ and an integer $q \ge 1$, the **hybrid query complexity**
--   $$
--   Q(g;q) = Q_{1/3}(g;q)
--   $$
--   is the least cost of a $q$-query hybrid algorithm with error at most $1/3$ on every promised input $x \in \mathrm{Dom}(g)$.
--
--   **Formalization Note** Error at most $1/3$ on $x$ is written as probability at least $2/3$ of outputting $g(x)$; for Boolean outputs the two are equivalent. The algorithm is defined on all of $\{0,1\}^\iota$ and only promised inputs are constrained. The minimum is an infimum over the natural numbers; for a finite index set the set of admissible costs is nonempty (read every bit), so the infimum is attained.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Definition 2.1, p.9 (PDF p.11)

import Definitions.Def_NoPerfectRandComp_PartialFn
import Definitions.Def_HybridXorLift_HybridAlg_outProb
import Definitions.Def_HybridXorLift_HybridAlg_cost
import Definitions.Def_HybridXorLift_HybridAlg_RoundsAtMost

namespace HybridXorLift

/-- The hybrid query complexity `Q(g; q) = Q_{1/3}(g; q)` (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), Definition 2.1, p.9 (PDF p.11)):
the least cost of a `q`-query hybrid algorithm with error at most `1/3` on every promised input.

**Formalization Note** Error at most `1/3` on `x ∈ dom g` is written as probability at least
`2/3` of outputting `g.val x` (equivalent for `Bool` outputs, whose output probabilities sum to
one). The algorithm is defined on all inputs; only promised inputs are constrained. The infimum
is over `ℕ`; for a finite index type the set is nonempty (the algorithm that reads every bit), so
the infimum is attained. -/
noncomputable def hybridQ {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : NoPerfectRandComp.PartialFn ι) (q : ℕ) : ℕ :=
  sInf {T : ℕ | ∃ A : HybridAlg ι Bool, A.RoundsAtMost q ∧ A.cost ≤ T ∧
    ∀ x ∈ g.dom, 2 / 3 ≤ A.outProb x (g.val x)}

end HybridXorLift


