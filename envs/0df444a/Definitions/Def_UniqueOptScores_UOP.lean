-- Prove2me | Definitions.Def_UniqueOptScores_UOP
-- name    : UniqueOptScores_UOP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:28:19.66295+00:00
-- url     : https://prove2.me/theorems/c6ec3f7f-0116-4bfc-b3ce-da262221e24a
-- title:
--   The polynomial-score class $\mathrm{UO}^A_{\mathrm P}$
-- statement:
--   A language $L$ belongs to $\mathrm{UO}^A_{\mathrm P}$ if there are a clocked deterministic oracle evaluator $E$, a candidate length $p \ge 1$ and a polynomial score bound $r$ with $r(n) \ge 1$ for all $n$ such that
--   $$
--   x \in L \iff z \mapsto s^A_{r(|x|)}(x, z) \text{ has exactly one maximizer on } \{0,1\}^{p(|x|)} .
--   $$
--   Scores above $r(|x|)$ count as $0$. The score bound is numerical (values, not bit lengths) and depends on the evaluator.
--
--   **Formalization Note** Same conventions as for $\mathrm{UO}[k]^A$: full candidate domain, polynomial $p \ge 1$, clocks valid for every oracle.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 4, p.16, Definition 4.1 ("The class UO^A_P allows scores in {0, . . . , r(|x|)} for an explicit, numerically polynomial bound r ≥ 1")

import Mathlib
import Definitions.Def_HMBinPacking_OracleMachine
import Definitions.Def_UniqueOptScores_IsClocked
import Definitions.Def_UniqueOptScores_score
import Definitions.Def_UniqueOptScores_UniqueMaxOn

namespace UniqueOptScores

/-- **The polynomial-score class UO^A_P.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §4, p.16, Definition 4.1: "The class UO^A_P allows scores in {0, . . . , r(|x|)} for an
explicit, numerically polynomial bound r ≥ 1, depending on the evaluator."

`L ∈ UOP A` if there are a clocked evaluator `E`, a candidate length `p ≥ 1` and a polynomial score
bound `r ≥ 1` such that `x ∈ L` exactly when `z ↦ score E A (r(|x|)) x z` on `{0,1}^{p(|x|)}` has
exactly one maximizer.

**Formalization Note.** As for `UO`: full candidate domain, `p ≥ 1`, out-of-range scores (above
`r(|x|)`) are `0`, clocks valid for every oracle; `r` is a polynomial with `r(n) ≥ 1` for all `n`. -/
def UOP (A : Set (List Bool)) : Set (Set (List Bool)) :=
  {L | ∃ (E : HMBinPacking.OracleMachine) (t p r : Polynomial ℕ), IsClocked E t ∧
    (∀ n : ℕ, 1 ≤ p.eval n) ∧ (∀ n : ℕ, 1 ≤ r.eval n) ∧
    ∀ x : List Bool, x ∈ L ↔ UniqueMaxOn (p.eval x.length) (score E A (r.eval x.length) x)}

end UniqueOptScores


