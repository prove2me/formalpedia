-- Prove2me | Definitions.Def_UniqueOptScores_UO
-- name    : UniqueOptScores_UO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:28:11.116178+00:00
-- url     : https://prove2.me/theorems/f0f1d414-4860-4cc3-b13d-39acc7fe35ff
-- title:
--   The fixed-score class $\mathrm{UO}[k]^A$
-- statement:
--   For an integer $k \ge 1$, a language $L$ belongs to $\mathrm{UO}[k]^A$ if there are a clocked deterministic oracle evaluator $E$ and a candidate length $p$ with $p(n) \ge 1$ for all $n$ such that for every input $x$
--   $$
--   x \in L \iff z \mapsto s^A_k(x, z) \text{ has exactly one maximizer on } \{0,1\}^{p(|x|)} ,
--   $$
--   where $s^A_k$ is the score of $E$ with ceiling $k$ (out-of-range values count as $0$). Since $p \ge 1$, the all-zero score function rejects. $\mathrm{UO}[1]^A = \mathrm{US}^A$, and the levels form the score hierarchy studied by the mission.
--
--   **Formalization Note** The paper allows any oracle-independent, polynomial-time computable, polynomially bounded candidate length $p \ge 1$; a polynomial $p \ge 1$ gives the same class (pad to a polynomial bound and give score $0$ to names with nonzero padding: positive-score multiplicities are unchanged and an all-zero function still has two maximizers). The clock holds for every oracle. The definition is stated for every $k$ and used for $k \ge 1$.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 4, p.16, Definition 4.1

import Mathlib
import Definitions.Def_HMBinPacking_OracleMachine
import Definitions.Def_UniqueOptScores_IsClocked
import Definitions.Def_UniqueOptScores_score
import Definitions.Def_UniqueOptScores_UniqueMaxOn

namespace UniqueOptScores

/-- **The fixed-score class UO[k]^A.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §4, p.16, Definition 4.1: "For an integer k ≥ 1, a language is in UO[k]^A if there is a
deterministic polynomial- time oracle evaluator s^A(x, z) ∈ {0, . . . , k}, z ∈ {0, 1}^{p(|x|)},
such that x belongs to the language exactly when s^A(x, ·) has one maximizing candidate."

`L ∈ UO A k` if there are a clocked evaluator `E` and a candidate length `p ≥ 1` such that `x ∈ L`
exactly when the score function `z ↦ score E A k x z` on `{0,1}^{p(|x|)}` has exactly one maximizer.

**Formalization Note.** Candidates range over the **whole** set `{0,1}^{p(|x|)}` with `p(n) ≥ 1`
for every `n` (so the all-zero score function rejects); out-of-range scores are `0` (`score`); the
clock holds for every oracle. The paper's candidate length is any oracle-independent,
polynomial-time computable, polynomially bounded `p ≥ 1`; a polynomial `p ≥ 1` gives the same
class (pad to a polynomial bound and give score `0` to names with nonzero padding). The class is
used for `k ≥ 1`. -/
def UO (A : Set (List Bool)) (k : ℕ) : Set (Set (List Bool)) :=
  {L | ∃ (E : HMBinPacking.OracleMachine) (t p : Polynomial ℕ), IsClocked E t ∧
    (∀ n : ℕ, 1 ≤ p.eval n) ∧
    ∀ x : List Bool, x ∈ L ↔ UniqueMaxOn (p.eval x.length) (score E A k x)}

end UniqueOptScores


