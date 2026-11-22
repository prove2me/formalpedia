-- Prove2me | Definitions.Def_AvgPHETH_Supplement_HasUnsetSubtree
-- name    : AvgPHETH_Supplement_HasUnsetSubtree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:56:43.298918+00:00
-- url     : https://prove2.me/theorems/d5bc9982-31f4-454d-82c6-e486a4e11e35
-- title:
--   A complete subtree with arity $2^{a_k(n)}$ and all selectors unset
-- statement:
--   For a partial assignment and a selector tree $T^k_x$, $|x|=n$, a complete subtree with arity $2^{a_k(n)}$ is a subtree rooted at the root of $T^k_x$ with arity $2^{a_k(n)}$ at each level. This definition says that below a given node there is such a subtree, of a given number of levels, all of whose selectors are unset: the selector of the node is unset and $2^{a_k(n)}$ of its children satisfy the condition again.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "The construction", p.40 (PDF 42)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_CVar
import Definitions.Def_AvgPHETH_Supplement_aPar

namespace AvgPHETH.Supplement

/-- Below the node `path` of the selector tree `T^k_x` there is a complete subtree with arity
`2^{a_k(|x|)}` at each of its `r` levels, all of whose selectors are unset in `ρ`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, p.40 (PDF 42): "`T^k_x` has a complete subtree with arity `2^{a_k(n)}`
which has all selectors unset. Here, by a 'complete subtree with arity `2^{a_k(n)}`' we mean a subtree
rooted at the root of `T^k_x` with arity `2^{a_k(n)}` at each level").

**Formalization Note** `r` is the number of levels below `path`; with `r = k` and `path = []` this is the
page's condition on `T^k_x`. The selector of `path` is unset and `2^{a_k(|x|)}` of its children (strings
of `Y_{j+1}(|x|)`, `j` the depth of `path`) again satisfy the condition; leaves carry no selector. -/
def HasUnsetSubtree (ε : ℕ → ℝ) (ρ : CVar → Option (List Bool)) (k : ℕ) (x : List Bool) :
    ℕ → List (List Bool) → Prop
  | 0, _ => True
  | r + 1, path =>
      ρ ⟨k, x, false, path⟩ = none ∧
        ∃ C : Finset (List Bool), C.card = 2 ^ aPar ε k x.length ∧
          ∀ y ∈ C, y.length = aPar ε (path.length + 1) x.length ∧
            HasUnsetSubtree ε ρ k x r (path ++ [y])

end AvgPHETH.Supplement


