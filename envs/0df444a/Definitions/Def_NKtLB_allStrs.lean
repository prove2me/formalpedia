-- Prove2me | Definitions.Def_NKtLB_allStrs
-- name    : NKtLB_allStrs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:56:34.682393+00:00
-- url     : https://prove2.me/theorems/9b76f8b2-64e4-4dc3-915c-789b90588156
-- title:
--   $\{0,1\}^n$ in lexicographic order
-- statement:
--   The list of all $2^n$ strings of length $n$ in lexicographic order with $0<1$. These are the loops "for $s'\in\{0,1\}^n$ by lexicographical order" of Algorithm 1.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Algorithm 1, p.75

import Mathlib

namespace NKtLB

/-- **`{0,1}^n` in lexicographic order** (the order of the loops of Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Algorithm 1, p.75:
"for `s′ ∈ {0,1}^n` by lexicographical order"), with `0 < 1`. -/
def allStrs : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allStrs n).map (List.cons false) ++ (allStrs n).map (List.cons true)

end NKtLB


