-- Prove2me | Definitions.Def_FourColorLinear_SepTree
-- name    : FourColorLinear_SepTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:16.445372+00:00
-- url     : https://prove2.me/theorems/a55fd253-3051-4b4c-b765-dd6bbec0a4ad
-- title:
--   The binary recursive subdivision of Appendix A, with its sizes
-- statement:
--   Appendix A embeds the recursive subdivision in a binary tree $T$ whose node $x$ represents a region $R(x)$; write $n(x)=|R(x)|$, $b(x)=|\partial R(x)|$. Here the tree keeps only these two numbers.
--
--   $S_r(x)$ is the set of highest descendants $y$ of $x$ with $n(y)\le r$. The **separator inequalities**, for nodes with $n(y)$ at least a constant $n_1$, say that the children have $n(y_i)\le n(y)$ and $n(y_0)+n(y_1)>n(y)$, and at depth $0$ mod $3$ also $\max\{n(y_0),n(y_1)\}\le 0.8\,n(y)$. They are the only properties of the construction of [15] that the proof of Lemma 13 uses, besides the sum bound in its statement.
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), App. A, pp.28–29

import Mathlib

namespace FourColorLinear

/-- The binary recursive subdivision of arXiv:2610.39753 (held version, sha256 4dce39c5…), App. A,
p.28, keeping of each node `x` only `n(x) = |R(x)|` and `b(x) = |∂R(x)|`. -/
inductive SepTree where
  | leaf (n b : ℕ) : SepTree
  | node (n b : ℕ) (l t : SepTree) : SepTree

namespace SepTree

/-- `n(x) = |R(x)|`. -/
def n : SepTree → ℕ
  | leaf n _ => n
  | node n _ _ _ => n

/-- `b(x) = |∂R(x)|`. -/
def b : SepTree → ℕ
  | leaf _ b => b
  | node _ b _ _ => b

/-- `S_r(x)`, p.28: "the set of the highest descendants y of x such that n(y) ≤ r (possibly y = x)". -/
def Sr (r : ℕ) : SepTree → List SepTree
  | leaf n b => if n ≤ r then [leaf n b] else []
  | node n b l t => if n ≤ r then [node n b l t] else Sr r l ++ Sr r t

/-- The inequalities of p.29 that the proof of Lemma 13 takes from [15], for nodes `y` with `n(y)`
at least the "large enough constant" `n₁`: "n(yi) ≤ n(y) and n(y0) + n(y1) > n(y). Moreover, if y is at
depth 0 mod 3 in T, then by [15, (2)], max{n(y0), n(y1)} ≤ 0.75n(y) + O(√n(y)) < 0.8n(y)". `d` is the
depth of the node in `T`; a leaf of `T` has `n < n₁`. -/
def IsSep (n₁ : ℕ) : ℕ → SepTree → Prop
  | _, leaf n _ => n < n₁
  | d, node n _ l t =>
      (n₁ ≤ n → l.n ≤ n ∧ t.n ≤ n ∧ n < l.n + t.n ∧
        (d % 3 = 0 → 10 * max l.n t.n ≤ 8 * n)) ∧
      IsSep n₁ (d + 1) l ∧ IsSep n₁ (d + 1) t

end SepTree

end FourColorLinear


