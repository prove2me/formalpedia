-- Prove2me | Definitions.Def_QWildMatch_pathCost
-- name    : QWildMatch_pathCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:16:16.320257+00:00
-- url     : https://prove2.me/theorems/b71dab46-6a32-42e1-a107-2657c52dd446
-- title:
--   Grid paths, their cost, and the threshold predicate $\mathrm{ED}_\mu\le k$
-- statement:
--   A grid path from $(0,s)$ to $(m,e)$ uses diagonal edges $(i,j)\to(i+1,j+1)$ of cost $\mu(P[i],T[j])$, vertical edges $(i,j)\to(i+1,j)$ of cost $c_{\mathrm{del}}(P[i])$, and horizontal edges $(i,j)\to(i,j+1)$ of cost $c_{\mathrm{ins}}(T[j])$. Its cost is the sum of its edge costs, and $\mathrm{ED}_\mu(P,w)$ is the minimum cost of a path for the word $w=T[s:e]$.
--
--   The predicate $\mathrm{ED}_\mu(P,w)\le k$ holds exactly when some path has cost at most $k$, and this threshold form is what every statement of the mission uses.
--
--   **Formalization Note** A path is a list of edge kinds, read from the corner $(0,s)$. A list that runs off the grid or stops before $(m,e)$ has cost $\top$ in `WithTop ℝ`, so paths are exactly the lists of finite cost. The predicate is defined by paths and not by the dynamic program, whose agreement with paths is the content of Theorem 4.1. The helpers `patternConsumed` and `textConsumed` count the symbols consumed by a prefix.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…), §3, p.4

import Mathlib
import Definitions.Def_QWildMatch_CostModel

namespace QWildMatch

/-- The three edge kinds of a grid path (Zhao et al., STOC 2027 submission (file sha256 9e87a9dd…),
§3, p.4): `diag` is `(i, j) → (i+1, j+1)`, `del` is the vertical `(i, j) → (i+1, j)`, and `ins` is the
horizontal `(i, j) → (i, j+1)`. -/
inductive Op
  | diag
  | del
  | ins
  deriving DecidableEq

/-- The cost of a grid path, given as its list of edges, from the corner `(0, s)` to `(m, e)`, where
`w = T[s : e]` (Zhao et al., STOC 2027 submission, §3, p.4): a diagonal edge costs `μ(P[i], T[j])`, a
vertical edge `c_del(P[i])`, a horizontal edge `c_ins(T[j])`, and the cost is the sum.

**Formalization Note** A list of edges that runs off the grid or stops before `(m, e)` has cost `⊤`,
so a path from `(0, s)` to `(m, e)` is exactly a list with finite cost. -/
noncomputable def pathCost {Sym : Type} (cm : CostModel Sym) :
    List (Option Sym) → List Sym → List Op → WithTop ℝ
  | [], [], [] => 0
  | a :: P, b :: w, Op.diag :: o => ((cm.μ a b : ℝ) : WithTop ℝ) + pathCost cm P w o
  | a :: P, w, Op.del :: o => ((cm.cdel a : ℝ) : WithTop ℝ) + pathCost cm P w o
  | P, b :: w, Op.ins :: o => ((cm.cins b : ℝ) : WithTop ℝ) + pathCost cm P w o
  | _, _, _ => ⊤

/-- Pattern symbols consumed by a prefix of edges: `i` = diagonals + deletions (Zhao et al., STOC
2027 submission, Lemma 3.1, p.4). -/
def patternConsumed (o : List Op) : ℕ := o.count Op.diag + o.count Op.del

/-- Text symbols consumed by a prefix of edges: `u` = diagonals + insertions (Zhao et al., STOC 2027
submission, Lemma 3.1, p.4). -/
def textConsumed (o : List Op) : ℕ := o.count Op.diag + o.count Op.ins

/-- The threshold predicate `ED_μ(P, w) ≤ k` (Zhao et al., STOC 2027 submission, §3, p.4).

**Formalization Note** `ED_μ` is the minimum path cost over a finite nonempty set of paths, so
`ED_μ ≤ k` holds exactly when some path has cost at most `k`; the threshold form is what every
statement uses. It is defined by paths and not by the dynamic program of §4, which is the subject of
`theorem_4_1`. -/
def EDle {Sym : Type} (cm : CostModel Sym) (P : List (Option Sym)) (w : List Sym) (k : ℝ) : Prop :=
  ∃ o : List Op, pathCost cm P w o ≤ ((k : ℝ) : WithTop ℝ)

end QWildMatch


