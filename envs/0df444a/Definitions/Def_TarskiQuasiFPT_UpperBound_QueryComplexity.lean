-- Prove2me | Definitions.Def_TarskiQuasiFPT_UpperBound_QueryComplexity
-- name    : TarskiQuasiFPT_UpperBound_QueryComplexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:45.785678+00:00
-- url     : https://prove2.me/theorems/ae3f5deb-cb6c-46fb-b32a-9443ac676fa5
-- title:
--   Decision trees on $[n]^k$ and the query complexities Tarski$(n,k)$, Tarski$^*(n,k)$, SafeTarski$^*(n,k)$
-- statement:
--   In the black-box model an algorithm is given $n,k$ and oracle access to an unknown function on $[n]^k$; in each round it chooses a query point $x$ and receives the **entire** value $f(x)$ (for the starred problems, the vector together with its label). Queries may depend on earlier answers, and computation between queries is free. A deterministic algorithm is therefore a **decision tree**: an internal node queries a point and branches on the full answer, a leaf outputs a point. Against an oracle $f$ the tree follows one path; its output is the leaf reached and its number of queries is the number of internal nodes on that path (a repeated query is charged again). The points queried on that path, in order, are recorded as $\mathrm{queried}(T,f)$.
--
--   The three deterministic query complexities are minima of worst-case query counts:
--
--   1. $\mathrm{Tarski}(n,k)$ (§1): the least $d$ such that some tree outputs a fixed point $f(x)=x$ of every monotone $f:[n]^k\to[n]^k$ with at most $d$ queries;
--   2. $\mathrm{Tarski}^*(n,k)$ (Definition 2): the least $d$ such that some tree outputs a solution of every monotone $f:[n]^k\to[n]^k\times\{\pm1\}$ with at most $d$ queries, with $\mathrm{Tarski}^*(n,0)=1$ by convention;
--   3. $\mathrm{SafeTarski}^*(n,k)$ (Definition 4): the same over safe $f$, with $\mathrm{SafeTarski}^*(n,0)=1$ by convention.
--
--   These quantities are the subject of the recurrence (Theorem 5), of the reduction (Lemma 1), of the equivalence (Theorem 4) and of the main bound (Theorem 2).
--
--   **Formalization Note** Trees are the published `QAlgorithms.DecisionTree ι κ α` with `eval` (output) and `queries` (query count); the answer type is the full answer type. Each complexity is the `sInf` in $\mathbb N$ of the set of achievable worst-case bounds; this set is nonempty for $n\ge1$ (query every point), so the infimum is attained. Upper bounds in the mission are stated as the existence of a tree, never as an inequality on this `sInf`. The conventions at $k=0$ are part of the definitions.
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, §1 (query model and Tarski(n,k), PDF p. 2 / printed p. 1), Definition 2 (PDF p. 4 / printed p. 3), Definition 4 (PDF p. 5 / printed p. 4)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid

set_option autoImplicit false

namespace TarskiQuasiFPT.UpperBound

/-! # Deterministic query algorithms and the complexities `Tarski`, `Tarski*`, `SafeTarski*`

Chen, Gao, Li, Rubinstein, Yannakakis, *Tarski Fixed Points in Quasi-FPT Queries*,
STOC 2027 submission #403, §1 (PDF p. 2), Definitions 2 and 4 (PDF pp. 4–5).

A deterministic adaptive query algorithm is a decision tree
`QAlgorithms.DecisionTree ι κ α` (published definition layer): at a `node i next` it queries
the point `i` and continues with `next (f i)`, where `f i` is the **entire** answer; at a
`leaf a` it outputs `a`. `DecisionTree.eval T f` is the output and `DecisionTree.queries T f`
the number of queries on the path followed against the oracle `f` (every query costs 1,
repeated queries included). Leaves never see `f`. -/

open QAlgorithms

variable {n k : ℕ}

/-- The list of points queried by `T` against the oracle `f`, in order (the query nodes on the
path that `f` follows). Its length is `T.queries f`. -/
def queriedPoints {ι κ α : Type*} : DecisionTree ι κ α → (ι → κ) → List ι
  | .leaf _, _ => []
  | .node i next, f => i :: queriedPoints (next (f i)) f

/-- `Tarski(n, k)` (§1): the deterministic query complexity of finding a fixed point of a
monotone `f : [n]^k → [n]^k`, i.e. the least `d` such that one decision tree, querying points
and receiving the whole vector `f(x)`, outputs a fixed point of every monotone `f` with at
most `d` queries. -/
noncomputable def tarskiQC (n k : ℕ) : ℕ :=
  sInf {d : ℕ | ∃ T : DecisionTree (Point n k) (Point n k) (Point n k),
    ∀ f : Point n k → Point n k, Monotone f → f (T.eval f) = T.eval f ∧ T.queries f ≤ d}

/-- `Tarski*(n, k)` (Definition 2): the deterministic query complexity of finding a solution of a
monotone `f : [n]^k → [n]^k × {±1}` (a query returns the whole pair `f(x)`), with
`Tarski*(n, 0) = 1` by convention. -/
noncomputable def tarskiStarQC (n k : ℕ) : ℕ :=
  if k = 0 then 1 else
  sInf {d : ℕ | ∃ T : DecisionTree (Point n k) (Point n k × Label) (Point n k),
    ∀ f : Point n k → Point n k × Label, Monotone f → IsSolution f (T.eval f) ∧ T.queries f ≤ d}

/-- `SafeTarski*(n, k)` (Definition 4): the deterministic query complexity of finding a solution of
a **safe** `f : [n]^k → [n]^k × {±1}`, with `SafeTarski*(n, 0) = 1` by convention. -/
noncomputable def safeTarskiStarQC (n k : ℕ) : ℕ :=
  if k = 0 then 1 else
  sInf {d : ℕ | ∃ T : DecisionTree (Point n k) (Point n k × Label) (Point n k),
    ∀ f : Point n k → Point n k × Label, IsSafe f → IsSolution f (T.eval f) ∧ T.queries f ≤ d}

end TarskiQuasiFPT.UpperBound


