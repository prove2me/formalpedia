-- Prove2me | Definitions.Def_TriFormQ_queriesWhere
-- name    : TriFormQ_queriesWhere
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:44:28.35183+00:00
-- url     : https://prove2.me/theorems/b0a5e96f-5c09-4aa8-b16d-c194332da61e
-- title:
--   Number of queries of a given kind on a decision-tree path
-- statement:
--   For a deterministic decision tree $t$ (which at each node queries an index $i$ of the input and branches on the answer) and an input $x$, $\mathrm{queriesWhere}_P(t,x)$ is the number of queries on the path that $x$ follows whose index satisfies the property $P$.
--
--   Lemma 5 uses it with $P$ = "is a RightMult query" and $P$ = "is a LeftMult query" to bound the two kinds of queries separately.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 5, p.17 (PDF p.20)

import Definitions.Def_QAlgorithms_Defs_Classical

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 5, p.17 (PDF p.20):
"makes r + ⌈log_q 1/ε⌉ RightMult queries, at most r LeftMult queries". The number of queries on
the path that input `x` follows in the decision tree `t` whose query index satisfies `P`.

**Formalization Note.** A per-kind refinement of the platform's `QAlgorithms.DecisionTree.queries`
(which counts every query): Lemma 5 bounds the two kinds of queries separately. -/
def queriesWhere {ι κ α : Type} (P : ι → Prop) [DecidablePred P] :
    QAlgorithms.DecisionTree ι κ α → (ι → κ) → ℕ
  | .leaf _, _ => 0
  | .node i next, x => (if P i then 1 else 0) + queriesWhere P (next (x i)) x

end TriFormQ


