-- Prove2me | Definitions.Def_DDNNFNeg_BDD_Reach
-- name    : DDNNFNeg_BDD_Reach
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:21:58.964342+00:00
-- url     : https://prove2.me/theorems/568f7959-7e8d-41c3-9b5e-8dd5c5697970
-- title:
--   Reachability in a branching program
-- statement:
--   For vertices $i, j$ of a branching program, $j$ is **reachable** from $i$ if there is a directed path (possibly of length $0$) from $i$ to $j$ along the edges of the program.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Definition 3.2, p.9

import Mathlib
import Definitions.Def_DDNNFNeg_BDD

namespace DDNNFNeg

/-- `B.Reach i j`: the vertex `j` of the branching program `B` is reachable from the vertex
`i` by a directed path (of length `≥ 0`) along the edges of `B`
(Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), Definition 3.2, p.9). -/
def BDD.Reach {X : Type*} (B : BDD X) : Fin B.size → Fin B.size → Prop :=
  Relation.ReflTransGen (fun i j =>
    (∃ v lo hi, B.node i = .test v lo hi ∧ (j = lo ∨ j = hi)) ∨
    (∃ l r, B.node i = .choice l r ∧ (j = l ∨ j = r)))

end DDNNFNeg


