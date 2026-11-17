-- Prove2me | Definitions.Def_NAMatchEst_Supplement_templateMult
-- name    : NAMatchEst_Supplement_templateMult
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:36:56.378543+00:00
-- url     : https://prove2.me/theorems/4c75fa46-1cc7-41fe-9525-c7b666d29652
-- title:
--   Edge multiplicities of the yes, no and auxiliary templates of §7.1
-- statement:
--   The two **templates** of §7.1 are bipartite multigraphs on the nodes $A^S, B^S_i, C^S_j$ ($S\in\{L,R\}$). The number of edge occurrences $(X^L,Y^R)$ of each kind is:
--
--   1. **yes initial**: $\alpha$ parallel edges $(A^L,A^R)$ and one edge $(B^L_i,B^R_i)$ for every $i\in[\alpha]$;
--   2. **no initial**: one edge $(A^L,B^R_i)$ and one edge $(B^L_i,A^R)$ for every $i\in[\alpha]$;
--   3. **common auxiliary**: at stage $j\in[r-1]$ every older node $X$ on one side receives $2h_{j-1}-\deg_{j-1}(X)$ parallel edges to $C_j$ on the opposite side. At stage $1$ this is $\alpha$ edges from each $A^S$ and $2\alpha-1$ from each $B^S_i$; at a stage $j\ge2$ it is $h_{j-1}$ edges from $C^S_{j-1}$ and $2h_{j-1}-2h_{j-2}$ from every other older node.
--
--   The yes template consists of the kinds 1 and 3, the no template of the kinds 2 and 3. In both, every node other than $C_{r-1}$ has degree $b=2h_{r-2}$ and $C_{r-1}$ has degree $h=h_{r-1}$.
--
--   **Formalization Note** Kinds are `0`, `1`, `2` (`Fin 3`). The auxiliary count is written in the closed form the paper derives on p.93 from the degrees before each stage; a sanity file checks the resulting degrees for small parameters.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §7.1, pp.92–93 (PDF 96–97)

import Mathlib
import Definitions.Def_NAMatchEst_Supplement_HINode
import Definitions.Def_NAMatchEst_Supplement_hSeq

namespace NAMatchEst.Supplement

/-- The **edge multiplicities of the §7.1 templates**. `templateMult α r k X Y` is the number of
template edge occurrences `(X^L, Y^R)` (left node `X`, right node `Y`) of kind `k`:

* `k = 0`, the initial **yes** edges: `α` parallel edges `(A^L, A^R)` and one edge
  `(B^L_i, B^R_i)` for every `i ∈ [α]`;
* `k = 1`, the initial **no** edges: `(A^L, B^R_i)` and `(B^L_i, A^R)` for every `i ∈ [α]`;
* `k = 2`, the **common auxiliary** edges: at stage `j ∈ [r − 1]` every older node `X` on one
  side receives `2h_{j−1} − deg_{j−1}(X)` parallel edges to `C_j` on the opposite side. At stage 1
  this is `α` edges from each `A^S` and `2α − 1` from each `B^S_i`. At a stage `j ⩾ 2` it is
  `h_{j−1}` edges from `C^S_{j−1}` and `2h_{j−1} − 2h_{j−2}` from every other older node.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §7.1, pp.92–93
(PDF 96–97): "In the yes template, add α parallel edges (A^L, A^R) and one edge (B^L_i, B^R_i) for
every i ∈ [α]. In the no template, add (A^L, B^R_i) and (B^L_i, A^R) for every i ∈ [α]." and "At
stage 1, introduce C^L_1, C^R_1. Add α parallel edges from each A^S to C_1 on the opposite side and
2α − 1 from each B^S_i to C_1 on the opposite side. … In general, at stage j ∈ [r − 1], introduce
C^L_j, C^R_j. For an older node X, let deg_{j−1}(X) be its degree before this stage. Add
2h_{j−1} − deg_{j−1}(X) parallel edges from X to C_j on the opposite side. … For j ⩾ 2, the nodes
C^L_{j−1}, C^R_{j−1} previously had degree h_{j−1}, while the other α + j − 1 nodes on each side had
degree 2h_{j−2}."

**Formalization Note**
1. Nodes and stages are 0-based (`HINode`): `C j` is introduced at stage `j + 1`, and the nodes
   older than it are `A`, every `B i` and every `C j'` with `j' < j`.
2. The auxiliary count `2h_{j−1} − deg_{j−1}(X)` is written in the closed form the paper derives
   on p.93 (`deg_{j−1}(C_{j−1}) = h_{j−1}`, every other older node `2h_{j−2}`); a sanity file
   checks the resulting template degrees (`b` on every non-final node, `h` on `C_{r−1}`) for
   small parameters.
3. An auxiliary occurrence `(X^L, Y^R)` arises either from `X^L` older than `Y^R = C^R_j`, or
   from `Y^R` older than `X^L = C^L_j`; the two terms are added (at most one is nonzero).
4. A kind `k` other than `0`, `1`, `2` does not occur (`k : Fin 3`). -/
def templateMult (α r : ℕ) (k : Fin 3) (X Y : HINode α r) : ℕ :=
  /- number of stage-`(j+1)` edges from the older node `old` to the new node `C j` -/
  let stage : Fin (r - 1) → HINode α r → ℕ := fun j old =>
    if j.val = 0 then
      (match old with
        | HINode.A => α
        | HINode.B _ => 2 * α - 1
        | HINode.C _ => 0)
    else
      (match old with
        | HINode.C j' =>
            if j'.val + 1 = j.val then hSeq α j.val
            else if j'.val < j.val then 2 * hSeq α j.val - 2 * hSeq α (j.val - 1) else 0
        | _ => 2 * hSeq α j.val - 2 * hSeq α (j.val - 1))
  /- auxiliary edges from `old` (one side) to `new` (the opposite side) -/
  let aux : HINode α r → HINode α r → ℕ := fun old new =>
    match new with
      | HINode.C j => stage j old
      | _ => 0
  match k.val with
  | 0 =>
      (match X, Y with
        | HINode.A, HINode.A => α
        | HINode.B i, HINode.B i' => if i = i' then 1 else 0
        | _, _ => 0)
  | 1 =>
      (match X, Y with
        | HINode.A, HINode.B _ => 1
        | HINode.B _, HINode.A => 1
        | _, _ => 0)
  | _ => aux X Y + aux Y X

end NAMatchEst.Supplement


