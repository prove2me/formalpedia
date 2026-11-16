-- Prove2me | Definitions.Def_DetANN_HPIMBSP
-- name    : DetANN_HPIMBSP
-- status  : Definition
-- author  : @milia
-- created : 2026-11-16T05:51:34.206225+00:00
-- url     : https://prove2.me/theorems/e9ff8ac6-be4e-489d-9499-48cdea8dd1e9
-- title:
--   Binary space partitions with boxes, and their centroid balancing
-- statement:
--   1. A **BSP** in $\mathbb R^m$ is either a leaf (a box and an optional answer) or a cut (a box and two sub-BSPs). Nodes are addressed by paths in $\{\text{left},\text{right}\}^*$; `paths` is the set of node paths, `sub` the subtree at a path, `box` and `ans` the box and answer of a node (inner nodes answer null).
--   2. $T$ **covers** if at every cut, each point of the cut's box lies in the box of one of its two children.
--   3. For a path $p$ and a set $R$ of removed paths, $\mathrm{comp}(p,R)$ is the set of nodes below $p$ (including $p$) that are not below any removed node.
--   4. The **centroid** of $\mathrm{comp}(p,R)$ is the node $c\ne p$ in it that minimizes
--   $$\max\bigl(|\mathrm{comp}(c,R)|,\ |\mathrm{comp}(p,R)|-|\mathrm{comp}(c,R)|\bigr),$$
--   with ties going to the least path in lexicographic order.
--   5. **Balancing** $(f,p,R)$ builds a box decision tree (definition `DetANN_HPIMFormat`). If $|\mathrm{comp}(p,R)|\le1$ it is the leaf holding the answer of node $p$. Otherwise, with $c$ the centroid, it tests $q\in\mathrm{box}(c)$; on *yes* it continues with $(f-1,c,R)$, and on *no* with $(f-1,p,R\cup\{c\})$.
--
--   **Formalization Note.** The fuel $f$ bounds the recursion depth so that the definition needs no termination proof; it returns a null leaf when the fuel is exhausted. The fuel $|T|+1$ is never exhausted.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). The search tree follows Har-Peled, Indyk, Motwani, Approximate nearest neighbor: towards removing the curse of dimensionality, Theory of Computing 8 (2012), §2, made deterministic and floor-free. The balancing is the standard centroid decomposition of a tree.

import Mathlib
import Definitions.Def_DetANN_HPIMFormat

/-!
# Binary space partitions and their centroid balancing

* `BSP m`: a binary space partition of a box in `ℝ^m` whose nodes carry their boxes. A leaf answers
  `none` or `some i`. Nodes are addressed by paths (`false` = left, `true` = right): `sub`, `paths`,
  `box`, `ans`.
* `BSP.Covers`: at every cut, each point of the box lies in the box of one of the two children.
* `balance T f p R`: the box decision tree obtained by centroid decomposition of the part of the
  subtree at `p` that is not below a removed node of `R`. It tests `q` against the box of the centroid
  node `c` (the node minimizing `max(size below c, size of the rest)`; ties go to the least path in
  lexicographic order), continues in the subtree of `c` on *yes* and in the rest on *no*.

Used by the lookup structures of the HPIM tree (definition `DetANN_HPIMFormat`).
-/

namespace DetANN.HPIM

variable {m : ℕ}

/-- A BSP whose nodes carry their boxes. A leaf answers `none` (OUT) or `some i` (IN, local index). -/
inductive BSP (m : ℕ) where
  | leaf (lo hi : Fin m → ℝ) (ans : Option ℕ)
  | cut (lo hi : Fin m → ℝ) (left right : BSP m)

namespace BSP

/-- The subtree at a path (`false` = left, `true` = right). -/
def sub : BSP m → List Bool → Option (BSP m)
  | t, [] => some t
  | .leaf .., _ :: _ => none
  | .cut _ _ l _, false :: p => l.sub p
  | .cut _ _ _ r, true :: p => r.sub p

/-- All node paths. -/
def paths : BSP m → Finset (List Bool)
  | .leaf .. => {[]}
  | .cut _ _ l r => insert [] ((l.paths.image (List.cons false)) ∪ (r.paths.image (List.cons true)))

/-- The box of a node. -/
def box : BSP m → (Fin m → ℝ) × (Fin m → ℝ)
  | .leaf lo hi _ => (lo, hi)
  | .cut lo hi _ _ => (lo, hi)

/-- The answer of a node (`none` for inner nodes). -/
def ans : BSP m → Option ℕ
  | .leaf _ _ a => a
  | .cut .. => none

end BSP

/-- The nodes of the subtree at `p` that are not below a removed node in `R`. -/
def comp (T : BSP m) (p : List Bool) (R : Finset (List Bool)) : Finset (List Bool) :=
  T.paths.filter fun x => p <+: x ∧ ∀ c ∈ R, ¬ c <+: x

/-- The centroid of `comp T p R`: among the nodes `c ≠ p`, minimize `max(sz c, total − sz c)`; ties
go to the least path in lexicographic order (preorder). -/
def centroid (T : BSP m) (p : List Bool) (R : Finset (List Bool)) : Option (List Bool) :=
  let C := comp T p R
  let score := fun c => max (comp T c R).card (C.card - (comp T c R).card)
  let cands := C.erase p
  if h : cands.Nonempty then
    let best := cands.filter fun c => score c = cands.inf' h score
    if hb : best.Nonempty then some (best.min' hb) else none
  else none

/-- Centroid balancing: test `q ∈ box c`; *yes* continues in subtree(c), *no* in the rest. -/
noncomputable def balance (T : BSP m) : ℕ → List Bool → Finset (List Bool) → BoxTree m
  | 0, _, _ => .leaf none
  | f + 1, p, R =>
    if (comp T p R).card ≤ 1 then .leaf ((T.sub p).bind BSP.ans) else
      match centroid T p R with
      | none => .leaf ((T.sub p).bind BSP.ans)
      | some c =>
        match T.sub c with
        | none => .leaf none
        | some tc => .test tc.box.1 tc.box.2 (balance T f c R) (balance T f p (insert c R))

namespace BSP

/-- The children of every cut cover its box. -/
def Covers : BSP m → Prop
  | .leaf .. => True
  | .cut lo hi l t =>
    (∀ q, InBox lo hi q → InBox l.box.1 l.box.2 q ∨ InBox t.box.1 t.box.2 q) ∧ Covers l ∧ Covers t

end BSP

end DetANN.HPIM


