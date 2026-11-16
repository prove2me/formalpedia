-- Prove2me | Definitions.Def_DetANN_HPIMFormat
-- name    : DetANN_HPIMFormat
-- status  : Definition
-- author  : @milia
-- created : 2026-11-16T05:50:38.481884+00:00
-- url     : https://prove2.me/theorems/4c637c6d-f314-4c5d-b057-f322d12941a9
-- title:
--   HPIM trees with box-decision lookups: data types and query semantics
-- statement:
--   Fix $m\ge1$.
--
--   1. A **box decision tree** is a binary tree whose inner nodes carry a box $[lo,hi]\subseteq\mathbb R^m$ and whose leaves carry an optional index. At a query $q$, an inner node continues in its first subtree if $q\in[lo,hi]$ and in its second subtree otherwise. `eval` is the value of the leaf reached, and `visits` is the number of nodes on the way.
--   2. An **HPIM tree** is either a single point (a global index $k$) or a node with $n$ local points (their global indices `glob`), a **ladder** $Z_0,\dots,Z_{M-1}$ of box decision trees, a number $t_0$, a child for each local point, and a child for the representatives.
--   3. **Lookups.** $Z_i(q)$ is the value of $Z_i$ at $q$ (null for $i\ge M$), and the clamped lookup reads $Z_{\min(i,M-1)}$. The **ladder search** `bisect` $(t,lo)$ returns $lo+1$ if $t=0$; otherwise it probes $lo+2^{t-1}$ and continues from there if that lookup is null, and from $lo$ otherwise.
--   4. **Search** at a node:
--      - if $Z_0(q)=i$, search the child of local point $i$;
--      - else, if $Z_{M-1}(q)$ is null, search the representatives' child;
--      - else answer the global index of $Z_{hi}(q)$, where $hi$ is the ladder search from $(t_0,0)$.
--
--      The **cost** counts one per tree node on the way, the visits of every lookup made, and one per ladder-search step.
--
--   This is the query side of a deterministic, floor-free version of the tree of Har-Peled, Indyk and Motwani (2012, §2), for `DetANN.lemma_3_3`. The ladder search uses only additions and doublings of indices, as the PNormReg machine has no division.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). The search tree follows Har-Peled, Indyk, Motwani, Approximate nearest neighbor: towards removing the curse of dimensionality, Theory of Computing 8 (2012), §2, made deterministic and floor-free.

import Mathlib

/-!
# HPIM trees with box-decision lookups: data types and query semantics

A deterministic, floor-free variant of the approximate-nearest-neighbour tree of
S. Har-Peled, P. Indyk, R. Motwani, *Approximate nearest neighbor: towards removing the curse of
dimensionality*, Theory of Computing 8 (2012), §2, written for `DetANN.lemma_3_3` (Y. Feng, P. Indyk,
*Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027 submission, p.7).

* `BoxTree m`: a binary decision tree whose inner nodes test `q ∈ [lo, hi]` and whose leaves hold
  `Option ℕ` (`none` = null, `some i` = a local index); `eval` and `visits` (nodes visited).
* `HTree m`: the search tree. An inner node has `n` local points with global indices `glob`, a ladder
  of `M` lookups `Z`, a child `kidOf i` for the component of each local point, and a child `reps` for
  the representatives.
* `lookup`, `lookupC` (clamped at the top of the ladder), `bisect` (binary search over the ladder by
  power-of-two steps, so no division is needed) and their costs.
* `HTree.search` and `HTree.cost`: the query and its cost in visited nodes.
-/

namespace DetANN.HPIM

/-- `q` lies in the closed box `[lo, hi]`. -/
def InBox {m : ℕ} (lo hi q : Fin m → ℝ) : Prop := ∀ j, lo j ≤ q j ∧ q j ≤ hi j

/-- A box decision tree. `test lo hi yes no` continues in `yes` if `q ∈ [lo, hi]`, else in `no`. -/
inductive BoxTree (m : ℕ) where
  | leaf (ans : Option ℕ)
  | test (lo hi : Fin m → ℝ) (yes no : BoxTree m)

namespace BoxTree

/-- The answer of the tree at `q`. -/
noncomputable def eval {m : ℕ} : BoxTree m → (Fin m → ℝ) → Option ℕ
  | .leaf a, _ => a
  | .test lo hi y n, q => by classical exact if InBox lo hi q then y.eval q else n.eval q

/-- The number of nodes visited at `q`. -/
noncomputable def visits {m : ℕ} : BoxTree m → (Fin m → ℝ) → ℕ
  | .leaf _, _ => 1
  | .test lo hi y n, q => by classical exact 1 + if InBox lo hi q then y.visits q else n.visits q

end BoxTree

/-- The HPIM12 tree: a single point (global index), or an inner node with `n` local points. -/
inductive HTree (m : ℕ) where
  | single (k : ℕ)
  | node (n M t₀ : ℕ) (Z : Fin M → BoxTree m) (glob : Fin n → ℕ) (kidOf : Fin n → HTree m)
      (reps : HTree m)

/-- The lookup `Z_i(q)`, `none` when `i` is out of range. -/
noncomputable def lookup {m M : ℕ} (Z : Fin M → BoxTree m) (i : ℕ) (q : Fin m → ℝ) : Option ℕ :=
  if h : i < M then (Z ⟨i, h⟩).eval q else none

/-- The visit count of the lookup `Z_i(q)` (`0` when `i` is out of range). -/
noncomputable def lookupCost {m M : ℕ} (Z : Fin M → BoxTree m) (i : ℕ) (q : Fin m → ℝ) : ℕ :=
  if h : i < M then (Z ⟨i, h⟩).visits q else 0

/-- The ladder lookup clamped at the top: indices `≥ M - 1` read `Z_{M-1}`. -/
noncomputable def lookupC {m M : ℕ} (Z : Fin M → BoxTree m) (i : ℕ) (q : Fin m → ℝ) : Option ℕ :=
  lookup Z (min i (M - 1)) q

/-- Visit count of `lookupC`. -/
noncomputable def lookupCCost {m M : ℕ} (Z : Fin M → BoxTree m) (i : ℕ) (q : Fin m → ℝ) : ℕ :=
  lookupCost Z (min i (M - 1)) q

/-- Binary search over the ladder by power-of-two steps (no pointer division needed). The invariant is
"`lookupC lo` is null and `lookupC (lo + 2^t)` is not". It returns `lo + 1` at `t = 0`. Started at
`t₀` (least with `2^t₀ ≥ M - 1`) and `lo = 0`. -/
noncomputable def bisect {m M : ℕ} (Z : Fin M → BoxTree m) (q : Fin m → ℝ) : ℕ → ℕ → ℕ
  | 0, lo => lo + 1
  | t + 1, lo => if lookupC Z (lo + 2 ^ t) q = none then bisect Z q t (lo + 2 ^ t) else bisect Z q t lo

/-- The cost of `bisect`: one unit plus the lookup visits per probe. -/
noncomputable def bisectCost {m M : ℕ} (Z : Fin M → BoxTree m) (q : Fin m → ℝ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | t + 1, lo => 1 + lookupCCost Z (lo + 2 ^ t) q +
      if lookupC Z (lo + 2 ^ t) q = none then bisectCost Z q t (lo + 2 ^ t) else bisectCost Z q t lo

/-- Turn a local answer into a global index (`0` if out of range; never happens for `hpimTree`). -/
def globOf {n : ℕ} (glob : Fin n → ℕ) (i : ℕ) : ℕ := if h : i < n then glob ⟨i, h⟩ else 0

namespace HTree

/-- The HPIM12 search (`hpim_spec.md` §3). Case (i): `Z_0` answers `i`, recurse into `kidOf i`.
Case (ii): `Z_{M-1}` is null, recurse into `reps`. Case (iii): bisect and answer `Z_hi`. -/
noncomputable def search {m : ℕ} : HTree m → (Fin m → ℝ) → ℕ
  | .single k, _ => k
  | .node n M t₀ Z glob kidOf reps, q =>
    match lookup Z 0 q with
    | some i => if h : i < n then (kidOf ⟨i, h⟩).search q else 0
    | none =>
      match lookup Z (M - 1) q with
      | none => reps.search q
      | some _ =>
        match lookupC Z (bisect Z q t₀ 0) q with
        | some i => globOf glob i
        | none => 0

/-- The query cost in visited nodes: one per HPIM level, plus the visits of every lookup made. -/
noncomputable def cost {m : ℕ} : HTree m → (Fin m → ℝ) → ℕ
  | .single _, _ => 1
  | .node n M t₀ Z _ kidOf reps, q =>
    1 + lookupCost Z 0 q +
    match lookup Z 0 q with
    | some i => if h : i < n then (kidOf ⟨i, h⟩).cost q else 0
    | none =>
      lookupCost Z (M - 1) q +
      match lookup Z (M - 1) q with
      | none => reps.cost q
      | some _ => bisectCost Z q t₀ 0 + lookupCCost Z (bisect Z q t₀ 0) q

end HTree

end DetANN.HPIM


