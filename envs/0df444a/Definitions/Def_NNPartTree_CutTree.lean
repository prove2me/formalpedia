-- Prove2me | Definitions.Def_NNPartTree_CutTree
-- name    : NNPartTree_CutTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:09.771249+00:00
-- url     : https://prove2.me/theorems/445903fd-f00b-4d7b-937e-c4ece75ff0d5
-- title:
--   Cut trees, regions and cost, perfect balanced halfspace trees, nearest neighbor distributions, the conditional mixture
-- statement:
--   A **cut tree** is a rooted binary tree with a cut at each internal node. A point $x$ walks from the root along the edge labeled by the cut's value, and a node $u$ is identified with its address, the list of labels from the root. The **region** $R_T(u)$ is the set of points whose walk passes through $u$.
--
--   $\mathcal D$ is a **nearest neighbor distribution** for $P=\{p_1,\dots,p_n\}$ if $(q,p^\star)\sim\mathcal D$ almost surely has $p^\star\in P$ with $p^\star$ minimizing $\|q-p\|_2$. $T$ is **$\beta$-balanced** if at every internal node $u$ with child $v$, $\mathcal D_Y(R_T(v))\ge\beta\,\mathcal D_Y(R_T(u))$. A **perfect $\beta$-balanced halfspace tree** has halfspaces at its internal nodes, exactly $n$ leaves, one for each point, with $T(p)=p$; it is $\beta$-balanced, and $T(q)=p^\star$ almost surely.
--
--   The **cost** is
--   $$\mathrm{cost}_{\mathcal D}(T)=\mathbf E_{(q,p^\star)\sim\mathcal D}\Big[\Pr_{p\sim\mathcal D_Y}\big[p\in R_T(\mathrm{LCA}_T(q,p^\star))\big]\Big],$$
--   with $\mathrm{LCA}_T(q,p^\star)$ the node at the longest common prefix of the two addresses.
--
--   The **conditional mixture** $\mathcal D^{(W)}$ draws $(q,p^\star)\sim\mathcal D$ conditioned on $p^\star\in W$, and outputs $(q,p^\star)$ if $q\in W$, else $(p^\star,p^\star)$. The **scan order** of a query lists the points of mass at least $\delta/(2n)$, once each, by nonincreasing common prefix with the address of $q$.
--
--   **Formalization Note** The perfect tree is that of §1. Bare Definition 6.1 has no condition on the leaves, so a single-leaf tree would be vacuously perfect and balanced. Masses are written $\mathcal D_Y(R_T(u))$, which equals $\Pr[p\in P^u]$ when $\mathcal D_Y$ lives on $P$. Cost is valued in $[0,\infty]$ and lies in $[0,1]$.
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), §1, pp.3–4; §6, p.21; Definition 6.1, Definition 6.2, Claim 6.1 proof, p.22; Definition 6.6, p.24

import Mathlib
import Definitions.Def_NNPartTree_Moments

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NNPartTree

/-!
# Cut trees, their regions and cost, perfect balanced trees, and the conditional mixture

S. Khanna, A. Padaki, E. Waingarten, *Learning Partition Trees for Nearest Neighbor Search*,
arXiv:2607.09909 (STOC 2027 submission), held copy of 2026-11-03, sha256 d32992f2…, §1, pp.3–4;
§6, p.21; Definitions 6.1, 6.2 (p.22), 6.6 (p.24).

**Formalization Note.**
* A node of a tree is an address: the list of edge labels from the root, `true` for the edge `+1` and
  `false` for the edge `−1`. `x` goes along the `+1` edge at a node with cut `g` iff `g x = 1`.
* `P^u` of the paper is `P ∩ R_T(u)`. In §6 the `y`-marginal is supported on `P`, so
  `Pr_{p∼D_nn}[p ∈ P^u]` is `D_Y(R_T(u))`, and this is how the mass is written here.
* `LCA_T(q, p★)` is the node whose address is the longest common prefix of the addresses of `q` and
  `p★`. When they reach the same leaf it is that leaf.
* `IsPerfectTree` is the tree of §1 (p.4), which has `n` leaves labeled by `P` with `T(p) = p`. Bare
  Definition 6.1 does not constrain the leaves, so the one-leaf tree would satisfy it vacuously, and
  the proof on p.25 contracts `T★` to pieces of small mass, which needs §1's leaves.
* `D` is a law on `ℝᵈ × ℝᵈ` throughout, and `IsNNDist` is the statement that it is a nearest neighbor
  pair distribution (§1, p.3). This covers the induced case of §6, p.21.
-/

variable {d : ℕ}

/-- A rooted binary tree with a function `ℝᵈ → ℝ` at each internal node (Definition 6.1, p.22). -/
inductive CutTree (d : ℕ) where
  | leaf : CutTree d
  | node (g : Pt d → ℝ) (minus plus : CutTree d) : CutTree d

namespace CutTree

open Classical in
/-- The address of the leaf reached by `x`: the route of `x` from the root. -/
noncomputable def addr : CutTree d → Pt d → List Bool
  | leaf, _ => []
  | node g m p, x => if g x = 1 then true :: addr p x else false :: addr m x

/-- The subtree at an address, if the address is a node of the tree. -/
def subtree : CutTree d → List Bool → Option (CutTree d)
  | t, [] => some t
  | leaf, _ :: _ => none
  | node _ m _, false :: u => subtree m u
  | node _ _ p, true :: u => subtree p u

/-- `u` is a node of `T`. -/
def IsNode (T : CutTree d) (u : List Bool) : Prop := (T.subtree u).isSome = true

/-- `u` is a leaf of `T`. -/
def IsLeaf (T : CutTree d) (u : List Bool) : Prop := T.subtree u = some leaf

/-- `u` is an internal node of `T`, labeled with the cut `g`. -/
def IsInternal (T : CutTree d) (u : List Bool) (g : Pt d → ℝ) : Prop :=
  ∃ m p, T.subtree u = some (node g m p)

/-- The addresses of all nodes of `T`. -/
def nodeAddrs : CutTree d → List (List Bool)
  | leaf => [[]]
  | node _ m p => [] :: (m.nodeAddrs.map (false :: ·) ++ p.nodeAddrs.map (true :: ·))

/-- The addresses of the internal nodes of `T`. -/
def internalAddrs : CutTree d → List (List Bool)
  | leaf => []
  | node _ m p => [] :: (m.internalAddrs.map (false :: ·) ++ p.internalAddrs.map (true :: ·))

/-- The depth of `T`. -/
def depth : CutTree d → ℕ
  | leaf => 0
  | node _ m p => 1 + max m.depth p.depth

/-- The routing region `R_T(u)`: the points whose walk down `T` arrives at `u` (Definition 6.1,
p.22). It has a meaning for the nodes `u` of `T`. -/
def region (T : CutTree d) (u : List Bool) : Set (Pt d) := {x | u <+: T.addr x}

/-- Every internal node of `T` holds a cut (Definition 6.1, p.22). -/
def IsCutTree (T : CutTree d) : Prop := ∀ u g, T.IsInternal u g → IsCut g

/-- `T` is `β`-balanced: at every internal node `u` and each child `v`,
`Pr_{p∼D_nn}[p ∈ P^v] ≥ β · Pr_{p∼D_nn}[p ∈ P^u]` (§1, p.4; Definition 6.1, p.22). -/
def IsBalanced (T : CutTree d) (D : Measure (Pt d × Pt d)) (β : ℝ) : Prop :=
  ∀ u g, T.IsInternal u g → ∀ b : Bool,
    ENNReal.ofReal β * marginalY D (T.region u) ≤ marginalY D (T.region (u ++ [b]))

end CutTree

/-- The longest common prefix of two addresses. -/
def commonPrefix : List Bool → List Bool → List Bool
  | a :: u, b :: v => if a = b then a :: commonPrefix u v else []
  | _, _ => []

/-- `D` is a nearest neighbor pair distribution for `P`: `(q, p★) ∼ D` has `p★ ∈ P` minimizing
`‖q − p★‖₂` (§1, p.3). -/
def IsNNDist {n : ℕ} (P : Fin n → Pt d) (D : Measure (Pt d × Pt d)) : Prop :=
  ∀ᵐ z ∂D, ∃ i, z.2 = P i ∧ ∀ j, ‖z.1 - P i‖ ≤ ‖z.1 - P j‖

/-- A perfect `β`-balanced halfspace tree for `(P, D)` (§1, p.4): every internal node holds a halfspace;
the leaves are exactly the addresses of the points of `P`, one leaf per point, so that `T` has `n`
leaves and `T(p) = p`; `T` is `β`-balanced; and `(q, p★) ∼ D` satisfies `T(q) = p★` almost surely. -/
structure IsPerfectTree {n : ℕ} (P : Fin n → Pt d) (D : Measure (Pt d × Pt d)) (β : ℝ)
    (T : CutTree d) : Prop where
  halfspaces : ∀ u g, T.IsInternal u g → IsHalfspace g
  leaves_inj : Function.Injective fun i => T.addr (P i)
  leaves_surj : ∀ u, T.IsLeaf u → ∃ i, T.addr (P i) = u
  balanced : T.IsBalanced D β
  perfect : ∀ᵐ z ∂D, T.addr z.1 = T.addr z.2

/-- The cost `cost_D(T) = E_{(q,p★)∼D}[Pr_{p∼D_nn}[p ∈ P^{LCA_T(q,p★)}]]` (Definition 6.2, p.22),
valued in `[0, ∞]`; it lies in `[0, 1]`. -/
noncomputable def cost (D : Measure (Pt d × Pt d)) (T : CutTree d) : ℝ≥0∞ :=
  ∫⁻ z, marginalY D (T.region (commonPrefix (T.addr z.1) (T.addr z.2))) ∂D

open Classical in
/-- The map of Definition 6.6: keep `(q, p★)` if `q ∈ W`, otherwise output `(p★, p★)`. -/
noncomputable def mixMap (W : Set (Pt d)) (z : Pt d × Pt d) : Pt d × Pt d :=
  if z.1 ∈ W then z else (z.2, z.2)

/-- The conditional mixture (Definition 6.6, p.24), for `W = R_T(u)`: draw `(q, p★) ∼ D` conditioned on
`p★ ∈ W`; output `(q, p★)` if `q ∈ W`, otherwise `(p★, p★)`. It is a probability measure when `W` is
measurable with `D_Y(W) > 0`. -/
noncomputable def condMix (D : Measure (Pt d × Pt d)) (W : Set (Pt d)) : Measure (Pt d × Pt d) :=
  (ProbabilityTheory.cond D (Prod.snd ⁻¹' W)).map (mixMap W)

/-- The scan order of the proof of Claim 6.1 (p.22): the list `L` holds exactly the points of mass at least `δ/(2n)`, once each,
in the bottom-up order of `T` from the leaf of `q`, that is, by nonincreasing length of the common prefix with `addr q`. -/
def IsBottomUpScan {n : ℕ} (P : Fin n → Pt d) (D : Measure (Pt d × Pt d)) (δ : ℝ) (T : CutTree d)
    (q : Pt d) (L : List (Fin n)) : Prop :=
  L.Nodup ∧ (∀ i, i ∈ L ↔ ENNReal.ofReal (δ / (2 * n)) ≤ marginalY D {P i}) ∧
    L.Pairwise fun i j =>
      (commonPrefix (T.addr q) (T.addr (P j))).length ≤ (commonPrefix (T.addr q) (T.addr (P i))).length

end NNPartTree


