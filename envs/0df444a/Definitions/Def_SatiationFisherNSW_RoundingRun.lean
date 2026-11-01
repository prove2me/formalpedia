-- Prove2me | Definitions.Def_SatiationFisherNSW_RoundingRun
-- name    : SatiationFisherNSW_RoundingRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:44.542632+00:00
-- url     : https://prove2.me/theorems/96456d06-eb5b-44f4-843a-22a4b18a2c28
-- title:
--   The rounding procedure for a thrifty and modest equilibrium (choices, kept children, recursion path, output)
-- statement:
--   The **rounding procedure** turns a thrifty and modest equilibrium $(x,p)$ of the Fisher market of an instance into an integral allocation. It works on the allocation graph with edges $\{i,j\}$ for $x_{ij}>0$, assumed to be a forest.
--
--   *Preprocessing.* (a) Each tree gets a root agent, which orients every edge from parent to child. (b) Every good $j$ keeps at most one child agent: a child agent $i$ that buys the largest amount $x_{ij}$ among the child agents of $j$ (ties broken arbitrarily), and only if
--   $$
--   m^a_i/2<p_j\quad(p_j>0),\qquad\qquad u_{ij}x_{ij}>c_i/2\quad(p_j=0).
--   $$
--   (c) The other child agents are cut off from $j$ and become roots.
--
--   *Rounding.* (a) Goods without a kept child go to their parent agent. (b) In each remaining tree, the root agent takes a child good $g$ maximizing its fractional value $u_{ag}x_{ag}$, every other good outside the subtree of $g$ goes to its child agent, and the child agent of $g$ becomes the root of that subtree; this is repeated. The agents that become roots form the **recursion path** $a_1,g_1,a_2,\dots,g_\ell,a_{\ell+1}$, and $k_i$ is the number of children of $a_i$.
--
--   A **run** records the free choices: the parent pointers from the root choice, the largest child of each good, and the good picked by each agent. A run is **valid** if the parent pointers orient exactly the edges of the allocation graph and are acyclic with agents as roots, each largest child is a maximizer among the child agents, and each pick is a maximizer among the remaining child goods. From a run one defines the kept children, the forest after preprocessing and its tree components $T$ (with their agents, goods, remaining goods, path goods and the product $k_1\cdots k_\ell$), the valuation of each agent after preprocessing, the recursion path, and the output allocation.
--
--   **Formalization Note** The price of a good selects the rule of Preprocessing (b): trees of $(B\setminus B_0)\times(G\setminus G_0)$ use the active-budget threshold (§4.1.2) and zero-price trees of $B_0\times G_0$ use the utility threshold (Appendix B). A valid run exists only if the allocation graph is a forest. The recursion of Rounding (b) is encoded by the recursion path (an inductive predicate) and the rule "a picked good on the path goes to its parent agent, every other remaining good to its child agent". Goods that nobody buys are not assigned.
-- source:
--   Garg, Hoefer, Mehlhorn, Satiation in Fisher markets and approximation of Nash social welfare, arXiv:1707.04428v3 (31 Jul 2019), https://arxiv.org/abs/1707.04428v3, §4.1.2, pp.26–27 (Preprocessing, Rounding, recursion path), and Appendix B, pp.33–34

import Mathlib
import Definitions.Def_SatiationFisherNSW_FisherMarket
open scoped Classical

namespace SatiationFisherNSW

/-- The choices made by one run of the rounding procedure of arXiv:1707.04428v3, §4.1.2,
pp.26–27, and Appendix B, pp.33–34. Which choices are admissible is `RoundingRun.IsValid`.

* `parentAgent j`, `parentGood i`: the rooted forest produced by Preprocessing (a) ("assign some
  agent to be a root node" of each tree): the parent agent of good `j` and the parent good of
  agent `i` (`none` for a root agent, and for an item not bought by anybody).
* `largestChild j`: the child agent of `j` that buys the largest amount of `j` among the child
  agents of `j` (Preprocessing (b), "ties are broken arbitrarily").
* `pick a`: the child good chosen by agent `a` in Rounding (b) when it is the root of the current
  tree, one that gives it the maximum value in the fractional solution. -/
structure RoundingRun (B G : Type*) where
  parentAgent : G → Option B
  parentGood : B → Option G
  largestChild : G → Option B
  pick : B → Option G

namespace RoundingRun

variable {B G : Type*} [Fintype B] [Fintype G]
variable (R : RoundingRun B G) (M : FisherMarket B G) (x : B → G → ℝ) (p : G → ℝ)

/-- The threshold of Preprocessing (b) for keeping the designated child agent `i` of good `j`:
`m^a_i/2 < p_j` on trees of positive-price goods (§4.1.2, p.26), and `u_{ij} x_{ij} > c_i/2` on
zero-price trees (Appendix B, p.34).

**Formalization Note** Every tree of the allocation graph of a thrifty and modest equilibrium
lies either in `(B \ B₀) × (G \ G₀)` or in `B₀ × G₀` (p.24), so the price of the good decides
which of the two rules of the paper applies. -/
def KeepCond (i : B) (j : G) : Prop :=
  if p j = 0 then M.c i / 2 < M.u i j * x i j else M.activeBudget p i / 2 < p j

/-- The child agent that good `j` keeps after Preprocessing (b): the designated largest child if
it meets the threshold `KeepCond`, and none otherwise. All other child agents of `j` are cut off
from `j` and become roots (Preprocessing (c)). -/
noncomputable def keptChild (j : G) : Option B :=
  match R.largestChild j with
  | none => none
  | some i => if KeepCond M x p i j then some i else none

/-- `g` is a child good of `a` that is still present at the beginning of Rounding (b): its parent
agent is `a`, and it kept a child agent (otherwise it was assigned to `a` in Rounding (a)). -/
def IsRemainingChild (a : B) (g : G) : Prop :=
  R.parentAgent g = some a ∧ R.keptChild M x p g ≠ none

/-- The admissible runs of the procedure.

1. `parentAgent`/`parentGood` orient every edge of the allocation graph from parent to child,
   each good that is bought by somebody has a parent agent (roots are agents), and the parent
   pointers are acyclic (a rank function decreases towards the roots). Such an orientation is
   exactly the choice of one root agent in every tree component of the allocation graph
   (Preprocessing (a)); it exists only if that graph is a forest.
2. `largestChild j` is a child agent of `j` buying the largest amount `x_{ij}` among the child
   agents of `j`, and is `none` exactly when `j` has no child agent (Preprocessing (b)).
3. `pick a` is a remaining child good `g` of `a` maximizing the fractional value
   `u_{ag} x_{ag}` among the remaining child goods of `a`, and is `none` exactly when `a` has no
   remaining child good (Rounding (b)).

**Formalization Note** Every tie-break of the paper is a free choice, and the theorems quantify
over all valid runs. The allocation graph `(B ∪ G, E)`, `E = {{i, j} | x_{ij} > 0}`, of an
equilibrium has a valid run only if it is a forest, which the paper assumes "without loss of
generality" (p.26). -/
def IsValid : Prop :=
  (∀ i j, 0 < x i j ↔ (R.parentAgent j = some i ∨ R.parentGood i = some j)) ∧
  (∀ i j, ¬ (R.parentAgent j = some i ∧ R.parentGood i = some j)) ∧
  (∀ j, (∃ i, 0 < x i j) → R.parentAgent j ≠ none) ∧
  (∃ rk : B ⊕ G → ℕ,
    (∀ i j, R.parentAgent j = some i → rk (Sum.inl i) < rk (Sum.inr j)) ∧
    (∀ i j, R.parentGood i = some j → rk (Sum.inr j) < rk (Sum.inl i))) ∧
  (∀ j i, R.largestChild j = some i →
    R.parentGood i = some j ∧ ∀ i', R.parentGood i' = some j → x i' j ≤ x i j) ∧
  (∀ j, R.largestChild j = none → ∀ i, R.parentGood i ≠ some j) ∧
  (∀ a g, R.pick a = some g →
    R.IsRemainingChild M x p a g ∧
      ∀ g', R.IsRemainingChild M x p a g' → M.u a g' * x a g' ≤ M.u a g * x a g) ∧
  (∀ a, R.pick a = none → ∀ g, ¬ R.IsRemainingChild M x p a g)

/-- Agent `a` is a root after preprocessing: an original root, or an agent cut off from its
parent good in Preprocessing (b) (Preprocessing (c)). -/
def IsPPRoot (a : B) : Prop :=
  ∀ j, R.parentGood a = some j → R.keptChild M x p j ≠ some a

/-- The agents of the recursion path of Rounding (b) (p.27): the root of each tree after
preprocessing is on the path, and if `b` is on the path and picks the child good `g`, then the
child agent of `g` is on the path (it becomes the root of the newly created tree). -/
inductive OnPath : B → Prop
  | root (a : B) : R.IsPPRoot M x p a → OnPath a
  | step (a b : B) (g : G) : OnPath b → R.pick b = some g → R.keptChild M x p g = some a →
      OnPath a

/-- The integral allocation produced by the run (Rounding (a) and (b), p.27).

* A good without a kept child goes to its parent agent (Rounding (a)).
* A good `g` with a kept child goes to its parent agent `b` if `b` is on the recursion path and
  picked `g`; otherwise it goes to its child agent ("Except in the subtree rooted at `j`, assign
  each good to its child agent in the remaining tree").
* A good that nobody buys (an isolated vertex of the allocation graph) is not assigned. -/
noncomputable def output : G → Option B := fun j =>
  match R.parentAgent j with
  | none => none
  | some b =>
    match R.keptChild M x p j with
    | none => some b
    | some a => if R.OnPath M x p b ∧ R.pick b = some j then some b else some a

/-- The forest after preprocessing: every parent edge (good to its parent agent) and every edge
from a good to its kept child agent. -/
def ppGraph : SimpleGraph (B ⊕ G) :=
  SimpleGraph.fromRel fun a b =>
    match a, b with
    | Sum.inl i, Sum.inr j => R.parentAgent j = some i ∨ R.keptChild M x p j = some i
    | _, _ => False

/-- The valuation of agent `i` after preprocessing, `min(c_i, Σ_j u_{ij} x_{ij})` over the goods
still adjacent to `i` (its child goods, and its parent good if it is kept). -/
noncomputable def ppUtility (i : B) : ℝ :=
  min (M.c i) (∑ j ∈ Finset.univ.filter
    (fun j => R.parentAgent j = some i ∨ R.keptChild M x p j = some i), M.u i j * x i j)

/-- The agents of a tree component `T` of the forest after preprocessing. -/
noncomputable def agentsOf (T : (R.ppGraph M x p).ConnectedComponent) : Finset B :=
  Finset.univ.filter (fun i => (R.ppGraph M x p).connectedComponentMk (Sum.inl i) = T)

/-- The goods of a tree component `T` of the forest after preprocessing, including the goods
assigned to its agents in Rounding (a). -/
noncomputable def goodsOf (T : (R.ppGraph M x p).ConnectedComponent) : Finset G :=
  Finset.univ.filter (fun j => (R.ppGraph M x p).connectedComponentMk (Sum.inr j) = T)

/-- The goods of `T` still present at the beginning of Rounding (b): `k_T` is their number. -/
noncomputable def remainingGoodsOf (T : (R.ppGraph M x p).ConnectedComponent) : Finset G :=
  (R.goodsOf M x p T).filter (fun j => R.keptChild M x p j ≠ none)

/-- The goods `g₁, …, g_ℓ` of the recursion path in `T` (p.27): `ℓ` is their number. -/
noncomputable def pathGoodsOf (T : (R.ppGraph M x p).ConnectedComponent) : Finset G :=
  (R.remainingGoodsOf M x p T).filter (fun j => ∃ a, R.OnPath M x p a ∧ R.pick a = some j)

/-- The number of children of agent `a` at the beginning of Rounding (b). -/
noncomputable def numChildren (a : B) : ℕ :=
  (Finset.univ.filter (fun g => R.IsRemainingChild M x p a g)).card

/-- The product `k₁ ⋯ k_ℓ` of the numbers of children of the path agents `a₁, …, a_ℓ` of `T`
(the path agents that pick a good; `a_{ℓ+1}` picks none) (p.27). -/
noncomputable def pathChildProduct (T : (R.ppGraph M x p).ConnectedComponent) : ℕ :=
  ∏ a ∈ (R.agentsOf M x p T).filter (fun a => R.OnPath M x p a ∧ R.pick a ≠ none),
    R.numChildren M x p a

/-- `T` is a tree of `(B \ B₀) × (G \ G₀)` (§4.1.2, p.26): it has an agent, and no agent of `B₀`. -/
def IsPriceTree (T : (R.ppGraph M x p).ConnectedComponent) : Prop :=
  (R.agentsOf M x p T).Nonempty ∧ ∀ a ∈ R.agentsOf M x p T, ¬ M.InB0 p a

/-- `T` is a zero-price tree of `B₀ × G₀` (Appendix B, p.33): it has an agent, and all its
agents lie in `B₀`. -/
def IsZeroPriceTree (T : (R.ppGraph M x p).ConnectedComponent) : Prop :=
  (R.agentsOf M x p T).Nonempty ∧ ∀ a ∈ R.agentsOf M x p T, M.InB0 p a

end RoundingRun

end SatiationFisherNSW


