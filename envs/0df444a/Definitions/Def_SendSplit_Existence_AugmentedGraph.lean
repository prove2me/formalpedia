-- Prove2me | Definitions.Def_SendSplit_Existence_AugmentedGraph
-- name    : SendSplit_Existence_AugmentedGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:12:24.294701+00:00
-- url     : https://prove2.me/theorems/1fef6932-04ec-47b3-87c8-90878de01b70
-- title:
--   Section 2 — strong components, the augmented graph $\underline{G}$, slopes $\dot c_{ij}(\infty)$, arc costs $\underline{c}$, chain costs $\underline{\pi}$
-- statement:
--   A **chain** from $i$ to $j$ is a directed walk (repeated nodes allowed). Nodes $i, j$ are in the same **strong component** of $G$ if there are chains from $i$ to $j$ and from $j$ to $i$. An arc lies *in* a strong component if both ends are in the same one, and otherwise *joins distinct* strong components. A strong component is a **sink** if there is no chain from it to a different strong component.
--
--   The **augmented graph** $\underline{G}$ appends a node $\nu$ to $N$ and an arc $(i, \nu)$ for each $i$ in a set $S$ that contains exactly one node of each sink strong component and no other node. The **slope at infinity** of an arc cost is
--
--   $$\dot c_{ij}(\infty) = \lim_{\lambda\to\infty} \dot c_{ij}(\lambda) \in [-\infty, \infty),$$
--
--   where $\dot c_{ij}(\lambda)$ is the right-hand derivative of $c_{ij}$ at $\lambda$. The arc costs $\underline{c}$ on $\underline{G}$ are $\underline{c}_{ij} = \dot c_{ij}(\infty)$ for each arc $(i,j)$ in a strong component of $G$, and arbitrary real numbers $b_{ij}$ (arcs of $G$ joining distinct strong components) and $b^\nu_i$ (appended arcs $(i,\nu)$) otherwise. The **cost of a chain** in $\underline{G}$ is the sum of the costs of its arcs, and
--
--   $$\underline{\pi}_i = \inf\{\text{cost of } P : P \text{ a chain in } \underline{G} \text{ from } i \text{ to } \nu\} \in [-\infty, +\infty].$$
--
--   A **minimum-cost chain** from a node $u$ of $\underline{G}$ to $\nu$ is a chain from $u$ to $\nu$ whose cost is a real number and is at most the cost of every chain from $u$ to $\nu$.
--
--   These objects state conditions 6° and 7° of Theorem 1.
--
--   **Formalization Note** $\underline{G}$ has node type `Option (Fin n)`, with `none` the appended node $\nu$; a chain is a list of nodes whose consecutive pairs are arcs of $\underline{G}$ (`List.IsChain`), and its cost is an `EReal` sum. Because $c_{ij}$ is concave on $[0,\infty)$, its right derivative exists on $(0,\infty)$ and is nonincreasing, so its limit at infinity equals its infimum; `slopeAtInfty` is defined as that infimum $\inf_{t>0}$ of `derivWithin (c i j) (Set.Ioi t) t`, an `EReal` that may be $-\infty$. Arc costs are never $+\infty$, so chain sums never meet $\top + \bot$. "Minimum-cost chain" requires a real cost: otherwise a chain through an arc of cost $-\infty$ would count as a minimum.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 639, Section 2

import Mathlib
import Definitions.Def_SendSplit_Existence_Network

namespace SendSplit.Existence

variable {n : ℕ}

/-- There is a chain (directed walk, possibly of length zero) from `i` to `j` in `G`. -/
def Reach (G : ArcGraph n) (i j : Fin n) : Prop :=
  Relation.ReflTransGen (fun a b => (a, b) ∈ G.A) i j

/-- `i` and `j` lie in the same strong component of `G`. -/
def SameComponent (G : ArcGraph n) (i j : Fin n) : Prop :=
  Reach G i j ∧ Reach G j i

/-- The strong component of `i` is a sink component: there is no chain from it to a
different strong component. -/
def InSinkComponent (G : ArcGraph n) (i : Fin n) : Prop :=
  ∀ j, Reach G i j → Reach G j i

/-- `S` contains exactly one node of each sink strong component of `G` and no other node:
the nodes `i` for which the augmented graph gets the arc `(i, ν)`. -/
def IsSinkSelection (G : ArcGraph n) (S : Finset (Fin n)) : Prop :=
  (∀ s ∈ S, InSinkComponent G s) ∧
    ∀ i, InSinkComponent G i → ∃! s, s ∈ S ∧ SameComponent G i s

/-- `ċ(∞) = lim_{t → ∞} ċ(t)`, where `ċ(t)` is the right-hand derivative of `f` at `t`.
For `f` concave on `[0, ∞)` the right derivative exists on `(0, ∞)` and is nonincreasing,
so its limit at infinity is the infimum over `t > 0`; the value lies in `[-∞, ∞)`. -/
noncomputable def slopeAtInfty (f : ℝ → ℝ) : EReal :=
  ⨅ (t : ℝ) (_ : 0 < t), ((derivWithin f (Set.Ioi t) t : ℝ) : EReal)

/-- The arcs of the augmented graph `G̲` on the nodes `Option (Fin n)`, where `none` is the
appended node `ν`: the arcs `(i, j)` of `G`, and the arcs `(i, ν)` for `i ∈ S`. -/
def AugArc (G : ArcGraph n) (S : Finset (Fin n)) : Option (Fin n) → Option (Fin n) → Prop
  | some i, some j => (i, j) ∈ G.A
  | some i, none => i ∈ S
  | none, _ => False

/-- `l` is a chain (directed walk) in `G̲` from `u` to `w`, listed by its nodes. -/
def IsAugChain (G : ArcGraph n) (S : Finset (Fin n)) (u w : Option (Fin n))
    (l : List (Option (Fin n))) : Prop :=
  l.IsChain (AugArc G S) ∧ l.head? = some u ∧ l.getLast? = some w

/-- The cost of a chain `l` under the arc costs `cost`: the sum of the costs of its arcs. -/
noncomputable def chainCost (cost : Option (Fin n) → Option (Fin n) → EReal) (l : List (Option (Fin n))) :
    EReal :=
  (List.zipWith cost l l.tail).sum

/-- The arc costs `c̲` of `G̲`: `c̲_ij = ċ_ij(∞)` for an arc `(i, j)` inside a strong component
of `G`; the real number `b i j` for an arc `(i, j)` of `G` joining distinct strong components;
the real number `bν i` for an appended arc `(i, ν)`. -/
noncomputable def augCost (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (b : Fin n → Fin n → ℝ) (bν : Fin n → ℝ) : Option (Fin n) → Option (Fin n) → EReal
  | some i, some j =>
      haveI := Classical.dec (SameComponent G i j)
      if SameComponent G i j then slopeAtInfty (c i j) else ((b i j : ℝ) : EReal)
  | some i, none => ((bν i : ℝ) : EReal)
  | none, _ => 0

/-- `π̲_i`: the infimum of the costs of the chains in `G̲` from node `i` to `ν`
(`⊤` if there is none). -/
noncomputable def minChainCost (G : ArcGraph n) (S : Finset (Fin n))
    (cost : Option (Fin n) → Option (Fin n) → EReal) (i : Fin n) : EReal :=
  ⨅ (l : List (Option (Fin n))) (_ : IsAugChain G S (some i) none l), chainCost cost l

/-- There is a minimum-cost chain from `u` to `ν` in `G̲`: a chain of real cost that is at
most the cost of every chain from `u` to `ν`. -/
def HasMinCostChain (G : ArcGraph n) (S : Finset (Fin n))
    (cost : Option (Fin n) → Option (Fin n) → EReal) (u : Option (Fin n)) : Prop :=
  ∃ l, IsAugChain G S u none l ∧ chainCost cost l ≠ ⊥ ∧ chainCost cost l ≠ ⊤ ∧
    ∀ l', IsAugChain G S u none l' → chainCost cost l ≤ chainCost cost l'

end SendSplit.Existence


