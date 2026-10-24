-- Prove2me | Definitions.Def_SignalSearch_Tree_Model
-- name    : SignalSearch_Tree_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:36:56.948249+00:00
-- url     : https://prove2.me/theorems/457b3dbb-858e-4652-b530-411360242de0
-- title:
--   §4–§5, pp. 5–11 — the search game G(Q, O, p) on a rooted tree with signals of accuracy p: expected search time, mean depth D, λ̄, favoring bias β, Table 1
-- statement:
--   This file sets up the search game $G(Q,O,p)$ of Alpern and Lidbetter and the quantities in which its solution is expressed.
--
--   **Trees.** A rooted tree $Q$ with root $O$ and arc lengths is built from three constructors: a single arc of length $\ell$ from $O$ to a leaf node; an arc of length $\ell$ from $O$ to the root of a subtree $Q'$ (the root has degree one); and a **branch node** $O$ with two **branches** $Q_1$ and $Q_2$, both rooted at $O$. The total length is $\mu(Q)$, the distance from the root to a leaf node $v$ is $d(O,v)$, and $L$ is the set of leaf nodes. The predicate *positive lengths* says that every arc has positive length.
--
--   **The game (§4, pp. 5–6).** Fix $\tfrac12<p\le 1$ and write $q=1-p$. The Hider picks a leaf node. The Searcher performs a depth-first search from $O$ at unit speed. On arriving at a branch node on the way to the Hider she receives a signal naming the branch containing the Hider, correct with probability $p$ and wrong with probability $q$, and chooses which branch to search first as a function of the signal: one of the four actions $[1,1]$ (always branch 1), $[2,2]$ (always branch 2), $[1,2]$ = **follow** the signal, $[2,1]$ = **opposite**. A pure Searcher strategy fixes an action at every branch node. If she enters the branch not containing the Hider first, she searches it completely and returns, at cost twice its length. The payoff $T(s,v)$ is the expected time for the pure strategy $s$ to reach the leaf $v$:
--   $$T(s,v)=d(O,v)+\sum_{j}\Pr[\text{$s$ enters the wrong branch first at $j$}]\cdot 2\mu(\text{wrong branch at }j),$$
--   the sum over the branch nodes $j$ on the path from $O$ to $v$. The game is the finite zero-sum game with this payoff matrix (rows: leaves, the maximizing Hider; columns: pure Searcher strategies, the minimizer); its value and optimal (min-max, max-min) strategies are those of the published matrix-game vocabulary.
--
--   **Mean depth (Definition 3, p. 7).** For weights $\lambda$ on $L$,
--   $$D(Q,O,\lambda)=\sum_{v\in L}\lambda(v)\,d(O,v).$$
--
--   **The Hider distribution $\bar\lambda$ (Definition 4 and (1), pp. 7–8).** By recursion: on a single arc $\bar\lambda=1$ at its leaf; at a root of degree one, $\bar\lambda_Q=\bar\lambda_{Q'}$; at a branch root with branches $Q_1,Q_2$ of lengths $\mu_1,\mu_2$ and mean depths $D_{Q_i}=D(Q_i,\bar\lambda^i)$, the **favored branch** $Q_f$ is the one of larger mean depth and $Q_u$ is the other, and
--   $$\bar\lambda(v)=\frac{p\mu_f}{p\mu_f+q\mu_u}\,\bar\lambda^f(v)\ (v\in Q_f),\qquad \bar\lambda(v)=\frac{q\mu_u}{p\mu_f+q\mu_u}\,\bar\lambda^u(v)\ (v\in Q_u).$$
--   The mean depth of $Q$ is $D_Q=D(Q,O,\bar\lambda)$.
--
--   **Favoring bias (3), p. 9.** At a branch node with branches $Q_f$ (favored) and $Q_u$,
--   $$\beta=\frac{(p-q)(D_{Q_f}-D_{Q_u})}{2(p\mu_f+q\mu_u)}.$$
--   The **favoring-bias strategy** chooses, independently at every branch node, the constant action "favored branch first" with probability $\beta$ and "follow" with probability $1-\beta$, where $\beta$ and the favored branch are those of that node's own two branches.
--
--   **Table 1 (p. 11).** For lengths $\mu_1,\mu_2$ and numbers $V_1,V_2$, the $2\times4$ matrix with rows the Hider's branch and columns the four actions:
--   $$\begin{array}{c|cccc} & [1,1] & [2,2] & [1,2] & [2,1]\\\hline 1 & V_1 & 2\mu_2+V_1 & q\cdot2\mu_2+V_1 & p\cdot2\mu_2+V_1\\ 2 & 2\mu_1+V_2 & V_2 & q\cdot2\mu_1+V_2 & p\cdot2\mu_1+V_2\end{array}$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Trees are the inductive type `RTree` (`arc`, `cons`, `fork`); it also contains trees with interior nodes of degree two and with forks whose branches start with a fork, which is the paper's own conversion by zero-length arcs (p. 5). Leaves and branch nodes are inductive families `Leaf t`, `BNode t` with sorry-free `Fintype` and `DecidableEq` instances. Signals and branches are `Bool` (`false` = branch 1) and an action is a map `Bool → Bool` (follow = `id`, opposite = `not`). The payoff `time` is the expected time computed from each path node's signal marginal; signals off the path do not affect it (p. 6), so no joint law of the signals is needed. On a tie $D_{Q_1}=D_{Q_2}$ branch 1 is favored (then $\beta=0$). `table1` is written through the column's two choices $[X,Y]$ and reproduces the four printed columns. Mixed strategies are probability vectors over all pure strategies.
-- source:
--   Alpern, Lidbetter, Search for an Immobile Hider on a Binary Tree with Unreliable Locational Information, arXiv:2303.13378v2, pp. 5–11, §4 (pp. 5–6), Definition 3 (p. 7), Definition 4 and eq. (1) (pp. 7–8), eq. (3) and Theorem 7 (iii) (pp. 9–10), Table 1 (p. 11)

import Mathlib
import Definitions.Def_ZeroSumLP_DantzigExt_MatrixGame

namespace SignalSearch.Tree

/-!
Alpern & Lidbetter, *Search for an Immobile Hider on a Binary Tree with Unreliable Locational
Information*, arXiv:2303.13378v2: the game `G(Q, O, p)` of §4 (pp. 5–6), the mean depth
(Definition 3, p. 7), the Hider distribution `λ̄` (Definition 4 and (1), pp. 7–8), the favoring bias
`β` ((3), p. 9) and the payoff matrix of Table 1 (p. 11).

The matrix-game vocabulary (min-max / max-min strategies and the value of a finite zero-sum game,
rows = the maximizing player, columns = the minimizing player) is the published
`ZeroSumLP.DantzigExt.MatrixGame`.
-/

open ZeroSumLP.DantzigExt

/-- A rooted tree with arc lengths; its root is `O`.
* `arc ℓ`: a single arc of length `ℓ` from `O` to a leaf node;
* `cons ℓ t`: an arc of length `ℓ` from `O` to the root of `t` (the root `O` has degree one);
* `fork t₁ t₂`: `O` is a branch node with branches `t₁` (branch 1) and `t₂` (branch 2), both
  rooted at `O`.

Every binary tree of §4 (p. 5) with positive arc lengths is an `RTree`; an `RTree` may in addition
have interior nodes of degree two and forks whose branches begin with a fork (the paper's own
conversion by arcs of length zero, p. 5). -/
inductive RTree where
  | arc (ℓ : ℝ) : RTree
  | cons (ℓ : ℝ) (t : RTree) : RTree
  | fork (t₁ t₂ : RTree) : RTree

namespace RTree

/-- Every arc of the tree has positive length. -/
def PosLengths : RTree → Prop
  | arc ℓ => 0 < ℓ
  | cons ℓ t => 0 < ℓ ∧ t.PosLengths
  | fork t₁ t₂ => t₁.PosLengths ∧ t₂.PosLengths

/-- `μ(Q)`, the total length of the tree. -/
def length : RTree → ℝ
  | arc ℓ => ℓ
  | cons ℓ t => ℓ + t.length
  | fork t₁ t₂ => t₁.length + t₂.length

end RTree

/-- The leaf nodes of `t` (the Hider's pure strategies, p. 5). -/
inductive Leaf : RTree → Type where
  | tip (ℓ : ℝ) : Leaf (.arc ℓ)
  | down (ℓ : ℝ) {t : RTree} : Leaf t → Leaf (.cons ℓ t)
  | left {t₁ : RTree} (t₂ : RTree) : Leaf t₁ → Leaf (.fork t₁ t₂)
  | right (t₁ : RTree) {t₂ : RTree} : Leaf t₂ → Leaf (.fork t₁ t₂)

/-- The branch nodes of `t`: the root of every `fork` occurring in `t`. -/
inductive BNode : RTree → Type where
  | root (t₁ t₂ : RTree) : BNode (.fork t₁ t₂)
  | down (ℓ : ℝ) {t : RTree} : BNode t → BNode (.cons ℓ t)
  | left {t₁ : RTree} (t₂ : RTree) : BNode t₁ → BNode (.fork t₁ t₂)
  | right (t₁ : RTree) {t₂ : RTree} : BNode t₂ → BNode (.fork t₁ t₂)

/-! ### Finiteness (structural) -/

/-- The single leaf of an arc. -/
def Leaf.equivArc (ℓ : ℝ) : Leaf (.arc ℓ) ≃ Unit where
  toFun _ := ()
  invFun _ := .tip ℓ
  left_inv v := by cases v; rfl
  right_inv _ := rfl

/-- The leaves of `cons ℓ t` are those of `t`. -/
def Leaf.equivCons (ℓ : ℝ) (t : RTree) : Leaf (.cons ℓ t) ≃ Leaf t where
  toFun | .down _ v => v
  invFun v := .down ℓ v
  left_inv v := by cases v; rfl
  right_inv _ := rfl

/-- The leaves of `fork t₁ t₂` are those of `t₁` and those of `t₂`. -/
def Leaf.equivFork (t₁ t₂ : RTree) : Leaf (.fork t₁ t₂) ≃ Leaf t₁ ⊕ Leaf t₂ where
  toFun
    | .left _ v => .inl v
    | .right _ v => .inr v
  invFun
    | .inl v => .left t₂ v
    | .inr v => .right t₁ v
  left_inv v := by cases v <;> rfl
  right_inv v := by cases v <;> rfl

/-- An arc has no branch node. -/
instance BNode.isEmpty_arc (ℓ : ℝ) : IsEmpty (BNode (.arc ℓ)) := ⟨fun j => nomatch j⟩

/-- The branch nodes of `cons ℓ t` are those of `t`. -/
def BNode.equivCons (ℓ : ℝ) (t : RTree) : BNode (.cons ℓ t) ≃ BNode t where
  toFun | .down _ j => j
  invFun j := .down ℓ j
  left_inv j := by cases j; rfl
  right_inv _ := rfl

/-- The branch nodes of `fork t₁ t₂`: its root (`none`), and those of `t₁` and of `t₂`. -/
def BNode.equivFork (t₁ t₂ : RTree) : BNode (.fork t₁ t₂) ≃ Option (BNode t₁ ⊕ BNode t₂) where
  toFun
    | .root _ _ => none
    | .left _ j => some (.inl j)
    | .right _ j => some (.inr j)
  invFun
    | none => .root t₁ t₂
    | some (.inl j) => .left t₂ j
    | some (.inr j) => .right t₁ j
  left_inv j := by cases j <;> rfl
  right_inv j := by rcases j with _ | j | j <;> rfl

/-- `Leaf t` is finite. -/
@[instance_reducible]
def Leaf.fintype : (t : RTree) → Fintype (Leaf t)
  | .arc ℓ => Fintype.ofEquiv Unit (Leaf.equivArc ℓ).symm
  | .cons ℓ t => @Fintype.ofEquiv _ _ (Leaf.fintype t) (Leaf.equivCons ℓ t).symm
  | .fork t₁ t₂ =>
      @Fintype.ofEquiv _ _ (@instFintypeSum _ _ (Leaf.fintype t₁) (Leaf.fintype t₂))
        (Leaf.equivFork t₁ t₂).symm

instance (t : RTree) : Fintype (Leaf t) := Leaf.fintype t

/-- `BNode t` is finite. -/
@[instance_reducible]
def BNode.fintype : (t : RTree) → Fintype (BNode t)
  | .arc _ => ⟨∅, fun j => nomatch j⟩
  | .cons ℓ t => @Fintype.ofEquiv _ _ (BNode.fintype t) (BNode.equivCons ℓ t).symm
  | .fork t₁ t₂ =>
      @Fintype.ofEquiv _ _
        (@instFintypeOption _ (@instFintypeSum _ _ (BNode.fintype t₁) (BNode.fintype t₂)))
        (BNode.equivFork t₁ t₂).symm

instance (t : RTree) : Fintype (BNode t) := BNode.fintype t

/-- `BNode t` has decidable equality. -/
@[instance_reducible]
def BNode.decEq : (t : RTree) → DecidableEq (BNode t)
  | .arc _ => fun j => nomatch j
  | .cons ℓ t => @Equiv.decidableEq _ _ (BNode.equivCons ℓ t) (BNode.decEq t)
  | .fork t₁ t₂ =>
      letI := BNode.decEq t₁
      letI := BNode.decEq t₂
      Equiv.decidableEq (BNode.equivFork t₁ t₂)

instance (t : RTree) : DecidableEq (BNode t) := BNode.decEq t

/-! ### The game `G(Q, O, p)` (§4, pp. 5–6) -/

/-- `d(O, v)`, the distance from the root to the leaf `v`. -/
def depth : {t : RTree} → Leaf t → ℝ
  | _, .tip ℓ => ℓ
  | _, .down ℓ v => ℓ + depth v
  | _, .left _ v => depth v
  | _, .right _ v => depth v

/-- The two branches at a branch node `j` of `t` (branch 1, branch 2). -/
def BNode.branches : {t : RTree} → BNode t → RTree × RTree
  | _, .root t₁ t₂ => (t₁, t₂)
  | _, .down _ j => j.branches
  | _, .left _ j => j.branches
  | _, .right _ j => j.branches

/-- A branch choice depending on the signal: `a σ` is the branch searched first when the signal is
`σ` (`false` = branch 1, `true` = branch 2). The four actions of p. 6 are
`[1, 1] = fun _ => false`, `[2, 2] = fun _ => true`, "follow" `= id` and "opposite" `= not`. -/
abbrev Action := Bool → Bool

/-- A pure Searcher strategy: the action used on (first) arrival at each branch node (p. 6). -/
abbrev SPure (t : RTree) := BNode t → Action

/-- At a branch node, with the Hider in branch `b`, the signal is `b` with probability `p` and
`!b` with probability `q = 1 - p` (p. 6). `wrongFirst p a b` is the probability that the action `a`
searches the other branch `!b` first. -/
def wrongFirst (p : ℝ) (a : Action) (b : Bool) : ℝ :=
  p * (if a b = b then 0 else 1) + (1 - p) * (if a (!b) = b then 0 else 1)

/-- The expected time `E[T]` for the depth-first search with pure strategy `s` to reach the leaf
`v` at unit speed (§4, pp. 5–6). Along the arc into a `cons` the Searcher spends `ℓ`. At a branch
node on the way to `v` she receives the signal; if she enters the branch not containing `v` first,
she covers it and returns, at cost twice its length, and then continues in the branch containing
`v`. Signals at branch nodes off the path to `v` do not affect the time to reach `v` (p. 6), and
the expected time depends only on the marginal law of the signal at each node of the path, so no
joint law of the signals is needed. -/
def time (p : ℝ) : (t : RTree) → SPure t → Leaf t → ℝ
  | .arc ℓ, _, .tip _ => ℓ
  | .cons ℓ t, s, .down _ v => ℓ + time p t (fun j => s (.down ℓ j)) v
  | .fork t₁ t₂, s, .left _ v =>
      wrongFirst p (s (.root t₁ t₂)) false * (2 * t₂.length) +
        time p t₁ (fun j => s (.left t₂ j)) v
  | .fork t₁ t₂, s, .right _ v =>
      wrongFirst p (s (.root t₁ t₂)) true * (2 * t₁.length) +
        time p t₂ (fun j => s (.right t₁ j)) v

/-- The payoff matrix of `G(Q, O, p)`: rows are the Hider's pure strategies (leaf nodes, the
maximizer), columns the Searcher's pure strategies (the minimizer); the entry is the expected
search time. -/
def payoff (p : ℝ) (t : RTree) : Matrix (Leaf t) (SPure t) ℝ := fun v s => time p t s v

/-- `V` is the value of the game `G(Q, O, p)`. -/
def IsValue (p : ℝ) (t : RTree) (V : ℝ) : Prop := IsGameValue (payoff p t) V

/-! ### Mean depth and `λ̄` (Definitions 3 and 4, pp. 7–8) -/

/-- Definition 3, p. 7: the mean depth `D(Q, O, λ) = ∑_{v ∈ L} λ(v) d(O, v)` of `t` with respect to
a weighting `λ` of its leaf nodes. -/
def meanDepthWrt (t : RTree) (lam : Leaf t → ℝ) : ℝ := ∑ v, lam v * depth v

/-- Definition 4 and (1), pp. 7–8: the Hider distribution `λ̄_Q`, by recursion on the tree.
* A single arc: `λ̄(A) = 1`.
* Root of degree one: the distribution of the subtree.
* Branch root with branches `Q₁ = t₁`, `Q₂ = t₂`, lengths `μ₁, μ₂` and mean depths
  `D_i = D(Q_i, λ̄^i)`: branch 1 is favored iff `D₂ ≤ D₁`. The favored branch `f` receives weight
  `p μ_f / (p μ_f + q μ_u)` and the other branch `u` weight `q μ_u / (p μ_f + q μ_u)`, `q = 1 - p`,
  each multiplied by the branch's own `λ̄`. On a tie `D₁ = D₂` branch 1 is favored. -/
noncomputable def hiderDist (p : ℝ) : (t : RTree) → Leaf t → ℝ
  | .arc _, _ => 1
  | .cons _ t, .down _ v => hiderDist p t v
  | .fork t₁ t₂, .left _ v =>
      let D₁ := ∑ w, hiderDist p t₁ w * depth w
      let D₂ := ∑ w, hiderDist p t₂ w * depth w
      (if D₂ ≤ D₁ then
          p * t₁.length / (p * t₁.length + (1 - p) * t₂.length)
        else
          (1 - p) * t₁.length / (p * t₂.length + (1 - p) * t₁.length)) *
        hiderDist p t₁ v
  | .fork t₁ t₂, .right _ v =>
      let D₁ := ∑ w, hiderDist p t₁ w * depth w
      let D₂ := ∑ w, hiderDist p t₂ w * depth w
      (if D₂ ≤ D₁ then
          (1 - p) * t₂.length / (p * t₁.length + (1 - p) * t₂.length)
        else
          p * t₂.length / (p * t₂.length + (1 - p) * t₁.length)) *
        hiderDist p t₂ v

/-- `D_Q`, the mean depth of `t` with respect to `λ̄` (Definition 3 with `λ = λ̄`, p. 7). -/
noncomputable def meanDepth (p : ℝ) (t : RTree) : ℝ := meanDepthWrt t (hiderDist p t)

/-- Branch 1 of `fork t₁ t₂` is the favored branch: `D_{Q₂} ≤ D_{Q₁}` (Definition 4, p. 7; ties
go to branch 1). As a signal/branch index the favored branch is `false` (branch 1) or `true`
(branch 2). -/
noncomputable def favored (p : ℝ) (t₁ t₂ : RTree) : Bool :=
  if meanDepth p t₂ ≤ meanDepth p t₁ then false else true

/-- (3), p. 9: the favoring bias at a branch node with branches `t₁, t₂`,
`β = (p - q)(D_{Q_f} - D_{Q_u}) / (2(p μ_f + q μ_u))`, where `f` is the favored and `u` the other
branch. -/
noncomputable def bias (p : ℝ) (t₁ t₂ : RTree) : ℝ :=
  if meanDepth p t₂ ≤ meanDepth p t₁ then
    (p - (1 - p)) * (meanDepth p t₁ - meanDepth p t₂) /
      (2 * (p * t₁.length + (1 - p) * t₂.length))
  else
    (p - (1 - p)) * (meanDepth p t₂ - meanDepth p t₁) /
      (2 * (p * t₂.length + (1 - p) * t₁.length))

/-- The favoring-bias law of actions at a branch node with branches `t₁, t₂` (Theorem 7 (iii),
pp. 9–10): the constant action "search the favored branch first" with probability `β`, "follow the
signal" (`id`) with probability `1 - β`, and the other two actions with probability `0`. -/
noncomputable def nodeLaw (p : ℝ) (t₁ t₂ : RTree) (a : Action) : ℝ :=
  if a false = favored p t₁ t₂ ∧ a true = favored p t₁ t₂ then bias p t₁ t₂
  else if a false = false ∧ a true = true then 1 - bias p t₁ t₂
  else 0

/-- The favoring-bias Searcher strategy as a mixed strategy on `SPure t`: independently at every
branch node `j`, the action is drawn from `nodeLaw` of `j`'s own two branches. -/
noncomputable def favoringStrategy (p : ℝ) (t : RTree) : SPure t → ℝ :=
  fun s => ∏ j : BNode t, nodeLaw p j.branches.1 j.branches.2 (s j)

/-! ### Table 1 (p. 11) -/

/-- Table 1, p. 11: the 2 × 4 payoff matrix of the game at a branch root, given the values
`V₁, V₂` of the games on the branches and their lengths `μ₁, μ₂`. The row is the Hider's branch
(`false` = 1, `true` = 2); the column is the action `[X, Y]` with `X = a false`, `Y = a true` the
branch searched first on signal 1, resp. 2. Row 1: `V₁` plus `2μ₂` times the probability of
searching `Q₂` first (`p` for `X = 2`, `q` for `Y = 2`); row 2 symmetrically. This gives the
columns `[1,1]: (V₁, 2μ₁ + V₂)`, `[2,2]: (2μ₂ + V₁, V₂)`, follow `[1,2]: (q·2μ₂ + V₁, q·2μ₁ + V₂)`,
opposite `[2,1]: (p·2μ₂ + V₁, p·2μ₁ + V₂)`. -/
def table1 (p μ₁ μ₂ V₁ V₂ : ℝ) : Matrix Bool Action ℝ
  | false, a =>
      (p * (if a false = true then 1 else 0) + (1 - p) * (if a true = true then 1 else 0)) *
        (2 * μ₂) + V₁
  | true, a =>
      (p * (if a true = false then 1 else 0) + (1 - p) * (if a false = false then 1 else 0)) *
        (2 * μ₁) + V₂

end SignalSearch.Tree


