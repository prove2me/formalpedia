-- Prove2me | Definitions.Def_InterpOptStop_SAA_TreePolicy
-- name    : InterpOptStop_SAA_TreePolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:03.580152+00:00
-- url     : https://prove2.me/theorems/60d92234-51ef-47a9-963f-d3dbf725fc38
-- title:
--   §3.3–§3.4, pp. 6–9 — tree policies π(x; 𝒯, v, θ, a), depth, splits, and the class Πtree(d)
-- statement:
--   This file defines the **tree policies** of Ciocan and Mišić (§3.3) and the class $\Pi_{\mathrm{tree}}(d)$ of tree policies of depth at most $d$ (§3.4).
--
--   A tree policy is given by a binary tree. Each **split node** $s$ carries a split variable index $v(s)\in\{1,\dots,n\}$ and a split point $\theta_s\in\mathbb R$, and asks the query $x_{v(s)}\le\theta_s$. If the answer is yes the state goes to the left child, otherwise to the right child. Each **leaf** $\ell$ carries an action $a(\ell)\in\{\mathbf{stop},\mathbf{go}\}$. The complete tree is the tuple $(\mathcal T,\mathbf v,\boldsymbol\theta,\mathbf a)$ of topology, split variable indices, split points and leaf actions. The policy $\pi(\mathbf x;\mathcal T,\mathbf v,\boldsymbol\theta,\mathbf a)$ is the action of the leaf that $\mathbf x$ reaches:
--   $$\pi(\mathbf x;\mathcal T,\mathbf v,\boldsymbol\theta,\mathbf a)=a\big(\ell(\mathbf x;\mathcal T,\mathbf v,\boldsymbol\theta)\big).$$
--   The set $\mathbf{splits}$ is the set of split nodes. The **depth** of a tree is the number of split nodes on its longest root-to-leaf path. $\Pi_{\mathrm{tree}}(d)$ is the set of tree policies of depth at most $d$ with arbitrary real split points.
--
--   The skeleton $(\mathcal T,\mathbf v,\mathbf a)$ ranges over a finite set once the depth is bounded, but the split points $\boldsymbol\theta\in\mathbb R^{\mathbf{splits}}$ do not. That is what makes the uniform convergence results of §3.4 nontrivial.
--
--   **Formalization Note** A skeleton is an inductive tree (`Tree n`) whose split nodes carry `i : Fin n` and whose leaves carry an action. Split points are a function `θ : List Bool → ℝ` keyed by the **address** of a split node (the path of turns from the root, `true` = left). Values at addresses that are not split nodes are never read, so `θ` carries exactly the information of $\boldsymbol\theta\in\mathbb R^{\mathbf{splits}}$. The query is $x_i\le\theta$, with ties going left as on the page. `S.splits` is the finite set of pairs (address, split variable) of the split nodes. A leaf has depth $0$ and a split node has depth one more than its deeper child. $\Pi_{\mathrm{tree}}(d)$ is the type `TreePol n d` of pairs (skeleton of depth $\le d$, split points), which is nonempty (it contains the leaf $\mathbf{go}$).
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, §3.3, pp. 6–8 (tree policies); §3.4, p. 9 (Πtree(d)); eq. (10), p. 12 (θ ∈ ℝ^splits)

import Mathlib
import Definitions.Def_InterpOptStop_SAA_StoppingModel

namespace InterpOptStop.SAA

/-- The skeleton `(𝒯, v, a)` of a tree policy (§3.3, pp. 6–7): a binary tree whose split
nodes carry a split variable index `i : Fin n` and whose leaves carry an action. -/
inductive Tree (n : ℕ)
  | leaf (a : Act)
  | split (i : Fin n) (l r : Tree n)
  deriving DecidableEq

/-- Split points `θ`, keyed by the address of a split node: the list of turns from the root,
`true` = left child. Values at addresses that are not split nodes are never read. -/
abbrev Thresholds := List Bool → ℝ

namespace Tree

variable {n : ℕ}

/-- Depth of a tree: a leaf has depth `0`, a split node one more than its deeper child. -/
def depth : Tree n → ℕ
  | leaf _ => 0
  | split _ l r => max l.depth r.depth + 1

/-- The action of the subtree located at address `p`, for state `x`: at a split node with
split variable `i` and split point `θ p`, go left if `x i ≤ θ p` and right otherwise; at a
leaf, return its action. -/
noncomputable def act : Tree n → Thresholds → List Bool → (Fin n → ℝ) → Act
  | leaf a, _, _, _ => a
  | split i l r, θ, p, x =>
      if x i ≤ θ p then l.act θ (p ++ [true]) x else r.act θ (p ++ [false]) x

/-- The split nodes of the subtree located at address `p`, each as (address, split variable). -/
def splitsAt : Tree n → List Bool → Finset (List Bool × Fin n)
  | leaf _, _ => ∅
  | split i l r, p => insert (p, i) (l.splitsAt (p ++ [true]) ∪ r.splitsAt (p ++ [false]))

/-- The set `splits` of the tree: each split node `s` as (its address, its split variable `v(s)`). -/
def splits (S : Tree n) : Finset (List Bool × Fin n) := S.splitsAt []

end Tree

/-- The tree policy `π(x; 𝒯, v, θ, a)` (§3.3, p. 7): the action of the leaf to which the
state `x` is mapped. It is stationary (p. 8): it does not depend on the period. -/
noncomputable def policy {n : ℕ} (S : Tree n) (θ : Thresholds) : (Fin n → ℝ) → Act := S.act θ []

/-- `Πtree(d)` (§3.4, p. 9), as parameters: a skeleton of depth at most `d` together with
arbitrary real split points. -/
def TreePol (n d : ℕ) := {q : Tree n × Thresholds // q.1.depth ≤ d}

instance {n d : ℕ} : Nonempty (TreePol n d) :=
  ⟨⟨(Tree.leaf Act.go, fun _ => 0), Nat.zero_le d⟩⟩

end InterpOptStop.SAA


