-- Prove2me | Definitions.Def_DecisionForest_Universal_Setting
-- name    : DecisionForest_Universal_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:49.5103+00:00
-- url     : https://prove2.me/theorems/7cc471ed-3df2-4f84-9bc5-4a688764b451
-- title:
--   §3.1–§3.3, pp. 6–9; EC.1.2, pp. ec1–ec2 — choice models, purchase decision trees, Requirements 1–3, depth, F_d, the forest model (3) and the trees and weights (EC.1)–(EC.5)
-- statement:
--   This file fixes the objects of the decision forest model of Chen and Mišić.
--
--   1. **Products, options, assortments.** There are $N$ products $\mathcal N=\{1,\dots,N\}$ and the purchase options $\mathcal N^+=\{0,1,\dots,N\}$, where $0$ is the no-purchase option. An **assortment** is any subset $S\subseteq\mathcal N$, the empty assortment included.
--   2. **Choice model** (§3.1). A function $\mathbf P(o\mid S)$ of an option $o\in\mathcal N^+$ and an assortment $S$ is a **discrete choice model** when, for every assortment $S$, $\mathbf P(\cdot\mid S)$ is a probability distribution on $\mathcal N^+$ and
--   $$\mathbf P(p\mid S)=0\qquad\text{for every product } p\notin S .$$
--   3. **Purchase decision trees** (§3.2). A tree $t$ is a binary tree whose split nodes carry products and whose leaves carry purchase options. A customer following $t$ and offered $S$ starts at the root; at a split carrying product $p$ the customer moves to the left child if $p\in S$ and to the right child otherwise; the option at the leaf reached is the purchase $\hat A(S,t)\in\mathcal N^+$.
--   4. **Requirements** (p. 7). Requirement 1 (each split carries a product) holds by construction. Requirement 2: the option at each leaf $\ell$ is $0$ or the product of a split $s\in\mathbf{LS}(\ell)$, i.e. a split for which $\ell$ lies in the left subtree (a product found present on the way down). Requirement 3: along every root-to-leaf path the splits carry pairwise distinct products.
--   5. **Depth** (p. 8). $\mathrm{Depth}(t)$ is the largest number of edges on a root-to-leaf path plus one, so a single leaf has depth $1$. The number of leaves of $t$ is $|\mathbf{leaves}(t)|$.
--   6. **The classes $F_d$** (Theorem 1). $F_d$ is the set of trees satisfying Requirements 1–3 with depth at most $d$.
--   7. **Decision forest model** (3). For a finite collection $F$ of trees and weights $\lambda$,
--   $$\mathbf P^{(F,\lambda)}(o\mid S)=\sum_{t\in F}\lambda_t\cdot\mathbb I\{o=\hat A(S,t)\}.$$
--   8. **The forest of the proof of Theorem 1** (EC.1)–(EC.5). For a tuple $\mathbf o=(o_S)_{S\subseteq\mathcal N}$ of options, one per assortment, the balanced tree $t_{\mathbf o}$ splits on product $1$ at the root, on product $2$ at the second level, …, on product $N$ at level $N$, and the leaf reached by assortment $S$ buys $o_S$. Its weight is
--   $$\lambda_{\mathbf o}=\prod_{S\subseteq\mathcal N}\mathbf P(o_S\mid S).$$
--
--   These objects are shared by every statement of the mission: Theorem 1 and the steps of its proof.
--
--   **Formalization Note** Products are `Fin N`, so the paper's product $k$ is `k - 1`; options are `Option (Fin N)` with `none` the no-purchase option $0$; assortments are `Finset (Fin N)`; probabilities are real numbers. A choice model is a function `P : Option (Fin N) → Finset (Fin N) → ℝ` with `IsChoiceModel P`. Trees are the inductive type `PTree N` (`leaf o`, `split p l r`), so Requirement 1 holds by typing; Requirements 2 and 3 are computed along paths by `req2Aux` (the products of left-going splits) and `req3Aux` (the products of all splits above). The paper's left-to-right enumeration of leaves and of tuples $\mathbf o^t$ is replaced by indexing leaves by assortments: a tuple is a function `o : Finset (Fin N) → Option (Fin N)`, and its tree is `fullTree o`.
-- source:
--   Chen and Mišić, Decision Forest: A Nonparametric Approach to Modeling Irrational Choice, arXiv:1904.11532v3, pp. 6–9, §3.1–§3.3, Requirements 1–3, (3); p. 11, Theorem 1 (F_d); pp. ec1–ec2, (EC.1)–(EC.5)

import Mathlib

namespace DecisionForest.Universal

/-- §3.2, p. 7: a binary purchase decision tree over the products `Fin N`. A split node carries
a product (Requirement 1 holds by typing) and has a left and a right subtree; a leaf carries a
purchase option, where `none` is the no-purchase option 0 and `some p` is product `p`. -/
inductive PTree (N : ℕ) where
  | leaf (o : Option (Fin N))
  | split (p : Fin N) (l r : PTree N)

variable {N : ℕ}

/-- `Â(S, t)`, §3.2–§3.3, pp. 7–8: the purchase option chosen by a customer following tree `t`
when offered assortment `S`. At a split on product `p`, the customer goes to the left child if
`p ∈ S` and to the right child otherwise; the option at the leaf reached is the purchase. -/
def choose : PTree N → Finset (Fin N) → Option (Fin N)
  | .leaf o, _ => o
  | .split p l r, S => if p ∈ S then choose l S else choose r S

/-- `Depth(t)`, p. 8: the number of edges on a longest root-to-leaf path plus one, so a single
leaf has depth 1. -/
def depth : PTree N → ℕ
  | .leaf _ => 1
  | .split _ l r => max (depth l) (depth r) + 1

/-- `|leaves(t)|`: the number of leaf nodes of `t`. -/
def numLeaves : PTree N → ℕ
  | .leaf _ => 1
  | .split _ l r => numLeaves l + numLeaves r

/-- Requirement 2 along paths: `L` is the set of products `x_s` of the splits `s` passed so far
for which the path went left (the set `LS(ℓ)` once a leaf `ℓ` is reached). A leaf satisfies it
when its option is `0` or a product in `L`. -/
def req2Aux : PTree N → Finset (Fin N) → Prop
  | .leaf o, L => ∀ p, o = some p → p ∈ L
  | .split p l r, L => req2Aux l (insert p L) ∧ req2Aux r L

/-- Requirement 3 along paths: `A` is the set of products of all splits passed so far (left or
right, the set `LS(ℓ) ∪ RS(ℓ)` once a leaf is reached). Every split's product must be new. -/
def req3Aux : PTree N → Finset (Fin N) → Prop
  | .leaf _, _ => True
  | .split p l r, A => p ∉ A ∧ req3Aux l (insert p A) ∧ req3Aux r (insert p A)

/-- Requirement 2, p. 7: for each leaf `ℓ`, `x_ℓ ∈ {0} ∪ ⋃_{s ∈ LS(ℓ)} {x_s}`. -/
def Req2 (t : PTree N) : Prop := req2Aux t ∅

/-- Requirement 3, p. 7: for each leaf `ℓ`, the splits in `LS(ℓ) ∪ RS(ℓ)` carry pairwise
distinct products. -/
def Req3 (t : PTree N) : Prop := req3Aux t ∅

/-- A purchase decision tree satisfying Requirements 1–3 (Requirement 1 holds by typing). -/
def IsPurchaseTree (t : PTree N) : Prop := Req2 t ∧ Req3 t

/-- `F_d`, Theorem 1, p. 11: the purchase decision trees satisfying Requirements 1–3 of depth
at most `d`. -/
def FSet (N d : ℕ) : Set (PTree N) := {t | IsPurchaseTree t ∧ depth t ≤ d}

/-- §3.1, p. 6: a discrete choice model `P(o | S)`: for every assortment `S ⊆ 𝒩` (including
`∅`) a probability distribution on the options `𝒩⁺`, giving probability zero to every product
outside `S`. -/
def IsChoiceModel (P : Option (Fin N) → Finset (Fin N) → ℝ) : Prop :=
  (∀ o S, 0 ≤ P o S) ∧ (∀ S, ∑ o, P o S = 1) ∧ (∀ S p, p ∉ S → P (some p) S = 0)

/-- (3), p. 8: the decision forest model `P^(F,λ)(o | S) = ∑_{t ∈ F} λ_t · 𝕀{o = Â(S, t)}`. -/
noncomputable def forestProb (F : Finset (PTree N)) (lam : PTree N → ℝ)
    (o : Option (Fin N)) (S : Finset (Fin N)) : ℝ :=
  ∑ t ∈ F, lam t * if choose t S = o then 1 else 0

/-- (EC.1)–(EC.4), pp. ec1–ec2: split on the products of `ps` level by level; `S` records the
products found present on the way down (left = present). The leaf reached by the assortment
`T` buys `o T`. -/
def fullTreeAux (o : Finset (Fin N) → Option (Fin N)) : List (Fin N) → Finset (Fin N) → PTree N
  | [], S => .leaf (o S)
  | p :: ps, S => .split p (fullTreeAux o ps (insert p S)) (fullTreeAux o ps S)

/-- The balanced tree of the proof of Theorem 1 (pp. ec1–ec2) with leaf decisions given by the
tuple `o`: level `k` splits on product `k` (0-based), and the leaf of assortment `S` buys
`o S`. -/
def fullTree (o : Finset (Fin N) → Option (Fin N)) : PTree N :=
  fullTreeAux o (List.finRange N) ∅

/-- (EC.5), p. ec2: the weight `λ_o = ∏_S P(o_S | S)` of the tree with leaf-decision tuple `o`. -/
noncomputable def prodWeight (P : Option (Fin N) → Finset (Fin N) → ℝ)
    (o : Finset (Fin N) → Option (Fin N)) : ℝ :=
  ∏ S, P (o S) S

end DecisionForest.Universal


