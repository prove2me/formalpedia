-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_Minimax_Bias
-- name    : RobertsonSeymour1991_GM10_Minimax_Bias
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:04:16.088081+00:00
-- url     : https://prove2.me/theorems/b31aa5d7-5d93-49d3-92d8-722993801bdf
-- title:
--   §3, pp. 159–160 — connectivity function, bias, tree-labelling, exact tree-labelling
-- statement:
--   Let $E$ be a finite set. A **connectivity function** on $E$ is a map $\kappa$ from the subsets of $E$ to the integers with
--
--   $$\kappa(X)=\kappa(E-X),\qquad \kappa(X\cup Y)+\kappa(X\cap Y)\le\kappa(X)+\kappa(Y)\qquad(X,Y\subseteq E).$$
--
--   A set $X\subseteq E$ is **efficient** if $\kappa(X)\le0$. A **bias** is a set $\mathcal B$ of efficient sets such that (i) for every efficient $X$, $\mathcal B$ contains $X$ or $E-X$, and (ii) $X\cup Y\cup Z\ne E$ for all $X,Y,Z\in\mathcal B$. A bias **extends** a set $\mathcal A$ of efficient sets if $\mathcal A\subseteq\mathcal B$.
--
--   A **tree-labelling over $\mathcal A$** is a pair $(T,\alpha)$ where $T$ is a ternary tree and $\alpha$ assigns to each incidence $(v,e)$ of $T$ ($v$ an end of the tree edge $e$) an efficient subset of $E$, such that
--
--   1. $\alpha(u,e)=E-\alpha(v,e)$ for each edge $e$ of $T$ with ends $u,v$;
--   2. for each incidence $(v,e)$ with $v$ a leaf, $\alpha(v,e)=E$ or $\alpha(v,e)\cup X=E$ for some $X\in\mathcal A$;
--   3. if $v$ has valency $3$, with edges $e_1,e_2,e_3$, then $\alpha(v,e_1)\cup\alpha(v,e_2)\cup\alpha(v,e_3)=E$.
--
--   A **fork** is a pair of distinct edges $e_1,e_2$ of $T$ with a common end $t$ (its nub); it is **exact** if $\alpha(t,e_1)\cap\alpha(t,e_2)=\emptyset$, and $(T,\alpha)$ is **exact** if every fork is exact.
--
--   Biases and tree-labellings are the two sides of the abstract minimax lemma (3.5), from which the tangle/branch-width duality is deduced.
--
--   **Formalization Note** Subsets of $E$ are `Set E`, and $E-X$ is the complement. The tree has vertex set `Fin n`; the incidence $(u,e)$ with $e=uw$ is the ordered adjacent pair $(u,w)$, and its label is `α u w`. Every condition on $\alpha$ is required only for adjacent pairs, so the values of `α` on non-adjacent pairs are irrelevant. A vertex of a ternary tree with three distinct neighbours has valency $3$, which is how condition 3 is written. "There is a tree-labelling over $\mathcal A$" quantifies over the number $n$ of tree vertices.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), pp. 159–160 (§3: connectivity function, efficient, bias, tree-labelling, fork, exact)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Minimax_BranchDecomposition

namespace RobertsonSeymour1991.GM10.Minimax

/-- p. 159: `κ` is a connectivity function on `E`: `κ(X) = κ(E − X)` and
`κ(X ∪ Y) + κ(X ∩ Y) ≤ κ(X) + κ(Y)` for all `X, Y ⊆ E`. Here `E − X` is `Xᶜ`. -/
def IsConnectivityFunction {E : Type} (κ : Set E → ℤ) : Prop :=
  (∀ X : Set E, κ X = κ Xᶜ) ∧ ∀ X Y : Set E, κ (X ∪ Y) + κ (X ∩ Y) ≤ κ X + κ Y

/-- p. 159: `ℬ` is a bias (for `κ`): a set of efficient sets (`κ(X) ≤ 0`) such that (i) every efficient
`X ⊆ E` has `X ∈ ℬ` or `E − X ∈ ℬ`, and (ii) `X ∪ Y ∪ Z ≠ E` for all `X, Y, Z ∈ ℬ`. -/
def IsBias {E : Type} (κ : Set E → ℤ) (ℬ : Set (Set E)) : Prop :=
  (∀ X ∈ ℬ, κ X ≤ 0) ∧
  (∀ X : Set E, κ X ≤ 0 → X ∈ ℬ ∨ Xᶜ ∈ ℬ) ∧
  (∀ X ∈ ℬ, ∀ Y ∈ ℬ, ∀ Z ∈ ℬ, X ∪ Y ∪ Z ≠ Set.univ)

/-- pp. 159–160: a tree-labelling `(T, α)` over `𝒜`. The ternary tree `T` is on `Fin n`; the incidence
`(u, e)` with `e = uw` is the ordered adjacent pair `(u, w)`, and `α u w` is `α(u, e)`. The values of `α`
on non-adjacent pairs are not used. -/
structure TreeLabelling {E : Type} (κ : Set E → ℤ) (𝒜 : Set (Set E)) (n : ℕ) where
  T : SimpleGraph (Fin n)
  ternary : IsTernaryTree T
  α : Fin n → Fin n → Set E
  /-- every label is efficient -/
  efficient : ∀ u w, T.Adj u w → κ (α u w) ≤ 0
  /-- (i): `α(u, e) = E − α(v, e)` for each edge `e` with ends `u, v` -/
  compl : ∀ u w, T.Adj u w → α u w = (α w u)ᶜ
  /-- (ii): at a leaf `v`, `α(v, e) = E` or `α(v, e) ∪ X = E` for some `X ∈ 𝒜` -/
  leaf : ∀ u w, T.Adj u w → (T.neighborSet u).ncard = 1 →
    α u w = Set.univ ∨ ∃ X ∈ 𝒜, α u w ∪ X = Set.univ
  /-- (iii): at a vertex of valency 3 with edges `e₁, e₂, e₃`, `α(v, e₁) ∪ α(v, e₂) ∪ α(v, e₃) = E` -/
  node : ∀ u w₁ w₂ w₃, T.Adj u w₁ → T.Adj u w₂ → T.Adj u w₃ → w₁ ≠ w₂ → w₁ ≠ w₃ → w₂ ≠ w₃ →
    α u w₁ ∪ α u w₂ ∪ α u w₃ = Set.univ

/-- p. 160: `(T, α)` is exact: every fork `{e₁, e₂}` (distinct edges with a common end `t`, the nub)
has `α(t, e₁) ∩ α(t, e₂) = ∅`. -/
def TreeLabelling.IsExact {E : Type} {κ : Set E → ℤ} {𝒜 : Set (Set E)} {n : ℕ}
    (L : TreeLabelling κ 𝒜 n) : Prop :=
  ∀ t w₁ w₂, L.T.Adj t w₁ → L.T.Adj t w₂ → w₁ ≠ w₂ → L.α t w₁ ∩ L.α t w₂ = ∅

end RobertsonSeymour1991.GM10.Minimax


