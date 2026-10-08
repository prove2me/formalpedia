-- Prove2me | Definitions.Def_RevenueOrdered_Stackelberg_Assortment
-- name    : RevenueOrdered_Stackelberg_Assortment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:17:27.464642+00:00
-- url     : https://prove2.me/theorems/8fbed34d-f759-4d44-88d5-a69dfd92b01a
-- title:
--   Proof of Theorem 4.16, pp. 32–34 — the assortment instance: $\mathcal C = B\times\{c_1,\dots,c_k\}$, $r = |B|q$, auxiliary matroid $M'$, choice probabilities, $p_S$, $S_p$
-- statement:
--   This module defines the explicit assortment instance built from a Stackelberg Matroid instance $(M,R,B,c)$ in the proof of Theorem 4.16 of Berbeglia and Joret.
--
--   Let $c_1<\dots<c_k$ be the distinct red costs.
--
--   1. **Products** $\mathcal C=B\times\{c_1,\dots,c_k\}$, with revenues $r((e,q))=|B|\cdot q$.
--   2. **Auxiliary matroid $M'$** on the ground set $R\cup\mathcal C$: a set $X\subseteq R\cup\mathcal C$ is independent iff (1) for each $e\in B$, $X$ contains at most one pair $(e,q)$, and (2) $(R\cap X)\cup\{e\in B:(e,q)\in X\text{ for some }q\}$ is independent in $M$.
--   3. **Cost** of $x\in R\cup\mathcal C$: $c(x)$ if $x\in R$, and $q$ if $x=(e,q)$. An ordering $L$ of $R\cup\mathcal C$ is admissible if it is non-decreasing in cost and puts elements of $\mathcal C$ before red elements of the same cost.
--   4. **Choice probabilities**, for such an $L$:
--   $$
--   \mathcal P((e,q),S)=\begin{cases}1/|B| & \text{if } (e,q)\in\mathrm{greedy}_{M'}(R\cup S,L),\\ 0&\text{otherwise.}\end{cases}
--   $$
--   5. **Price of an assortment** $S\subseteq\mathcal C$: $p_S(e)=\min\{q:(e,q)\in S\}$ if such a pair exists, and $+\infty$ otherwise.
--   6. **Assortment of a price assignment** $p$ and customer ordering $L^*$: $S_p=\{(e,p(e)): e\in\mathrm{greedy}_M(R\cup B,L^*)\}$.
--   7. **Rounding up**: $p(e)$ is replaced by the least red cost $c_i\ge p(e)$, or by $+\infty$ if $p(e)>c_k$.
--
--   These are the objects of the proof's three steps: regularity of $\mathcal P$, $\mathrm{rev}(S)$ equals the revenue of $p_S$, and the revenue of $p$ equals $\mathrm{rev}(S_p)$.
--
--   **Formalization Note** Elements of $R\cup\mathcal C$ live in the sum type `α ⊕ (α × ℝ)`: red elements are `Sum.inl`, products are `Sum.inr`. The paper's condition (1) reads $|\{(e,q):q\in\{c_1,\dots,c_k\}\}|\le 1$, omitting "$\in X$", and its condition (2) writes $\mathcal X$ for $X$; the intended conditions are formalized. The price $+\infty$ is represented by `abovePrice` $=1+\sum_{f\in R}c(f)$, a real number strictly above every red cost; a blue element priced above every red cost is never bought, because $R$ contains a base. $S_p$ is the set of products $(e,q)$ with $e$ bought and $q=p(e)$; it is the paper's $S_p$ whenever the bought elements have prices in $\{c_1,\dots,c_k\}$.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, pp. 32–34, proof of Theorem 4.16

import Mathlib
import Definitions.Def_RevenueOrdered_Stackelberg_Model
import Definitions.Def_RevenueOrdered_Stackelberg_Greedy
import Definitions.Def_RevenueOrdered_Stackelberg_Instance

namespace RevenueOrdered.Stackelberg

variable {α : Type*}

open Classical

/-- The set `{c₁, …, c_k}` of distinct red costs (p. 24, Theorem 4.16). -/
noncomputable def costs (I : Instance α) : Finset ℝ := I.R.image I.c

/-- The products of the assortment instance, `𝒞 := B × {c₁, …, c_k}` (proof of Theorem 4.16,
p. 32), as a finite set of pairs. -/
noncomputable def products (I : Instance α) : Finset (α × ℝ) := I.B ×ˢ costs I

/-- The type of products `𝒞`. -/
abbrev Product (I : Instance α) : Type _ := {y : α × ℝ // y ∈ products I}

/-- The RevenueOrdered.Ratio.revenue function `r((e, q)) := |B| · q` (p. 32). -/
noncomputable def prodRevenue (I : Instance α) (y : Product I) : ℝ :=
  (I.B.card : ℝ) * y.1.2

/-- The ground set `R ∪ 𝒞` of the auxiliary matroid `M′` (p. 32); red elements are `Sum.inl`,
products are `Sum.inr`. -/
noncomputable def auxGround (I : Instance α) : Finset (α ⊕ (α × ℝ)) :=
  I.R.map Function.Embedding.inl ∪ (products I).map Function.Embedding.inr

/-- Independence in the auxiliary matroid `M′` (p. 32): `X ⊆ R ∪ 𝒞` is independent iff
(1) for each `e ∈ B`, `X` contains at most one pair `(e, q)` with `q ∈ {c₁, …, c_k}`, and
(2) `(R ∩ X) ∪ {e ∈ B : (e, q) ∈ X for some q ∈ {c₁, …, c_k}}` is independent in `M`.
The paper's (1) reads `|{(e, q) : q ∈ {c₁, …, c_k}}| ⩽ 1`, omitting `∈ X`, and its (2) writes
`(e, q) ∈ 𝒳` for `(e, q) ∈ X`; this is the intended reading of both. -/
def auxIndep (I : Instance α) (X : Finset (α ⊕ (α × ℝ))) : Prop :=
  X ⊆ auxGround I ∧
    (∀ e ∈ I.B, (X.filter (fun y => ∃ q ∈ costs I, y = Sum.inr (e, q))).card ≤ 1) ∧
    I.M.Indep (((I.R.filter (fun a => Sum.inl a ∈ X)) ∪
      (I.B.filter (fun e => ∃ q ∈ costs I, Sum.inr (e, q) ∈ X)) : Finset α) : Set α)

/-- The cost of an element of `R ∪ 𝒞` (p. 32): `c(x)` for `x ∈ R`, and `q` for `x = (e, q)`. -/
def auxCost (I : Instance α) : α ⊕ (α × ℝ) → ℝ := Sum.elim I.c Prod.snd

/-- `L` is an ordering of `R ∪ 𝒞` as in the proof of Theorem 4.16 (p. 32): a linear ordering
that is non-decreasing in cost and gives elements of `𝒞` priority over red elements on ties
(if `(e, q) ∈ 𝒞`, `f ∈ R` and `c(f) = q` then `(e, q) <_L f`). With `List.Pairwise`: whenever
`x` precedes `y`, `cost(x) ≤ cost(y)`, and if the costs are equal and `x` is red then `y` is red. -/
def IsAuxOrder (I : Instance α) (L : List (α ⊕ (α × ℝ))) : Prop :=
  IsLinearOrderOf L (auxGround I) ∧
    L.Pairwise (fun x y => auxCost I x ≤ auxCost I y ∧
      (auxCost I x = auxCost I y → x.isLeft = true → y.isLeft = true))

/-- The embedding of products into `R ∪ 𝒞`. -/
def productEmb (I : Instance α) : Product I ↪ α ⊕ (α × ℝ) :=
  (Function.Embedding.subtype _).trans Function.Embedding.inr

/-- The choice probabilities of the proof of Theorem 4.16 (p. 32), for the ordering `L`:
`𝒫((e, q), S) = 1/|B|` if `(e, q) ∈ greedy_{M′}(R ∪ S, L)`, and `0` otherwise. -/
noncomputable def choiceProb (I : Instance α) (L : List (α ⊕ (α × ℝ))) (y : Product I)
    (S : Finset (Product I)) : ℝ :=
  if Sum.inr y.1 ∈ greedy (auxIndep I) L (I.R.map Function.Embedding.inl ∪ S.map (productEmb I))
  then 1 / (I.B.card : ℝ) else 0

/-- A price strictly above every red cost, `1 + ∑_{f ∈ R} c(f)`; it plays the role of the
paper's price `+∞` (p. 33): a blue element priced above every red cost is never bought, because
`R` contains a base. -/
noncomputable def abovePrice (I : Instance α) : ℝ := 1 + ∑ f ∈ I.R, I.c f

/-- The price assignment `p_S` of an assortment `S ⊆ 𝒞` (p. 33):
`p_S(e) = min{q : (e, q) ∈ S}` if some `(e, q) ∈ S`, and `+∞` (here `abovePrice`) otherwise. -/
noncomputable def priceOfAssortment (I : Instance α) (S : Finset (Product I)) (e : α) : ℝ :=
  let Q := (S.filter (fun y => y.1.1 = e)).image (fun y => y.1.2)
  if h : Q.Nonempty then Q.min' h else abovePrice I

/-- The assortment `S_p := {(e, p(e)) : e ∈ greedy_M(R ∪ B, L*)}` of a price assignment `p`
with values in `{c₁, …, c_k} ∪ {+∞}` (p. 34), as a set of products: the pairs `(e, q) ∈ 𝒞`
with `e` bought under the ordering `L*` and `q = p(e)`. -/
noncomputable def assortmentOfPrices (I : Instance α) (p : α → ℝ) (L : List α) :
    Finset (Product I) :=
  Finset.univ.filter (fun y => y.1.1 ∈ greedyM I.M L (I.R ∪ I.B) ∧ y.1.2 = p y.1.1)

/-- Rounding a price up to the cost levels (p. 34): `p(e)` is replaced by the least red cost
`c_i ≥ p(e)`, or by `+∞` (here `abovePrice`) if `p(e) > c_k`. -/
noncomputable def roundUp (I : Instance α) (p : α → ℝ) (e : α) : ℝ :=
  if h : ((costs I).filter (fun q => p e ≤ q)).Nonempty
  then ((costs I).filter (fun q => p e ≤ q)).min' h else abovePrice I

end RevenueOrdered.Stackelberg


