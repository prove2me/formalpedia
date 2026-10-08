-- Prove2me | Definitions.Def_RevenueOrdered_Stackelberg_Instance
-- name    : RevenueOrdered_Stackelberg_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:05:51.475001+00:00
-- url     : https://prove2.me/theorems/5eb7b32a-738e-4ded-8f09-842cd4b977b7
-- title:
--   §4.6, p. 23 — Stackelberg Matroid instance, customer orderings (15a)–(15b) and the leader's revenue
-- statement:
--   This module defines the Stackelberg Matroid problem of §4.6 of Berbeglia and Joret.
--
--   An **instance** consists of a matroid $M=(E,\mathcal X)$ with finite ground set, a bipartition $E=R\sqcup B$ into red and blue elements, and a cost function $c:R\to\mathbb R_{>0}$. As in the paper, every instance is assumed to have a base of $M$ consisting only of red elements; otherwise the optimum revenue is unbounded.
--
--   The leader chooses prices $p:B\to\mathbb R_{>0}$. The customer sees the weights $c'(e)=c(e)$ for $e\in R$ and $c'(e)=p(e)$ for $e\in B$, and runs the greedy algorithm on $R\cup B$ with a linear ordering $L^*$ that is **compatible** with these weights:
--
--   1. (15a) if $c'(e)<c'(f)$ then $e<_{L^*}f$, for all $e,f\in R\cup B$;
--   2. (15b) if $c'(e)=c'(f)$ with $e\in B$ and $f\in R$, then $e<_{L^*}f$ (blue elements have priority on ties).
--
--   The leader's **revenue** under $p$ and $L^*$ is
--   $$
--   \mathrm{rev}_{\mathrm{Stack}}(p,L^*)=\sum_{e\in B\cap\,\mathrm{greedy}_M(R\cup B,\,L^*)} p(e).
--   $$
--   Lemma 4.15 shows that this does not depend on which compatible $L^*$ the customer uses.
--
--   **Formalization Note** $R$ and $B$ are `Finset`s whose union is the matroid's ground set; values of $c$ outside $R$ and of $p$ outside $B$ are never used. Compatibility is written as a pairwise condition on the list: whenever $e$ precedes $f$, $c'(e)\le c'(f)$, and if the weights are equal and $e$ is red then $f$ is red. For a linear ordering of $R\cup B$ this is equivalent to (15a)–(15b). The paper's display (15a)–(15b) writes $c_S(f)$ on the right-hand side, a typo for $c'(f)$.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, pp. 23 and 33, §4.6 (Stackelberg Matroid problem), (15a), (15b)

import Mathlib
import Definitions.Def_RevenueOrdered_Stackelberg_Greedy

namespace RevenueOrdered.Stackelberg

open Classical in
/-- An instance of the Stackelberg Matroid problem (Berbeglia–Joret, arXiv:1606.01371v3, §4.6,
p. 23): a matroid `M = (E, 𝒳)`, a bipartition `E = R ⊔ B` into red and blue elements, and a cost
function `c : R → ℝ_{>0}`. The paper always assumes (p. 23) that `M` has a base consisting only of
red elements (`exists_red_base`); otherwise the optimum RevenueOrdered.Ratio.revenue is unbounded. The ground set is
finite because it equals `R ∪ B`. Values of `c` outside `R` are irrelevant. -/
structure Instance (α : Type*) where
  M : Matroid α
  R : Finset α
  B : Finset α
  c : α → ℝ
  disjoint : Disjoint R B
  ground_eq : ((R ∪ B : Finset α) : Set α) = M.E
  cost_pos : ∀ e ∈ R, 0 < c e
  exists_red_base : ∃ X : Set α, X ⊆ (R : Set α) ∧ M.IsBase X

variable {α : Type*}

open Classical in
/-- The weight `c′` the customer sees once prices `p` are set on the blue elements (p. 33):
`c′(e) = p(e)` for `e ∈ B` and `c′(e) = c(e)` otherwise. -/
noncomputable def Instance.weight (I : Instance α) (p : α → ℝ) (e : α) : ℝ :=
  if e ∈ I.B then p e else I.c e

open Classical in
/-- `L` is an ordering a customer facing prices `p` may use (p. 23 and (15a), (15b), p. 33):
a linear ordering of `R ∪ B` that is non-decreasing in the weight `c′`, and in which, on ties,
blue elements come before red ones. Writing it with `List.Pairwise`: whenever `e` precedes `f`,
`c′(e) ≤ c′(f)`, and if moreover `c′(e) = c′(f)` and `e` is red then `f` is red. -/
def Instance.IsCustomerOrder (I : Instance α) (p : α → ℝ) (L : List α) : Prop :=
  IsLinearOrderOf L (I.R ∪ I.B) ∧
    L.Pairwise (fun e f => I.weight p e ≤ I.weight p f ∧
      (I.weight p e = I.weight p f → e ∈ I.R → f ∈ I.R))

open Classical in
/-- The RevenueOrdered.Ratio.revenue of the leader when the blue elements are priced by `p` and the customer buys
the minimum-weight base `greedy_M(R ∪ B, L)`: the sum of `p(e)` over the blue elements `e` of
that base (p. 23). -/
noncomputable def Instance.stackRevenue (I : Instance α) (p : α → ℝ) (L : List α) : ℝ :=
  ∑ e ∈ I.B ∩ greedyM I.M L (I.R ∪ I.B), p e

end RevenueOrdered.Stackelberg


