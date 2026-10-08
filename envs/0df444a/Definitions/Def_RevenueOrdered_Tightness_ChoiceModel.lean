-- Prove2me | Definitions.Def_RevenueOrdered_Tightness_ChoiceModel
-- name    : RevenueOrdered_Tightness_ChoiceModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:50:49.148306+00:00
-- url     : https://prove2.me/theorems/5eeeac36-f58b-446a-963b-0bf00b002967
-- title:
--   Regular discrete choice model, revenue $\mathrm{rev}(S)$ and $\mathrm{OPT}$
-- statement:
--   Let $\mathcal C$ be a finite set of products and let $x=0$ denote the no-purchase option. A **system of choice probabilities** assigns to every choice set $S\subseteq\mathcal C$ and every product $x\in\mathcal C$ a number $\mathcal P(x,S)$, the probability that a consumer offered $S$ buys $x$. The no-purchase probability is
--   $$
--   \mathcal P(0,S)=1-\sum_{x\in S}\mathcal P(x,S).
--   $$
--   The system is a **regular discrete choice model** if it satisfies the four axioms
--   1. (i) $\mathcal P(x,S)\ge 0$ for every $x\in\mathcal C\cup\{0\}$ and $S\subseteq\mathcal C$;
--   2. (ii) $\mathcal P(x,S)=0$ for every $x\in\mathcal C$ and $S\subseteq\mathcal C\setminus\{x\}$;
--   3. (iii) $\sum_{x\in S}\mathcal P(x,S)\le 1$ for every $S\subseteq\mathcal C$;
--   4. (iv) (regularity) $\mathcal P(x,S)\ge\mathcal P(x,S')$ for every $S\subseteq S'\subseteq\mathcal C$ and $x\in S\cup\{0\}$.
--
--   Given a revenue function $r:\mathcal C\to\mathbb R$, the seller's revenue when offering $S$ is
--   $$
--   \mathrm{rev}(S)=\sum_{x\in S}\mathcal P(x,S)\,r(x),
--   $$
--   and $\mathrm{OPT}=\max_{S\subseteq\mathcal C}\mathrm{rev}(S)$ is the optimum of the assortment problem (the empty set, with revenue $0$, is allowed).
--
--   These are the objects every result of the paper is about.
--
--   **Formalization Note** Products form a finite type `C`; the no-purchase option is not a product, and $\mathcal P(0,S)$ is the derived quantity `RevenueOrdered.Ratio.noPurchase P S`, imported from the definition module `RevenueOrdered.Ratio.Model`. Axioms (i) and (iv) are each split into their product case and their no-purchase case; the no-purchase case of (i) follows from (iii) and is kept explicitly. `P x S` is defined for all $x$, and axiom (ii) forces it to vanish off $S$. This module defines the structure `IsRegular` and the revenue `rev`; $\mathrm{OPT}$ is not redefined here, and the theorems that use these objects take it from `RevenueOrdered.Ratio.opt` (the maximum of the same revenue sum over all subsets).
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, pp. 5–6, §2, axioms (i)–(iv) and Definition 1

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model

namespace RevenueOrdered.Tightness

/-! Regular discrete choice models and the assortment problem
(Berbeglia & Joret, arXiv:1606.01371v3, §2, pp. 5–6, axioms (i)–(iv) and Definition 1).

The set of products `𝒞 = {1, …, N}` is a finite type `C`. The no-purchase option `x = 0` is not a
product: `P x S` is `𝒫(x, S)` for a product `x : C`, and `𝒫(0, S)` is the derived quantity
`noPurchase P S = 1 - ∑_{x ∈ S} 𝒫(x, S)` (p. 5). Choice sets are `Finset C`. -/

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- A regular discrete choice model (p. 6): the four axioms (i)–(iv), with axiom (i) and the
regularity axiom (iv) each split into its product case (`x ∈ 𝒞`) and its no-purchase case
(`x = 0`). The no-purchase case of (i) is implied by (iii) and is kept explicitly. -/
structure IsRegular (P : C → Finset C → ℝ) : Prop where
  /-- (i), `x ∈ 𝒞`: `𝒫(x, S) ⩾ 0`. -/
  nonneg : ∀ (x : C) (S : Finset C), 0 ≤ P x S
  /-- (i), `x = 0`: `𝒫(0, S) ⩾ 0`. -/
  noPurchase_nonneg : ∀ S : Finset C, 0 ≤ RevenueOrdered.Ratio.noPurchase P S
  /-- (ii): `𝒫(x, S) = 0` for `S ⊆ 𝒞 \ {x}`. -/
  eq_zero_of_not_mem : ∀ (x : C) (S : Finset C), x ∉ S → P x S = 0
  /-- (iii): `∑_{x ∈ S} 𝒫(x, S) ⩽ 1`. -/
  sum_le_one : ∀ S : Finset C, ∑ x ∈ S, P x S ≤ 1
  /-- (iv), `x ∈ S`: `𝒫(x, S) ⩾ 𝒫(x, S')` for `S ⊆ S'`. -/
  antitone : ∀ S S' : Finset C, S ⊆ S' → ∀ x ∈ S, P x S' ≤ P x S
  /-- (iv), `x = 0`: `𝒫(0, S) ⩾ 𝒫(0, S')` for `S ⊆ S'`. -/
  noPurchase_antitone : ∀ S S' : Finset C, S ⊆ S' → RevenueOrdered.Ratio.noPurchase P S' ≤ RevenueOrdered.Ratio.noPurchase P S

/-- The seller's revenue `∑_{x ∈ S} 𝒫(x, S) r(x)` when offering `S` (Definition 1, p. 6). -/
def rev (P : C → Finset C → ℝ) (r : C → ℝ) (S : Finset C) : ℝ :=
  ∑ x ∈ S, P x S * r x

end RevenueOrdered.Tightness


