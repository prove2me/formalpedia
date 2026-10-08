-- Prove2me | Definitions.Def_RevenueOrdered_UDPmin_Model
-- name    : RevenueOrdered_UDPmin_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T16:55:11.58598+00:00
-- url     : https://prove2.me/theorems/e7bc05e7-50e2-410a-ad29-cc30d9509a27
-- title:
--   Regular discrete choice models, assortment revenue, OPT and revenue-ordered assortments
-- statement:
--   Let $\mathcal C$ be a finite set of products. A **system of choice probabilities** assigns to every assortment $S\subseteq\mathcal C$ and every product $x\in\mathcal C$ a number $\mathcal P(x,S)$, the probability that a consumer offered $S$ buys $x$. The option of buying nothing, denoted $0$, has probability
--   $$\mathcal P(0,S)=1-\sum_{x\in S}\mathcal P(x,S).$$
--   The model is **regular** when it satisfies the four axioms:
--
--   1. $\mathcal P(x,S)\ge 0$ for every $x\in\mathcal C\cup\{0\}$ and $S\subseteq\mathcal C$;
--   2. $\mathcal P(x,S)=0$ whenever $x\notin S$;
--   3. $\sum_{x\in S}\mathcal P(x,S)\le 1$ for every $S$;
--   4. $\mathcal P(x,S)\ge\mathcal P(x,S')$ for every $S\subseteq S'\subseteq\mathcal C$ and every $x\in S\cup\{0\}$ — in particular the no-purchase probability can only drop when the assortment grows.
--
--   Given revenues $r:\mathcal C\to\mathbb R_{>0}$, the **revenue** of an assortment is $\mathrm{rev}(S)=\sum_{x\in S}\mathcal P(x,S)\,r(x)$ and $\mathrm{OPT}=\max_{S\subseteq\mathcal C}\mathrm{rev}(S)$ (the empty assortment, of revenue $0$, is allowed).
--
--   Let $0<r_1<r_2<\dots<r_k$ be the distinct values of $r$, put $r_0:=0$, and let $S_i=\{x\in\mathcal C: r(x)\ge r_i\}$. The **revenue-ordered assortments** strategy earns
--   $$\mathrm{RO}=\max_{1\le i\le k}\mathrm{rev}(S_i).$$
--   The file also names the sum $\sum_{i=1}^k (r_i-r_{i-1})/r_i$ and the extreme values $r_1$, $r_k$, which appear in Theorem 3.2.
--
--   These are the objects of the paper's general assortment problem; the $\mathrm{UDP}_{\min}$ reduction of this mission produces an instance of it.
--
--   **Formalization Note** Products form a finite type `C`; `P : C → Finset C → ℝ` gives product probabilities and `noPurchase P S` the no-purchase probability. `IsRegular` lists axiom (i) for products and for the no-purchase option separately (the latter also follows from (iii)), and axiom (iv) for products and for the no-purchase option separately. `OPT` is `Finset.sup'` over all `Finset C`. `RO` is the maximum over the distinct values `t` of `r` of the revenue of the threshold set `{x | t ≤ r x}`. The sorted values are `revAt r : Fin k ↪o ℝ`, 0-based: `revAt r i` is the paper's $r_{i+1}$, and `prevRev r i` is $r_i$ with $r_0=0$ handled as a separate case.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, pp. 5–6 (§2, axioms (i)–(iv), Definition 1), p. 7 (§3, revenue-ordered assortments), p. 8 (Theorem 3.2, r_0 := 0)

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Tightness_ChoiceModel

namespace RevenueOrdered.UDPmin

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- A **regular discrete choice model** on the finite product set `C` (Berbeglia–Joret,
arXiv:1606.01371v3, §2, p. 6, axioms (i)–(iv)). Axiom (i) for the no-purchase option is the
field `noPurchase_nonneg` (it also follows from (iii)); axiom (iv) is stated both for products
(`antitone`) and for the no-purchase option (`noPurchase_antitone`). -/
structure IsRegular (P : C → Finset C → ℝ) : Prop where
  /-- (i) for products: `𝒫(x, S) ≥ 0`. -/
  nonneg : ∀ (x : C) (S : Finset C), 0 ≤ P x S
  /-- (i) for the no-purchase option: `𝒫(0, S) ≥ 0`. -/
  noPurchase_nonneg : ∀ S : Finset C, 0 ≤ RevenueOrdered.Ratio.noPurchase P S
  /-- (ii) `𝒫(x, S) = 0` when `x ∉ S`. -/
  eq_zero_of_not_mem : ∀ (x : C) (S : Finset C), x ∉ S → P x S = 0
  /-- (iii) `∑_{x ∈ S} 𝒫(x, S) ≤ 1`. -/
  sum_le_one : ∀ S : Finset C, ∑ x ∈ S, P x S ≤ 1
  /-- (iv) for products: `𝒫(x, S) ≥ 𝒫(x, S')` for `S ⊆ S'` and `x ∈ S`. -/
  antitone : ∀ (S S' : Finset C) (x : C), S ⊆ S' → x ∈ S → P x S' ≤ P x S
  /-- (iv) for the no-purchase option: `𝒫(0, S) ≥ 𝒫(0, S')` for `S ⊆ S'`. -/
  noPurchase_antitone : ∀ S S' : Finset C, S ⊆ S' → RevenueOrdered.Ratio.noPurchase P S' ≤ RevenueOrdered.Ratio.noPurchase P S

/-- The set `{r_1, …, r_k}` of distinct values taken by the revenue function (§3, p. 7). -/
noncomputable def revValues (r : C → ℝ) : Finset ℝ :=
  Finset.univ.image r

/-- `k`, the number of distinct revenue values. -/
noncomputable def numRev (r : C → ℝ) : ℕ :=
  (revValues r).card

/-- The distinct revenue values in increasing order: `revAt r i` is the paper's `r_{i+1}`
(0-based index `i : Fin k`). -/
noncomputable def revAt (r : C → ℝ) : Fin (numRev r) ↪o ℝ :=
  (revValues r).orderEmbOfFin rfl

/-- The predecessor value: `prevRev r i` is the paper's `r_i` for the 0-based index `i`, that is
`r_0 := 0` at `i = 0` and `revAt r (i - 1)` otherwise. -/
noncomputable def prevRev (r : C → ℝ) (i : Fin (numRev r)) : ℝ :=
  if h : (i : ℕ) = 0 then 0 else revAt r ⟨(i : ℕ) - 1, by omega⟩

/-- The threshold set `{x ∈ C : r(x) ≥ t}`; for `t = r_i` this is the paper's `S_i` (p. 7). -/
noncomputable def thresholdSet (r : C → ℝ) (t : ℝ) : Finset C :=
  Finset.univ.filter (fun x => t ≤ r x)

/-- The revenue-ordered value `RO = max_{i ∈ [k]} RevenueOrdered.Tightness.rev(S_i)` (§3, p. 7): the maximum of the revenue
over the `k` threshold sets `S_i = {x : r(x) ≥ r_i}`, one per distinct revenue value. -/
noncomputable def ro [Nonempty C] (P : C → Finset C → ℝ) (r : C → ℝ) : ℝ :=
  (revValues r).sup' (Finset.univ_nonempty.image r) (fun t => RevenueOrdered.Tightness.rev P r (thresholdSet r t))

/-- The sum `∑_{i=1}^{k} (r_i − r_{i−1}) / r_i` of Theorem 3.2 (p. 8), with `r_0 := 0`. -/
noncomputable def ratioSum (r : C → ℝ) : ℝ :=
  ∑ i : Fin (numRev r), (revAt r i - prevRev r i) / revAt r i

/-- The largest revenue value `r_k`. -/
noncomputable def rMax [Nonempty C] (r : C → ℝ) : ℝ :=
  (revValues r).max' (Finset.univ_nonempty.image r)

/-- The smallest revenue value `r_1`. -/
noncomputable def rMin [Nonempty C] (r : C → ℝ) : ℝ :=
  (revValues r).min' (Finset.univ_nonempty.image r)

end RevenueOrdered.UDPmin


