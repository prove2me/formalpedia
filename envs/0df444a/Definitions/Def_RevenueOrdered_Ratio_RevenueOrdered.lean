-- Prove2me | Definitions.Def_RevenueOrdered_Ratio_RevenueOrdered
-- name    : RevenueOrdered_Ratio_RevenueOrdered
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:28:16.841128+00:00
-- url     : https://prove2.me/theorems/9f013576-76fc-430a-bb53-3a994892297c
-- title:
--   §3, p. 7 — distinct revenues r_1 < ⋯ < r_k, revenue-ordered assortments S_i and their best revenue
-- statement:
--   Fix a finite nonempty set of products $\mathcal C$, a system of choice probabilities $\mathcal P$ and a revenue function $r:\mathcal C\to\mathbb R_{>0}$. Let
--   $$
--   0<r_1<r_2<\cdots<r_k
--   $$
--   be the distinct values taken by $r$, sorted increasingly, so $k$ is the number of distinct revenues (not the number of products), and set $r_0:=0$. For each $i\in[k]=\{1,\dots,k\}$ the **revenue-ordered assortment** $S_i$ is the set of all products of revenue at least $r_i$:
--   $$
--   S_i=\{x\in\mathcal C : r(x)\ge r_i\}.
--   $$
--   The **revenue-ordered assortments strategy** compares the revenues of the $k$ sets $S_1,\dots,S_k$ and chooses one of maximum revenue; its value is
--   $$
--   \mathrm{RO}=\max_{i\in[k]}\operatorname{rev}(S_i).
--   $$
--   Finally, the quantity that appears in the approximation guarantee of Theorem 3.2 is
--   $$
--   \sum_{i=1}^{k}\frac{r_i-r_{i-1}}{r_i}.
--   $$
--
--   The strategy is the heuristic whose guarantees the mission studies; it examines only $k$ assortments, not all $2^{|\mathcal C|}$.
--
--   **Formalization Note** The paper's indices are kept 1-based: `level r i` is $r_i$ for $1\le i\le k$, `level r 0 = 0` is the convention $r_0=0$, and indices $i>k$ (never used) also return $0$. `numVals r` is $k$, the cardinality of the image of $r$; `sortedVals r` is the 0-based increasing enumeration of that image. `roSet r i` is $S_i$, `roValue P r` is the maximum over $i\in\{1,\dots,k\}$ only (it needs `[Nonempty C]`, which makes $k\ge1$), and `ratioSum r` is the sum above over $i\in\{1,\dots,k\}$.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 7, §3 (revenue-ordered assortments strategy) and p. 8, Theorem 3.2 (r_0 := 0)

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model

namespace RevenueOrdered.Ratio

noncomputable section

variable {C : Type*} [Fintype C]

/-- The set `{r(x) : x ∈ 𝒞}` of distinct values of the revenue function. -/
def revVals (r : C → ℝ) : Finset ℝ := Finset.univ.image r

/-- `k`, the number of distinct values of `r` (§3, p. 7). -/
def numVals (r : C → ℝ) : ℕ := (revVals r).card

/-- The distinct values of `r` sorted increasingly, 0-based: `sortedVals r j = r_{j+1}`. -/
def sortedVals (r : C → ℝ) : Fin (numVals r) ↪o ℝ :=
  (revVals r).orderEmbOfFin rfl

/-- The paper's `r_i` with its 1-based index (§3, p. 7): for `1 ≤ i ≤ k`, `level r i` is the
`i`-th smallest distinct value of `r`, so `r_1 < r_2 < ⋯ < r_k`; `level r 0 = 0` is the paper's
convention `r_0 := 0` (Theorem 3.2, p. 8). Indices `i > k` are never used and return `0`. -/
def level (r : C → ℝ) (i : ℕ) : ℝ :=
  if h : 1 ≤ i ∧ i ≤ numVals r then sortedVals r ⟨i - 1, by omega⟩ else 0

/-- The revenue-ordered assortment `S_i = {x ∈ 𝒞 : r(x) ≥ r_i}` (§3, p. 7), used for
`1 ≤ i ≤ k`. -/
def roSet (r : C → ℝ) (i : ℕ) : Finset C :=
  Finset.univ.filter (fun x => level r i ≤ r x)

lemma numVals_pos [Nonempty C] (r : C → ℝ) : 0 < numVals r :=
  Finset.card_pos.mpr (Finset.univ_nonempty.image r)

/-- The revenue earned by the revenue-ordered assortments strategy (§3, p. 7):
`RO = max_{i ∈ [k]} rev(S_i)`, the maximum over the `k` sets `S_1, …, S_k` only. -/
def roValue [Nonempty C] (P : C → Finset C → ℝ) (r : C → ℝ) : ℝ :=
  (Finset.Icc 1 (numVals r)).sup'
    (Finset.nonempty_Icc.mpr (numVals_pos r)) (fun i => revenue P r (roSet r i))

/-- `∑_{i=1}^{k} (r_i − r_{i−1}) / r_i` with `r_0 = 0` (Theorem 3.2, p. 8). -/
def ratioSum (r : C → ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (numVals r), (level r i - level r (i - 1)) / level r i

end

end RevenueOrdered.Ratio


