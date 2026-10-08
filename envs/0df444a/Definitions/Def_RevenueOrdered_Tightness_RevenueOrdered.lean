-- Prove2me | Definitions.Def_RevenueOrdered_Tightness_RevenueOrdered
-- name    : RevenueOrdered_Tightness_RevenueOrdered
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:05:47.684894+00:00
-- url     : https://prove2.me/theorems/e4851c8b-4fd4-474e-bbda-d99fa0e6ff9c
-- title:
--   Revenue-ordered assortments and the bound quantities $k$, $\sum_i (r_i-r_{i-1})/r_i$, $\sum_i (N_i-N_{i+1})/N_i$
-- statement:
--   Fix a system of choice probabilities $\mathcal P$ on a finite nonempty product set $\mathcal C$ and revenues $r:\mathcal C\to\mathbb R$. Let $r_1<r_2<\dots<r_k$ be the distinct values taken by $r$, and set $r_0:=0$. For $i\in[k]$ the $i$-th **revenue-ordered assortment** is
--   $$
--   S_i=\{x\in\mathcal C: r(x)\ge r_i\},
--   $$
--   and the revenue-ordered assortments strategy earns $\mathrm{RO}=\max_{i\in[k]}\mathrm{rev}(S_i)$, the best of these $k$ sets only.
--
--   The module also defines the quantities appearing in the three approximation guarantees of §3:
--   1. $k$, the number of distinct revenues (Theorem 3.1);
--   2. $D_r=\sum_{i=1}^k \frac{r_i-r_{i-1}}{r_i}$ (Theorem 3.2);
--   3. for a set $S^*\subseteq\mathcal C$, $N_i=\sum_{x\in S^*,\,r(x)\ge r_i}\mathcal P(x,S^*)$ for $i\in[k]$, $N_{k+1}:=0$, $\ell$ the largest $i\in[k]$ with $N_i>0$, and
--   $$
--   D_N(S^*)=\sum_{i=1}^{\ell}\frac{N_i-N_{i+1}}{N_i}\qquad\text{(Theorem 3.3).}
--   $$
--
--   **Formalization Note** The sorted distinct revenues are indexed by `Fin k` from $0$: the Lean index $i$ is the paper's $i+1$. $r_0=0$ is a separate case (`prevRevenue`). $\mathrm{RO}$ is `Finset.sup'` over the $k$ threshold sets and requires `Nonempty C`. $\ell$ is a `WithBot (Fin k)`, equal to $\bot$ (empty sum) when no $N_i$ is positive.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, pp. 7–9, §3, Theorems 3.1–3.3

import Mathlib
import Definitions.Def_RevenueOrdered_Tightness_ChoiceModel

noncomputable section

namespace RevenueOrdered.Tightness

/-! Revenue-ordered assortments and the three bound quantities of §3
(Berbeglia & Joret, arXiv:1606.01371v3, pp. 7–9).

Indexing convention: the paper's distinct revenues `r_1 < ⋯ < r_k` (`i ∈ [k]`, 1-based) are
`sortedRevenue r i` for `i : Fin k` (0-based), so the paper's `r_i` is `sortedRevenue r ⟨i - 1, _⟩`.
The paper's `r_0 := 0` is `prevRevenue r ⟨0, _⟩ = 0`, a separate case. -/

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The set of distinct values taken by the revenue function `r`. -/
def revenueValues (r : C → ℝ) : Finset ℝ :=
  Finset.univ.image r

/-- `k`, the number of distinct revenues (p. 7). -/
def numRevenues (r : C → ℝ) : ℕ :=
  (revenueValues r).card

/-- The distinct revenues sorted increasingly, `r_1 < r_2 < ⋯ < r_k` (p. 7); 0-based. -/
def sortedRevenue (r : C → ℝ) : Fin (numRevenues r) ↪o ℝ :=
  (revenueValues r).orderEmbOfFin rfl

/-- The previous revenue `r_{i-1}` of `r_i`, with `r_0 := 0` (p. 8). -/
def prevRevenue (r : C → ℝ) (i : Fin (numRevenues r)) : ℝ :=
  if h : i.val = 0 then 0 else sortedRevenue r ⟨i.val - 1, by omega⟩

/-- The `i`-th revenue-ordered assortment `S_i = {x ∈ 𝒞 : r(x) ⩾ r_i}` (p. 7). -/
def thresholdSet (r : C → ℝ) (i : Fin (numRevenues r)) : Finset C :=
  Finset.univ.filter (fun x => sortedRevenue r i ≤ r x)

omit [DecidableEq C] in
theorem numRevenues_pos [Nonempty C] (r : C → ℝ) : 0 < numRevenues r :=
  Finset.card_pos.mpr (Finset.univ_nonempty.image r)

/-- The revenue of the revenue-ordered assortments strategy, `max_{i ∈ [k]} rev(S_i)`: the best
of the `k` threshold sets only (p. 7). Requires `𝒞 ≠ ∅`, i.e. `k ⩾ 1`. -/
def roValue [Nonempty C] (P : C → Finset C → ℝ) (r : C → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin (numRevenues r))).sup'
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, numRevenues_pos r⟩⟩)
    (fun i => rev P r (thresholdSet r i))

/-- The bound quantity of Theorem 3.2, `∑_{i=1}^{k} (r_i - r_{i-1}) / r_i` with `r_0 = 0`
(p. 8). -/
def revenueGapSum (r : C → ℝ) : ℝ :=
  ∑ i : Fin (numRevenues r), (sortedRevenue r i - prevRevenue r i) / sortedRevenue r i

/-- `N_i := ∑_{x ∈ S, r(x) ⩾ r_i} 𝒫(x, S)` (Theorem 3.3, p. 9), for the set `S = S^*`. -/
def purchaseAbove (P : C → Finset C → ℝ) (r : C → ℝ) (S : Finset C)
    (i : Fin (numRevenues r)) : ℝ :=
  ∑ x ∈ S.filter (fun x => sortedRevenue r i ≤ r x), P x S

/-- `N_{i+1}`, with `N_{k+1} := 0` (p. 9). -/
def nextPurchaseAbove (P : C → Finset C → ℝ) (r : C → ℝ) (S : Finset C)
    (i : Fin (numRevenues r)) : ℝ :=
  if h : i.val + 1 < numRevenues r then purchaseAbove P r S ⟨i.val + 1, h⟩ else 0

/-- `ℓ`, the maximum index `i ∈ [k]` with `N_i > 0` (Theorem 3.3, p. 9), as an element of
`WithBot (Fin k)`; it is `⊥` exactly when no `N_i` is positive. -/
def lastPositive (P : C → Finset C → ℝ) (r : C → ℝ) (S : Finset C) :
    WithBot (Fin (numRevenues r)) :=
  (Finset.univ.filter (fun i => 0 < purchaseAbove P r S i)).max

/-- The bound quantity of Theorem 3.3, `∑_{i=1}^{ℓ} (N_i - N_{i+1}) / N_i` (p. 9). -/
def purchaseGapSum (P : C → Finset C → ℝ) (r : C → ℝ) (S : Finset C) : ℝ :=
  ∑ i ∈ Finset.univ.filter
      (fun i : Fin (numRevenues r) => (i : WithBot (Fin (numRevenues r))) ≤ lastPositive P r S),
    (purchaseAbove P r S i - nextPurchaseAbove P r S i) / purchaseAbove P r S i

end RevenueOrdered.Tightness

end


