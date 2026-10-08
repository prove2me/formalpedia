-- Prove2me | Definitions.Def_RevenueOrdered_Nesting_RevenueOrdered
-- name    : RevenueOrdered_Nesting_RevenueOrdered
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:06:37.181659+00:00
-- url     : https://prove2.me/theorems/9698f26c-463b-4375-9cd0-7deba209197d
-- title:
--   §3, p. 7 and §5, p. 25 — distinct revenues r_1 < ⋯ < r_k and revenue-ordered assortments S_ℓ
-- statement:
--   Fix a finite nonempty set of products $\mathcal C$ and a revenue function $r:\mathcal C\to\mathbb R$. Let
--   $$
--   r_1<r_2<\cdots<r_k
--   $$
--   be the distinct values taken by $r$, sorted increasingly, so $k\ge 1$ is the number of distinct revenues (not the number of products), and $r_k=\max_{x\in\mathcal C} r(x)$ is the revenue of the most expensive product. For each index $\ell\in[k]=\{1,\dots,k\}$ the **revenue-ordered assortment** $S_\ell$ is the set of all products of revenue at least $r_\ell$:
--   $$
--   S_\ell=\{x\in\mathcal C : r(x)\ge r_\ell\}.
--   $$
--   Thus $S_1=\mathcal C$, $S_k$ consists of the most expensive products, and a larger index gives a smaller set: $S_k\subseteq S_{k-1}\subseteq\cdots\subseteq S_1$. In §5 the paper sorts the products by non-increasing revenue and writes $S_\ell=\{1,\dots,j(\ell)\}$.
--
--   The definition also provides, for a function $f$ on indices, the set $\{\ell\in[k] : f(\ell)=\max_{\ell'\in[k]}f(\ell')\}$ of indices at which $f$ is maximal over $[k]$; it is nonempty, so its minimum is well defined.
--
--   **Formalization Note** `numVals r` is $k$; `level r ℓ` is $r_\ell$ with the paper's 1-based index (values outside $1\le\ell\le k$ are never used and are set to $0$); `topRevenue r` is $r_k$; `roSet r ℓ` is $S_\ell$ as a `Finset`; `levels r` is $[k]$ as `Finset.Icc 1 k`; `argmaxLevels r f` is the set of maximisers of `f` over $[k]$, with the maximum taken by `Finset.sup'` (nonempty because `C` is nonempty).
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 7, §3, and p. 25, §5 (r_1, …, r_k and j(ℓ))

import Mathlib
import Definitions.Def_RevenueOrdered_Nesting_Model
import Definitions.Def_RevenueOrdered_Ratio_RevenueOrdered

namespace RevenueOrdered.Nesting

noncomputable section

variable {C : Type*} [Fintype C]

/-- `r_k`, the largest revenue (the revenue of the most expensive product). -/
def topRevenue (r : C → ℝ) : ℝ := RevenueOrdered.Ratio.level r (RevenueOrdered.Ratio.numVals r)

lemma numVals_pos [Nonempty C] (r : C → ℝ) : 0 < RevenueOrdered.Ratio.numVals r :=
  Finset.card_pos.mpr (Finset.univ_nonempty.image r)

/-- The index set `[k] = {1, …, k}` of the revenue-ordered assortments. -/
def levels (r : C → ℝ) : Finset ℕ := Finset.Icc 1 (RevenueOrdered.Ratio.numVals r)

lemma levels_nonempty [Nonempty C] (r : C → ℝ) : (levels r).Nonempty :=
  Finset.nonempty_Icc.mpr (numVals_pos r)

/-- `{ℓ ∈ [k] : f(ℓ) = max_{ℓ' ∈ [k]} f(ℓ')}`, the indices at which `f` attains its maximum
over `[k]`. -/
def argmaxLevels [Nonempty C] (r : C → ℝ) (f : ℕ → ℝ) : Finset ℕ :=
  (levels r).filter (fun ℓ => f ℓ = (levels r).sup' (levels_nonempty r) f)

lemma argmaxLevels_nonempty [Nonempty C] (r : C → ℝ) (f : ℕ → ℝ) :
    (argmaxLevels r f).Nonempty := by
  obtain ⟨ℓ, hℓ, h⟩ := Finset.exists_mem_eq_sup' (levels_nonempty r) f
  exact ⟨ℓ, Finset.mem_filter.mpr ⟨hℓ, h.symm⟩⟩

end

end RevenueOrdered.Nesting


