-- Prove2me | Definitions.Def_LittleCharity_GMMS_Setting
-- name    : LittleCharity_GMMS_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T10:17:24.402374+00:00
-- url     : https://prove2.me/theorems/1ec71ab8-5b75-417a-95f4-1831d12c6979
-- title:
--   Valuations, partial allocations, EFX, maximin share, GMMS, and pool donation
-- statement:
--   Let $N$ be a finite set of agents and $M$ a finite set of indivisible goods. A **bundle** is a subset of $M$, and agent $i$ has a nonnegative **additive valuation** $v_i$: the value of a bundle is the sum of its singleton-good values. A **partial allocation** $X=(X_i)_{i\in N}$ assigns pairwise disjoint bundles; its **pool** is $P=M\setminus\bigcup_{i\in N}X_i$. It is complete when $P$ is empty.
--
--   The allocation is **EFX** when $v_i(X_j\setminus\{g\})\le v_i(X_i)$ for every $i,j$ and every $g\in X_j$. The **envy graph** has an edge $i\to j$ exactly when $v_i(X_i)<v_i(X_j)$; a **source** is an agent with no incoming edge.
--
--   For $k\ge1$, let $\operatorname{MMS}_i(k,S)$ be the maximum, over all partitions of a good set $S$ into $k$ labelled bundles, of the minimum value of a part to agent $i$. An allocation $Y$ is **$\alpha$-GMMS** when
--
--   $$
--   v_i(Y_i)\ge\alpha\operatorname{MMS}_i\!\left(|N'|,\bigcup_{j\in N'}Y_j\right)
--   \quad\text{for every }N'\subseteq N\text{ and }i\in N'.
--   $$
--
--   Finally, $\operatorname{donate}(X,s)$ leaves every bundle except $s$'s unchanged and gives $P$ to $s$. These definitions express the finite allocation model and the constructed allocation used in Theorem 16.
--
--   **Formalization Note** Agents and goods are `Fin n` and `Fin m`, with agents numbered from zero. Partitions may have empty parts. Membership $i\in N'$ guarantees the maximin-share part count is positive. Completeness is separate from the definition of GMMS, matching Definition 15 and the convention on p. 5.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, pp. 3–5, 8, 15, §1.1, Definition 1, Definition 15, constructed allocation before Theorem 16

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_LittleCharity_MMS_Setting

namespace LittleCharity.GMMS

/-- A complete allocation has disjoint bundles and no unallocated goods (pp. 3, 5). -/
def IsCompleteAllocation {n m : ℕ} (X : Fin n → Finset (Fin m)) : Prop :=
  LittleCharity.EFX.IsPartialAllocation X ∧ LittleCharity.EFX.pool X = ∅

/-- Definition 15 (p. 15). The page reuses `i` as the bound variable of the union; as in the
proof of Theorem 16 (p. 16, "for every Ñ ⊆ N and all i ∈ Ñ"), the agent `i` ranges over the
group `N'`, so `N'.card ≥ 1` and `mms` is never taken with zero parts. -/
def IsGMMS {n m : ℕ} (α : ℝ) (v : Fin n → Finset (Fin m) → ℝ)
    (Y : Fin n → Finset (Fin m)) : Prop :=
  ∀ N' : Finset (Fin n), ∀ i ∈ N',
    α * LittleCharity.MMS.mms (v i) N'.card (N'.biUnion Y) ≤ v i (Y i)

/-- The complete allocation `Y` made by giving the pool to a source `s` (p. 15; the page's
agent 1 is `s`). -/
def donate {n m : ℕ} (X : Fin n → Finset (Fin m)) (s : Fin n) :
    Fin n → Finset (Fin m) :=
  Function.update X s (X s ∪ LittleCharity.EFX.pool X)

end LittleCharity.GMMS


