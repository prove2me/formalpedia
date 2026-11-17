-- Prove2me | Definitions.Def_GSRandomOrder_Supplement_IsOptimalAllocation
-- name    : GSRandomOrder_Supplement_IsOptimalAllocation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:06:44.144682+00:00
-- url     : https://prove2.me/theorems/6c799f1f-e973-4d3a-942a-12edf2df2459
-- title:
--   Optimal allocation $X^S$ of a set $S$
-- statement:
--   Let $v_1,\dots,v_m$ be valuations on $N$ and $S\subseteq N$. An $m$-tuple $X=(X_1,\dots,X_m)$ is an **optimal allocation** of $S$ if the sets $X_i\subseteq S$ are pairwise disjoint and
--   $$
--   \sum_{i=1}^m v_i(X_i)=W(S).
--   $$
--   The prefix proposals of §4.3 fix such an allocation $X^S$ for every $S\subseteq N$; bidder $i$'s proposal map is $P_i(S)=X^S_i$.
--
--   **Formalization Note** The equality is in `WithBot ℝ`, with $W(S)$ the real number `welfare v S`.
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §4.3, p.15, "Prefix proposals"

import Mathlib
import Definitions.Def_GSRandomOrder_Supplement_welfare

set_option autoImplicit false

namespace GSRandomOrder.Supplement

/-- **Optimal allocation of a set** `S` (R. Paes Leme, M. Pál, N. Patel, *Gross Substitutes
Welfare in Random Order*, STOC 2027 submission, manuscript sha256 69787f50…, §4.3, p.15, "Prefix
proposals"): `X = (X_1, …, X_m)` is an optimal allocation of `S` if the `X_i ⊆ S` are pairwise
disjoint and `Σ_i v_i(X_i) = W(S)`.

**Formalization Note.** The equality is in `WithBot ℝ`, with `W(S)` the real number `welfare v S`
(for valuations it is the maximum of (2), which is `≥ 0`). The paper's prefix optimum `X^S` is a
choice of such an `X` for every `S ⊆ N`. -/
def IsOptimalAllocation {n m : ℕ} (v : Fin m → Finset (Fin n) → WithBot ℝ)
    (S : Finset (Fin n)) (X : Fin m → Finset (Fin n)) : Prop :=
  (∀ i, X i ⊆ S) ∧ (Pairwise fun i j => Disjoint (X i) (X j)) ∧
    ∑ i, v i (X i) = ((welfare v S : ℝ) : WithBot ℝ)

end GSRandomOrder.Supplement


