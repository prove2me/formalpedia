-- Prove2me | Definitions.Def_SubmodOrder_thresholdAdd
-- name    : SubmodOrder_thresholdAdd
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:36:56.979984+00:00
-- url     : https://prove2.me/theorems/3b49095d-389f-4628-95ad-388b37fd7f25
-- title:
--   Algorithm 2: Threshold Add$(k,\tau)$
-- statement:
--   Let the ground set be indexed in a (known) order $\pi$, let $k$ be a cardinality and $\tau$ a threshold. **Threshold Add** starts from $S=\emptyset$ and scans the elements once in increasing $\pi$-index. While $|S|<k$, the next element $e$ is added to $S$ if
--
--   $$
--   f(e\mid S)\ \ge\ \tau ;
--   $$
--
--   once $|S|=k$ the scan stops. The output is a set $S$ of at most $k$ elements.
--
--   Threshold Add is the subroutine of Algorithm 1, which runs it for a geometric grid of thresholds.
--
--   **Formalization Note** The algorithm is a value-oracle program built from $\pi$, $k$ and $\tau$ only; it returns the pair $(S,f(S))$. The value of the current set is kept, so each scanned element costs one query, $f(S\cup\{e\})$, and $f(\emptyset)=0$, the paper's normalization, is not queried.
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, Algorithm 2, p.13; p.13, "In Algorithm 2, let the ground set N = {1, 2, · · · , n} be indexed in submodular order."

import Mathlib
import Definitions.Def_SubmodOrder_OracleProg

namespace SubmodOrder

/-- The ground set listed in increasing `π`-index: `π⁻¹(0), π⁻¹(1), …, π⁻¹(n−1)` (Udwani,
arXiv:2107.02743v5, p.13: "In Algorithm 2, let the ground set N = {1, 2, · · · , n} be indexed in
submodular order."). -/
def orderList {α : Type*} {n : ℕ} (π : α ≃ Fin n) : List α :=
  (List.finRange n).map π.symm

/-- The scan loop of Threshold Add: `taLoop k τ l S v` scans the list `l` with current set `S`,
whose value `f(S)` is cached as `v`. While `|S| < k`, the next element `e` is tested by querying
`f(S ∪ {e})`; it is added when `f(e | S) = f(S ∪ {e}) − f(S) ≥ τ`. -/
noncomputable def taLoop {α : Type*} [DecidableEq α] (k : ℕ) (τ : ℝ) :
    List α → Finset α → ℝ → OracleProg α (Finset α × ℝ)
  | [], S, v => OracleProg.pure (S, v)
  | e :: es, S, v =>
    if S.card < k then
      OracleProg.query (insert e S) fun w =>
        if τ ≤ w - v then taLoop k τ es (insert e S) w else taLoop k τ es S v
    else OracleProg.pure (S, v)

/-- Algorithm 2, Threshold Add(k, τ) (Udwani, arXiv:2107.02743v5, p.13):

```
Input: Cardinality k, threshold τ, N indexed in submodular order;
Initialize S = ∅;
for i ∈ {1, 2, · · · , n} and |S| < k do
  if f(i|S) ≥ τ then S → S ∪ {i};
end
Output: Set S of size at most k;
```

The program returns the pair `(S, f(S))`.

**Formalization Note.** The elements are scanned once, in increasing `π`-index (`orderList π`),
and the scan stops as soon as `|S| = k`. The value `f(S)` of the current set is cached, so each
scanned element costs exactly one query, `f(S ∪ {e})`; the initial value `f(∅) = 0` is the
paper's normalization (p.2) and is not queried. The program is built from `π`, `k` and `τ` only. -/
noncomputable def thresholdAdd {α : Type*} [DecidableEq α] {n : ℕ} (π : α ≃ Fin n) (k : ℕ)
    (τ : ℝ) : OracleProg α (Finset α × ℝ) :=
  taLoop k τ (orderList π) ∅ 0

end SubmodOrder


