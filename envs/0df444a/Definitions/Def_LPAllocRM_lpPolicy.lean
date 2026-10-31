-- Prove2me | Definitions.Def_LPAllocRM_lpPolicy
-- name    : LPAllocRM_lpPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:59.004643+00:00
-- url     : https://prove2.me/theorems/49f0799e-3f41-4be9-a143-407304e8528f
-- title:
--   The allocation policy $\pi_j(t)\equiv 1(D_j(t)\le y_j)$, eq. (4)
-- statement:
--   For an allocation vector $y\in\mathbb R^n$, the allocation policy accepts a class-$j$ request at time $t$ if and only if
--
--   $$D_j(t)\le y_j,$$
--
--   where $D_j(t)$ is the number of class-$j$ requests in $(0,t]$, including one arriving at $t$. With $y=x^*$ this is the paper's policy $\pi^{LP}$ of (4), "accept up to $x^*_j$ customers in class $j$"; in the $k$th problem the paper uses $y=kx^*$ ("we adopt the convention that we use $kx^*$ to create our allocations").
--
--   **Formalization Note** $D_j(t)$ is read from the history at its right end point $t$, so the current arrival is counted, and the comparison is $\le$.
-- source:
--   Cooper, Asymptotic Behavior of an Allocation Policy for Revenue Management, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855, eq. (4), p.723; §4, p.723 (convention kx*)

import Mathlib
import Definitions.Def_LPAllocRM_Policy

namespace LPAllocRM

/-- The allocation policy with allocation vector `y`: accept a class-`j` request at time `t` iff
the number `D_j(t)` of class-`j` requests in `(0, t]`, including one arriving at `t`, is at most
`y_j`: `π_j(t) ≡ 1(D_j(t) ≤ y_j)`. The paper's `π^LP` is `lpPolicy x*`, and in the kth problem
`lpPolicy (k • x*)`.
Cooper, *Asymptotic Behavior of an Allocation Policy for Revenue Management*, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855,
(4), p.723 (PDF p.4): "π^LP_j(t) ≡ 1(D_j(t) ⩽ x∗_j)"; "Recall that D_j(t) includes any class j
arrival at time t"; §4, p.723: "we adopt the convention that we use kx∗ to create our allocations".

**Formalization Note** `D_j(t)` is read from the history at its right end point `t`, which belongs
to `Set.Iic t`, so the current arrival is counted. The comparison is `≤` (not `<`). -/
noncomputable def lpPolicy {n : ℕ} (y : Fin n → ℝ) : Policy n :=
  fun t h j => decide (((h ⟨t, Set.mem_Iic.mpr le_rfl⟩ j : ℕ) : ℝ) ≤ y j)

end LPAllocRM


