-- Prove2me | Definitions.Def_LPAllocRM_value
-- name    : LPAllocRM_value
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:08:30.349156+00:00
-- url     : https://prove2.me/theorems/973c9a89-8cc3-46e4-a4e0-59a0aa9f94d0
-- title:
--   The optimal value $v$ of the revenue management problem, eq. (1)
-- statement:
--   The value of the revenue management problem with capacity $b$ is
--
--   $$v\equiv\sup_{\pi\in\Pi}\{E(f\cdot N^\pi) : AN^\pi\le b,\ 0\le N^\pi\le D(\tau)\},$$
--
--   the supremum of the expected revenue over all admissible history-dependent policies. The value $v^{(k)}$ of the $k$th problem is the case $b=kc$ with the arrival process $D^{(k)}$.
--
--   **Formalization Note** The supremum is Lean's real `sSup`, which returns $0$ on an empty or unbounded set; in the paper's setting the set is nonempty (the LP policy and the reject-all policy are admissible) and bounded above by $k\beta$ (Lemma 2), so it is the paper's supremum. The expectation is the Bochner integral.
-- source:
--   Cooper, Asymptotic Behavior of an Allocation Policy for Revenue Management, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855, eq. (1), p.722; §4, p.723

import Mathlib
import Definitions.Def_LPAllocRM_Admissible
import Definitions.Def_LPAllocRM_revenue
open MeasureTheory

namespace LPAllocRM

/-- The optimal value of the revenue management problem with capacity `b`:
`v ≡ sup_{π ∈ Π} {E(f · N^π) : A N^π ≤ b, 0 ≤ N^π ≤ D(τ)}`, the supremum of the expected revenue
over all admissible history-dependent policies. In the kth problem `v^(k)` is
`value A (k • c) f τ (P k) (D k)`.
Cooper, *Asymptotic Behavior of an Allocation Policy for Revenue Management*, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855,
(1), p.722 (PDF p.3); "v^(k) is the value of the kth problem; see (1)", §4, p.723 (PDF p.4).

**Formalization Note** The supremum is Lean's real `sSup`, which returns `0` on an empty or
unbounded-above set. In the paper's setting the set is nonempty (`π^LP`, and the reject-all
policy, are admissible) and bounded above (Lemma 2: by `k β`), so `value` is the paper's `v`. The
expectation is the Bochner integral; for admissible `π` the revenue is integrable when `D(τ)` is,
since `0 ≤ N^π ≤ D(τ)`. -/
noncomputable def value {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (f : Fin n → ℝ) (τ : ℝ) (P : Measure Ω) (D : Ω → ℝ → Fin n → ℕ) : ℝ :=
  sSup ((fun π : Policy n => ∫ ω, revenue f τ π (D ω) ∂P) '' {π | Admissible A b τ P D π})

end LPAllocRM


