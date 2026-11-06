-- Prove2me | Definitions.Def_SilverRateSC_IsRepairSelection
-- name    : SilverRateSC_IsRepairSelection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:45:03.887104+00:00
-- url     : https://prove2.me/theorems/e6211194-d901-4077-af18-3fdca39f5a27
-- title:
--   The repair checkpoint selection rule (§4.2)
-- statement:
--   Let $h_1,\dots,h_r\ge0$ be the stepsizes of the unselected tail, with $S:=h_1+\dots+h_r\ge S_0>0$. Select $q\in\{1,2\}$ checkpoints from the **shortest suffix** whose stepsizes sum to more than $S_0/8$:
--   1. if this suffix contains a stepsize $h_t\ge S_0/16$, select one such index as the only checkpoint $t_1$;
--   2. otherwise, select $t_1<t_2$ in the suffix with $b_1,b_2\ge S_0/(64r^2)$ and $s_2:=\sum_{t=t_1+1}^{t_2-1}h_t\le\min\{b_1,b_2\}$.
--
--   The rule is nondeterministic; the predicate holds for every list $[t_1]$ or $[t_1,t_2]$ it permits.
--
--   **Formalization Note** The suffix starts at the largest $j\le r$ with $\sum_{t=j}^rh_t>S_0/8$.
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), §4.2, p.18

import Mathlib

open Classical

namespace SilverRateSC

/-- The start `j*` of the shortest suffix `h_{j*}, …, h_r` whose stepsizes sum to more than
`S_0/8`: the largest `j ≤ r` with `∑_{t=j}^r h_t > S_0/8`. -/
noncomputable def suffixStart (S₀ : ℝ) (r : ℕ) (h : ℕ → ℝ) : ℕ :=
  Nat.findGreatest (fun j => S₀ / 8 < ∑ t ∈ Finset.Icc j r, h t) r

/-- **The repair checkpoint selection rule** (§4.2). For stepsizes `h_1, …, h_r ≥ 0` of the
unselected tail with `S := h_1 + ⋯ + h_r ≥ S_0 > 0`, select `q ∈ {1, 2}` checkpoints from the
shortest suffix whose stepsizes sum to more than `S_0/8`:
* if this suffix contains a stepsize `h_t ≥ S_0/16`, select one such index as the only
  checkpoint `t_1`;
* otherwise, select `t_1 < t_2` in the suffix with `b_1, b_2 ≥ S_0/(64 r²)` and
  `s_2 := ∑_{t=t_1+1}^{t_2−1} h_t ≤ min{b_1, b_2}`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, §4.2, "Repair checkpoint selection rule", p. 18.

**Formalization Note** The rule is nondeterministic, so it is a predicate on the selected list
`ts = [t_1]` or `[t_1, t_2]` (1-based positions). The suffix starts at `suffixStart S₀ r h`
(`Nat.findGreatest`; under `S > S_0/8` it is at least `1`). -/
def IsRepairSelection (S₀ : ℝ) (r : ℕ) (h : ℕ → ℝ) (ts : List ℕ) : Prop :=
  ((∃ t, suffixStart S₀ r h ≤ t ∧ t ≤ r ∧ S₀ / 16 ≤ h t) ∧
      ∃ t₁, ts = [t₁] ∧ suffixStart S₀ r h ≤ t₁ ∧ t₁ ≤ r ∧ S₀ / 16 ≤ h t₁) ∨
    ((¬ ∃ t, suffixStart S₀ r h ≤ t ∧ t ≤ r ∧ S₀ / 16 ≤ h t) ∧
      ∃ t₁ t₂, ts = [t₁, t₂] ∧ t₁ < t₂ ∧ suffixStart S₀ r h ≤ t₁ ∧ t₂ ≤ r ∧
        S₀ / (64 * (r : ℝ) ^ 2) ≤ h t₁ ∧ S₀ / (64 * (r : ℝ) ^ 2) ≤ h t₂ ∧
        ∑ t ∈ Finset.Ioo t₁ t₂, h t ≤ min (h t₁) (h t₂))

end SilverRateSC


