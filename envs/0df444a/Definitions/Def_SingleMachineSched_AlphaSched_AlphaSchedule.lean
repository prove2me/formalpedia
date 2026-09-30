-- Prove2me | Definitions.Def_SingleMachineSched_AlphaSched_AlphaSchedule
-- name    : SingleMachineSched_AlphaSched_AlphaSchedule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:10:39.700519+00:00
-- url     : https://prove2.me/theorems/2b97d448-4b88-4c66-80b0-6a27baa73e3e
-- title:
--   The $(\alpha_j)$-schedule and its completion times $C^{\alpha}_j$
-- statement:
--   Let $\boldsymbol\alpha = (\alpha_1, \dots, \alpha_n)$ with $0 < \alpha_j \le 1$, and let $t_j(\alpha_j)$ be the $\alpha_j$-point of job $j$ in the LP schedule. The **$(\alpha_j)$-schedule** processes the jobs nonpreemptively, each as early as possible, in nondecreasing order of their $\alpha_j$-points; ties are broken by job index. The **$\alpha$-schedule** is the special case $\alpha_1 = \cdots = \alpha_n = \alpha$.
--
--   Write $k \preceq j$ when $(t_k(\alpha_k), k)$ is lexicographically at most $(t_j(\alpha_j), j)$. Scheduling the jobs as early as possible in the order $\preceq$ gives job $j$ the completion time
--
--   $$C^{\boldsymbol\alpha}_j = \max_{k \preceq j} \Big( r_k + \sum_{i \,:\, k \preceq i \preceq j} p_i \Big),$$
--
--   the closed form of list scheduling: the machine last idles before the block of jobs that ends with $j$, and that block starts at the release date of its first job.
--
--   These completion times are what the paper's randomized algorithms output.
--
--   **Formalization Note** The completion time is defined directly by the closed form above, which equals the recursion $C_{\sigma(1)} = r_{\sigma(1)} + p_{\sigma(1)}$, $C_{\sigma(i)} = \max(C_{\sigma(i-1)}, r_{\sigma(i)}) + p_{\sigma(i)}$ along the order. For $\alpha_j \in (0, 1]$ two distinct jobs never have the same $\alpha_j$-point in the LP schedule, so the index tie-break never acts there.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 176 ($\alpha$-schedule) and p. 177 ($(\alpha_j)$-schedule)

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaSched_AlphaPoints

namespace SingleMachineSched.AlphaSched

/-- The order in which the `(α_j)`-schedule processes the jobs (p. 177): `k` comes no later than
`j` when `(t_k(α_k), k)` is lexicographically at most `(t_j(α_j), j)`, the `α`-points taken in the
LP schedule. The index only breaks ties of `α`-points. -/
def alphaOrder {n : ℕ} (p r : Fin n → ℕ) (α : Fin n → ℝ) (k j : Fin n) : Prop :=
  alphaPoint p (lpSet p r) k (α k) < alphaPoint p (lpSet p r) j (α j) ∨
    (alphaPoint p (lpSet p r) k (α k) = alphaPoint p (lpSet p r) j (α j) ∧ k ≤ j)

open Classical in
/-- The completion time `C^α_j` of job `j` in the `(α_j)`-schedule (p. 177): the jobs are
processed nonpreemptively, as early as possible, in the order `alphaOrder`. List scheduling in a
fixed order has the closed form
`C_j = max_{k ≼ j} (r_k + Σ_{i : k ≼ i ≼ j} p_i)`. -/
noncomputable def alphaCompletion {n : ℕ} (p r : Fin n → ℕ) (α : Fin n → ℝ) (j : Fin n) : ℝ :=
  (Finset.univ.filter (fun k => alphaOrder p r α k j)).sup'
    ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, Or.inr ⟨rfl, le_refl j⟩⟩⟩
    (fun k => (r k : ℝ) +
      ∑ i ∈ Finset.univ.filter (fun i => alphaOrder p r α k i ∧ alphaOrder p r α i j), (p i : ℝ))

end SingleMachineSched.AlphaSched


