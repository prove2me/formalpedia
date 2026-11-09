-- Prove2me | Definitions.Def_MinSumFPT_IsCovered
-- name    : MinSumFPT_IsCovered
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:57.261616+00:00
-- url     : https://prove2.me/theorems/173eca7d-3ed6-4a36-925e-e84c19aa9e1d
-- title:
--   Definition 1: $(\varepsilon,\alpha)$-approximate centers and covered clusters
-- statement:
--   Let $M\subseteq A$, let $C$ be a cluster, and let $\Lambda$ be a real number (the paper's $\mathrm{OPT}$). A point $p$ is an **$(\varepsilon,\alpha)$-approximate center** of $C$ if
--
--   $$
--   |C|\cdot\sum_{x\in C}\|e_x-e_p\|_{W_1}\ \le\ \frac{\varepsilon}{4\alpha}\cdot\frac{\Lambda}{k}+\alpha\cdot\mathrm{cost}(C), \tag{1}
--   $$
--
--   and $C$ is **$(\varepsilon,\alpha)$-covered** by $M$ if some $p\in M$ is an $(\varepsilon,\alpha)$-approximate center of $C$.
--
--   Stage 1 of the algorithm produces candidate sets that cover every cluster; the covering points serve as approximate cluster centers in the later stages.
--
--   **Formalization Note** The value written $\mathrm{OPT}$ in (1) is a parameter. Claim 4, Hypothesis 1 and §§2.4–2.5 use the optimum of the instance. In §2.3, where the target clustering is arbitrary, the milestones use the target's cost or an upper bound on it.
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Definition 1, Eq. (1), p.9

import Mathlib
import Definitions.Def_MinSumClust_cost
import Definitions.Def_MinSumFPT_Delta

namespace MinSumFPT

/-!
# Definition 1: (ε, α)-approximate centers and (ε, α)-covered clusters

Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation
Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256
12e81235…), Definition 1, Eq. (1), p.9: a cluster C is (ε, α)-covered by M if some p ∈ M has
|C| ⋅ ∑_{x∈C} ‖e_x − e_p‖_{W₁} ≤ (ε/(4α)) ⋅ OPT/k + α ⋅ cost(C); such p is an (ε, α)-approximate
center of C.

This module bundles `IsApproxCenter` and `IsCovered`.

**Formalization Note.** The value written OPT in (1) is the parameter `Λ`. Where the paper's OPT is
the optimum of the instance (Claim 4, Theorem 5, Hypothesis 1, §§2.4–2.5) the statements put
`Λ := optCost d k`; in Lemmas 10 and 11 (§2.3, where the target clustering is arbitrary) the
statements take `Λ` to be any upper bound on the target's cost, see their milestones. -/

/-- `p` is an (ε, α)-approximate center of `C` (Eq. (1) with `OPT := Λ`). -/
def IsApproxCenter {n : ℕ} (d : Fin n → Fin n → ℝ) (Λ : ℝ) (k : ℕ) (ε α : ℝ)
    (C : Finset (Fin n)) (p : Fin n) : Prop :=
  (C.card : ℝ) * ∑ x ∈ C, PerturbedWF.transNorm d (unitVec x - unitVec p) ≤
    ε / (4 * α) * (Λ / k) + α * MinSumClust.cost d C

/-- The cluster `C` is (ε, α)-covered by the point set `M` (Definition 1 with `OPT := Λ`). -/
def IsCovered {n : ℕ} (d : Fin n → Fin n → ℝ) (Λ : ℝ) (k : ℕ) (ε α : ℝ) (M C : Finset (Fin n)) :
    Prop :=
  ∃ p ∈ M, IsApproxCenter d Λ k ε α C p

end MinSumFPT


