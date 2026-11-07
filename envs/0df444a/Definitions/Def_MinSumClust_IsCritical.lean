-- Prove2me | Definitions.Def_MinSumClust_IsCritical
-- name    : MinSumClust_IsCritical
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:24.205516+00:00
-- url     : https://prove2.me/theorems/4dbf8ac2-5ff5-489f-bc2c-0f585b8a9747
-- title:
--   Definition 38: $\Gamma$-critical clusters
-- statement:
--   For a distance $d$, a vector $\alpha$ and a constant $\Gamma$, a cluster $C$ is **$\Gamma$-critical** if
--
--   $$\alpha_i>2\Gamma\, d(i,C)\qquad\text{for every } i\in C.$$
--
--   The paper applies it to the final dual solution $\alpha^*$ of Algorithm 3: by Observation 39 dual feasibility needs to be shown only for critical clusters (Lemma 47).
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Definition 38, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_MinSumClust_cost

namespace MinSumClust

/-- **Definition 38 (Γ-critical cluster)**, p.34.

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Definition 38, p.34 (PDF p.36).

A cluster `C` is Γ-critical (for the dual vector `α`) if `α_i > 2Γ · d(i, C)` for every `i ∈ C`.

**Formalization Note.** The paper states it for the final dual vector `α*` of Algorithm 3; the
definition takes the vector as a parameter, and the milestones apply it to `α*`. -/
def IsCritical {D : Type*} (d : D → D → ℝ) (α : D → ℝ) (Γ : ℝ) (C : Finset D) : Prop :=
  ∀ i ∈ C, 2 * Γ * dist1 d i C < α i

end MinSumClust


