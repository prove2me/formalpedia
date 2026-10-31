-- Prove2me | Definitions.Def_MWMSLagrange_Vlam
-- name    : MWMSLagrange_Vlam
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:06:00.158301+00:00
-- url     : https://prove2.me/theorems/4d0c1bb9-de2d-49f5-a404-06e9d1ab05de
-- title:
--   Lagrangian dual function $V^\lambda$
-- statement:
--   The value of the Lagrangian relaxation problem (3.3) is
--
--   $$V^\lambda=\inf_{\pi\ \text{relaxed}}\Big(\text{objective of (3.3) at }\pi\Big)\in[-\infty,\infty),$$
--
--   the infimum over policies without the warehouse constraint. For $\lambda\ge0$ it is a lower bound on $V^*$, and the multiplier $\lambda^*$ of SLaBS maximizes it over $\lambda\ge0$ (3.6).
--
--   **Formalization Note** Valued in `EReal`: $V^\lambda=-\infty$ when some $c_{i,j}-w_j+\lambda_j$ is negative enough that unbounded shipping pays. The maximizer is expressed as `IsMaxOn (Vlam I μ) {λ | 0 ≤ λ} λ*`.
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), (3.3), p.10; (3.6), p.12

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_RelaxedPolicy
import Definitions.Def_MWMSLagrange_relaxedCost

open MeasureTheory

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), (3.3), p.10: the value
`V^λ = min_{π} (3.3)` of the Lagrangian relaxation problem, the infimum of `relaxedCost λ`
over all relaxed (non-anticipating, uncapacitated) policies.

**Formalization Note.** `V^λ` takes values in `EReal`: it is `−∞` when some unit shipping cost
`c_{i,j} − w_j + λ_j` is so negative that shipping without bound pays (proof of Lemma 4,
p.34). The infimum ranges over a nonempty type (the zero policy), so it is never Lean's
default value. The maximizer `λ^*` of (3.6) is expressed in the theorems as
`IsMaxOn (Vlam I μ) {λ | 0 ≤ λ} λ^*`. -/
noncomputable def Vlam {M N T : ℕ} (I : Instance M N) (μ : Fin N → Fin T → Measure ℝ)
    (lam : Fin M → ℝ) : EReal :=
  ⨅ π : RelaxedPolicy I μ, ((relaxedCost I μ lam π.z : ℝ) : EReal)

end MWMSLagrange


