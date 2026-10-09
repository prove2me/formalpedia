-- Prove2me | Definitions.Def_KAdaptability_PolicyCount_PO
-- name    : KAdaptability_PolicyCount_PO
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:02:04.560386+00:00
-- url     : https://prove2.me/theorems/b9e2b8ae-7b78-4484-ab25-98e3e784c1b7
-- title:
--   The two-stage robust binary program 𝒫𝒪 with objective uncertainty and its optimal value
-- statement:
--   Given the data of a two-stage robust binary program with objective uncertainty, the **two-stage robust binary program** $\mathcal{PO}$ is
--
--   $$\text{minimize}\quad \max_{\xi\in\Xi}\Big[\xi^\top Cx+\min_{y\in\mathcal Y}\{\xi^\top Qy : Tx+Wy\le h\}\Big]\quad\text{subject to}\quad x\in\mathcal X.$$
--
--   The first-stage decision $x$ is taken before $\xi$ is revealed; the second-stage decision $y$ is chosen after $\xi$ is observed, among the binary vectors of $\mathcal Y$ satisfying the deterministic constraints $Tx+Wy\le h$. Following the paper's convention, maxima and minima are suprema and infima: if no $y\in\mathcal Y$ satisfies $Tx+Wy\le h$, the inner minimum is $+\infty$, and so is the objective at $x$. The **optimal value** of $\mathcal{PO}$ is the infimum of the objective over $x\in\mathcal X$, equal to $+\infty$ when $\mathcal X$ is empty.
--
--   **Formalization Note** The objective `objPO x` and the optimal value `optPO` take values in the extended reals `EReal`, as `⨆ ξ ∈ Ξ` of the real number $\xi^\top Cx$ plus `⨅` over the feasible $y\in\mathcal Y$; an empty infimum is `⊤`.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. 10, problem (PO); sup/inf convention: p. 10, Notation

import Mathlib
import Definitions.Def_KAdaptability_PolicyCount_Problem

open Matrix

namespace KAdaptability.PolicyCount

variable {N M L nQ R : ℕ}

/-- The objective of 𝒫𝒪 (p. 10) at a first-stage decision `x`:
`sup_{ξ∈Ξ} [ξ⊤Cx + inf_{y∈𝒴} {ξ⊤Qy : Tx + Wy ≤ h}]`, in `EReal`.
The inner infimum over an empty set of feasible `y` is `⊤ = +∞`. -/
noncomputable def Problem.objPO (P : Problem N M L nQ R) (x : Fin N → ℝ) : EReal :=
  ⨆ ξ ∈ P.Xi, (((ξ ⬝ᵥ (P.C *ᵥ x) : ℝ) : EReal) +
    ⨅ y ∈ P.Y, ⨅ (_ : P.T *ᵥ x + P.W *ᵥ y ≤ P.h), ((ξ ⬝ᵥ (P.Q *ᵥ y) : ℝ) : EReal))

/-- The optimal value of 𝒫𝒪: the infimum of `objPO` over `x ∈ 𝒳` (`⊤` if `𝒳 = ∅`). -/
noncomputable def Problem.optPO (P : Problem N M L nQ R) : EReal :=
  ⨅ x ∈ P.X, P.objPO x

end KAdaptability.PolicyCount


