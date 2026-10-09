-- Prove2me | Definitions.Def_KAdaptability_PolicyCount_POK
-- name    : KAdaptability_PolicyCount_POK
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:02:04.447158+00:00
-- url     : https://prove2.me/theorems/860e4f67-ba4c-4035-8d32-ca9b5a2e62e7
-- title:
--   The K-adaptability problem 𝒫𝒪_K and its optimal value
-- statement:
--   Fix a number $K$ of second-stage policies and write $\mathcal K=\{1,\dots,K\}$. The **K-adaptability problem** $\mathcal{PO}_K$ associated with $\mathcal{PO}$ is
--
--   $$\begin{aligned}\text{minimize}\quad&\max_{\xi\in\Xi}\Big[\xi^\top Cx+\min_{k\in\mathcal K}\xi^\top Qy^k\Big]\\ \text{subject to}\quad&x\in\mathcal X,\ y^k\in\mathcal Y,\ k\in\mathcal K,\\ &Tx+Wy^k\le h\quad\forall k\in\mathcal K.\end{aligned}$$
--
--   Here the $K$ policies $y^1,\dots,y^K$ are fixed here-and-now together with $x$, and once $\xi$ is observed the cheapest of them is implemented. Every policy must satisfy the second-stage constraints; the policies need not be distinct. The **optimal value** of $\mathcal{PO}_K$ is the infimum of the objective over all feasible decisions $(x,y^1,\dots,y^K)$, equal to $+\infty$ if there is none.
--
--   This is the form $\mathcal{PO}_K$ of Observation 1 in the paper, the one Theorem 1 is about.
--
--   **Formalization Note** Policies are indexed by `Fin K` and given as a function `ys : Fin K → (Fin M → ℝ)`, not necessarily injective. `objPOK`, `optPOK` take values in `EReal`; for $K=0$ the minimum over the empty index set is `⊤`. `FeasibleK K x ys` is the constraint set above.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. 11, Observation 1, problem (PO_K); p. 8 (K = {1,…,K}, sup/inf reading)

import Mathlib
import Definitions.Def_KAdaptability_PolicyCount_Problem

open Matrix

namespace KAdaptability.PolicyCount

variable {N M L nQ R : ℕ}

/-- The objective of the K-adaptability problem 𝒫𝒪_K (Observation 1, p. 11) at a decision
`(x, y¹, …, y^K)`: `sup_{ξ∈Ξ} [ξ⊤Cx + min_{k∈𝒦} ξ⊤Qy^k]`, in `EReal`. The policies are indexed
by `Fin K` and need not be distinct. -/
noncomputable def Problem.objPOK (P : Problem N M L nQ R) (K : ℕ) (x : Fin N → ℝ)
    (ys : Fin K → Fin M → ℝ) : EReal :=
  ⨆ ξ ∈ P.Xi, (((ξ ⬝ᵥ (P.C *ᵥ x) : ℝ) : EReal) + ⨅ k, ((ξ ⬝ᵥ (P.Q *ᵥ ys k) : ℝ) : EReal))

/-- Feasibility in 𝒫𝒪_K: `x ∈ 𝒳`, and every policy satisfies `y^k ∈ 𝒴` and `Tx + Wy^k ≤ h`. -/
def Problem.FeasibleK (P : Problem N M L nQ R) (K : ℕ) (x : Fin N → ℝ)
    (ys : Fin K → Fin M → ℝ) : Prop :=
  x ∈ P.X ∧ ∀ k, ys k ∈ P.Y ∧ P.T *ᵥ x + P.W *ᵥ ys k ≤ P.h

/-- The optimal value of 𝒫𝒪_K: the infimum of `objPOK` over the feasible decisions
(`⊤` if there are none). -/
noncomputable def Problem.optPOK (P : Problem N M L nQ R) (K : ℕ) : EReal :=
  ⨅ (x : Fin N → ℝ) (ys : Fin K → Fin M → ℝ) (_ : P.FeasibleK K x ys), P.objPOK K x ys

end KAdaptability.PolicyCount


