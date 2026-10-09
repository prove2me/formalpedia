-- Prove2me | Definitions.Def_KAdaptability_ConstrGap_Values
-- name    : KAdaptability_ConstrGap_Values
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:00:24.470767+00:00
-- url     : https://prove2.me/theorems/e1c40cae-6102-4b5b-98de-c62f90cf0442
-- title:
--   Objective and optimal values of 𝒫 and of its K-adaptability problem 𝒫_K
-- statement:
--   Fix data of the two-stage robust binary program as in `KAdaptability.ConstrGap.Problem`. For a first-stage decision $x$ and a parameter $\xi$, the **second-stage value** is
--   $$\phi(x,\xi)=\inf_{y\in\mathcal Y}\{\xi^\top Qy : Tx+Wy\le H\xi\},$$
--   which is $+\infty$ when no $y\in\mathcal Y$ satisfies the second-stage constraints. The **two-stage robust binary program** $\mathcal P$ (p. 6) has objective and optimal value
--   $$f(x)=\sup_{\xi\in\Xi}\big[\xi^\top Cx+\phi(x,\xi)\big],\qquad \operatorname{opt}(\mathcal P)=\inf_{x\in\mathcal X}f(x).$$
--
--   For $K\in\mathbb N$ and $\mathcal K=\{1,\dots,K\}$, the **K-adaptability problem** $\mathcal P_K$ (p. 8) chooses $x\in\mathcal X$ and $K$ second-stage policies $y^1,\dots,y^K\in\mathcal Y$ here-and-now; once $\xi$ is observed, the best feasible policy is implemented:
--   $$f_K(x,y^1,\dots,y^K)=\sup_{\xi\in\Xi}\Big[\xi^\top Cx+\inf_{k\in\mathcal K}\{\xi^\top Qy^k : Tx+Wy^k\le H\xi\}\Big],$$
--   $$\operatorname{opt}(\mathcal P_K)=\inf\{f_K(x,y^1,\dots,y^K) : x\in\mathcal X,\ y^k\in\mathcal Y,\ k\in\mathcal K\}.$$
--
--   As on p. 8, if all policies are infeasible for some $\xi\in\Xi$, the inner minimum is an infimum over the empty set and the objective is $+\infty$. An infeasible problem has optimal value $+\infty$.
--
--   **Formalization Note** All values live in the extended reals `EReal`; max and min are read as sup and inf (the paper's Notation, p. 10), so an empty infimum is $\top=+\infty$. The left summand is always a real number and the inner infimum is a real number or $+\infty$, so no expression of the form $-\infty+\infty$ arises. The policies are a family indexed by `Fin K` and may repeat; $K=0$ is allowed (then the objective is $+\infty$ since $\Xi\neq\emptyset$).
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. 6, problem (P); p. 8, problem (P_K) and the +∞ convention; p. 10, Notation (max/min as sup/inf)

import Mathlib
import Definitions.Def_KAdaptability_ConstrGap_Problem

open Matrix

namespace KAdaptability.ConstrGap

variable {N M L nQ R : ℕ}

/-- The second-stage value of 𝒫 at `(x, ξ)`: `inf_{y∈𝒴} {ξ⊤Qy : Tx + Wy ≤ Hξ}` in `EReal`;
it is `⊤ = +∞` when no `y ∈ 𝒴` satisfies the second-stage constraints. -/
noncomputable def Problem.recourse (P : Problem N M L nQ R) (x : Fin N → ℝ)
    (ξ : Fin nQ → ℝ) : EReal :=
  ⨅ y ∈ P.Y, ⨅ (_ : P.T *ᵥ x + P.W *ᵥ y ≤ P.H *ᵥ ξ), ((ξ ⬝ᵥ (P.Q *ᵥ y) : ℝ) : EReal)

/-- The objective of 𝒫 (p. 6) at a first-stage decision `x`:
`sup_{ξ∈Ξ} [ξ⊤Cx + inf_{y∈𝒴} {ξ⊤Qy : Tx + Wy ≤ Hξ}]`, in `EReal`. -/
noncomputable def Problem.objP (P : Problem N M L nQ R) (x : Fin N → ℝ) : EReal :=
  ⨆ ξ ∈ P.Xi, (((ξ ⬝ᵥ (P.C *ᵥ x) : ℝ) : EReal) + P.recourse x ξ)

/-- The optimal value of the two-stage robust binary program 𝒫: `inf_{x∈𝒳} objP x`
(`⊤` if `𝒳 = ∅`). -/
noncomputable def Problem.optP (P : Problem N M L nQ R) : EReal :=
  ⨅ x ∈ P.X, P.objP x

/-- The objective of the K-adaptability problem 𝒫_K (p. 8) at a decision `(x, y¹, …, y^K)`:
`sup_{ξ∈Ξ} [ξ⊤Cx + inf_{k∈𝒦} {ξ⊤Qy^k : Tx + Wy^k ≤ Hξ}]`, in `EReal`. If all policies are
infeasible for some `ξ ∈ Ξ`, the inner infimum is over the empty set and equals `⊤ = +∞`, so the
objective is `+∞` (the convention of p. 8). Policies are indexed by `Fin K` and may repeat. -/
noncomputable def Problem.objPK (P : Problem N M L nQ R) (K : ℕ) (x : Fin N → ℝ)
    (ys : Fin K → Fin M → ℝ) : EReal :=
  ⨆ ξ ∈ P.Xi, (((ξ ⬝ᵥ (P.C *ᵥ x) : ℝ) : EReal) +
    ⨅ k, ⨅ (_ : P.T *ᵥ x + P.W *ᵥ ys k ≤ P.H *ᵥ ξ), ((ξ ⬝ᵥ (P.Q *ᵥ ys k) : ℝ) : EReal))

/-- The optimal value of the K-adaptability problem 𝒫_K: the infimum of `objPK` over
`x ∈ 𝒳` and `y¹, …, y^K ∈ 𝒴` (`⊤` if there is no such decision). -/
noncomputable def Problem.optPK (P : Problem N M L nQ R) (K : ℕ) : EReal :=
  ⨅ x ∈ P.X, ⨅ (ys : Fin K → Fin M → ℝ) (_ : ∀ k, ys k ∈ P.Y), P.objPK K x ys

end KAdaptability.ConstrGap


