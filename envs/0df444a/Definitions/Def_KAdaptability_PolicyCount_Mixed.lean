-- Prove2me | Definitions.Def_KAdaptability_PolicyCount_Mixed
-- name    : KAdaptability_PolicyCount_Mixed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:02:44.911482+00:00
-- url     : https://prove2.me/theorems/b72bc410-6e89-4087-ba54-d3eeccef2b6d
-- title:
--   The randomized-policy problems (EC.1)/(EC.2) and their optimal value
-- statement:
--   Write $\Delta_K=\{\lambda\in\mathbb R^K_+ : e^\top\lambda=1\}$ for the unit simplex in $\mathbb R^K$. The problem used in the proof of Theorem 1 with $K$ policies is
--
--   $$\begin{aligned}\text{minimize}\quad&\max_{\xi\in\Xi}\Big[\xi^\top Cx+\sum_{k\in\mathcal K}\lambda_k\cdot\xi^\top Qy^k\Big]\\ \text{subject to}\quad&x\in\mathcal X,\ y^k\in\mathcal Y,\ k\in\mathcal K,\ \lambda\in\Delta_K,\\ &Tx+Wy^k\le h\quad\forall k\in\mathcal K.\end{aligned}$$
--
--   It is problem (EC.1) of the paper for $K=|\mathcal Y|$ and problem (EC.2) for $K=\dim\mathcal Y+1$. Its **optimal value** is the infimum of the objective over all feasible $(x,y^1,\dots,y^K,\lambda)$, equal to $+\infty$ if there is none.
--
--   **Formalization Note** `objMixed K x ys lam` is the objective in `EReal`; `optMixed K` is the infimum over `FeasibleK K x ys` and `lam ∈ stdSimplex ℝ (Fin K)` (Mathlib's unit simplex). For $K=0$ the simplex is empty and the value is `⊤`.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec1 (PDF p. 35), problem (EC.1); p. ec2 (PDF p. 36), problem (EC.2)

import Mathlib
import Definitions.Def_KAdaptability_PolicyCount_POK

open Matrix

namespace KAdaptability.PolicyCount

variable {N M L nQ R : ℕ}

/-- The objective of problems (EC.1)/(EC.2) (pp. ec1–ec2) at `(x, y¹, …, y^K, λ)`:
`sup_{ξ∈Ξ} [ξ⊤Cx + Σ_{k} λ_k · ξ⊤Qy^k]`, in `EReal`. -/
noncomputable def Problem.objMixed (P : Problem N M L nQ R) (K : ℕ) (x : Fin N → ℝ)
    (ys : Fin K → Fin M → ℝ) (lam : Fin K → ℝ) : EReal :=
  ⨆ ξ ∈ P.Xi, (((ξ ⬝ᵥ (P.C *ᵥ x) + ∑ k, lam k * (ξ ⬝ᵥ (P.Q *ᵥ ys k)) : ℝ) : EReal))

/-- The optimal value of (EC.1) with `K` policies (and of (EC.2) when `K = D + 1`): the
infimum of `objMixed` over `x ∈ 𝒳`, `y^k ∈ 𝒴` with `Tx + Wy^k ≤ h` for all `k`, and `λ` in the
unit simplex `Δ_K = {λ ∈ ℝ^K_+ : e⊤λ = 1}` (`⊤` if there is no such decision). -/
noncomputable def Problem.optMixed (P : Problem N M L nQ R) (K : ℕ) : EReal :=
  ⨅ (x : Fin N → ℝ) (ys : Fin K → Fin M → ℝ) (_ : P.FeasibleK K x ys)
    (lam : Fin K → ℝ) (_ : lam ∈ stdSimplex ℝ (Fin K)), P.objMixed K x ys lam

end KAdaptability.PolicyCount


