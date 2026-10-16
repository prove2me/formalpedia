-- Prove2me | Definitions.Def_NeedPersuasion_FullInfo_Constants
-- name    : NeedPersuasion_FullInfo_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T01:04:55.299695+00:00
-- url     : https://prove2.me/theorems/e9b43cb9-153e-4839-8b91-60b8fb264bb3
-- title:
--   Proposition 3, p. 18, and its proof, p. 41 — the lower bound on Λ̄_L(λ_H), the gain factors β_{L,sm}, β_{H,sm} and the function f(λ_L, λ_H)
-- statement:
--   This file defines the explicit constants of Proposition 3 and the polynomial $f$ of its proof, for the model of `NeedPersuasion.FullInfo.Model`.
--
--   1. For a utility sequence $u_L$, $m_{fi}(u_L)$ is the smallest $k$ with $u_L(k)<0$; for a model it agrees with $m_{fi}$.
--   2. The **lower bound** on the threshold $\bar\Lambda_L(\lambda_H)$, depending on $\lambda_H$ and $u_L$ only:
--   $$\underline{\Lambda}(\lambda_H,u_L)=(1-\lambda_H)\,\frac{u_L(m_{fi}-1)}{u_L(0)-\sum_{k=1}^{m_{fi}-1}\lambda_H^k\,\big(u_L(k-1)-u_L(k)\big)}.$$
--   3. The **gain factors** of Proposition 3(2):
--   $$\beta_{L,sm}=1+\frac{\lambda_H(1-\lambda)\lambda_L\lambda^{m_{fi}-1}}{1-\lambda_H-\lambda_L\lambda^{m_{fi}-1}},\qquad \beta_{H,sm}=1+\frac{(1-\lambda_H)(1-\lambda)\lambda_L\lambda^{m_{fi}-1}}{1-\lambda_H-\lambda_L\lambda^{m_{fi}-1}}.$$
--   4. The function of the proof of Proposition 3:
--   $$f(\lambda_L,\lambda_H)=\lambda_Lu_L(0)-\lambda_L\sum_{k=1}^{m_{fi}-1}(\lambda_H+\lambda_L)^k\big(u_L(k-1)-u_L(k)\big)-(1-\lambda_H)u_L(m_{fi}-1).$$
--
--   The sign of $f$ decides whether the full-information mechanism is Pareto-efficient, and the three constants are the quantitative content of Proposition 3.
--
--   **Formalization Note** The sums over $k=1,\dots,m_{fi}-1$ are finite sums over `Finset.Ico 1 m_fi`; under the standing assumptions $m_{fi}\ge1$ (because $u_L(0)>0$), so $m_{fi}-1$ is a natural-number subtraction without truncation. The divisions are real divisions; the statements that use them carry hypotheses under which the denominators are positive.
-- source:
--   arXiv:2005.07253v3, Proposition 3(1)–(2), p. 18; App. C, proof of Proposition 3, p. 41

import Mathlib
import Definitions.Def_NeedPersuasion_FullInfo_Model

namespace NeedPersuasion.FullInfo

/-- The full-information threshold of a utility sequence `u_L` alone: the smallest `k` with
`u_L(k) < 0` (p. 12). For a model `M`, `mfi M = mfiOf M.uL` by definition. -/
noncomputable def mfiOf (uL : ℕ → ℝ) : ℕ := sInf {k | uL k < 0}

theorem mfi_eq_mfiOf (M : Model) : mfi M = mfiOf M.uL := rfl

/-- The lower bound on `Λ̄_L(λ_H)` of Proposition 3(1), p. 18:
`(1 − λ_H) · u_L(m_fi − 1) / (u_L(0) − ∑_{k=1}^{m_fi−1} λ_H^k (u_L(k−1) − u_L(k)))`.
It depends on `λ_H` and `u_L` only. -/
noncomputable def lowerBound (lamH : ℝ) (uL : ℕ → ℝ) : ℝ :=
  (1 - lamH) * (uL (mfiOf uL - 1) /
    (uL 0 - ∑ k ∈ Finset.Ico 1 (mfiOf uL), lamH ^ k * (uL (k - 1) - uL k)))

/-- `β_{L,sm} = 1 + λ_H(1−λ)λ_L λ^{m_fi−1} / (1 − λ_H − λ_L λ^{m_fi−1})`, Proposition 3(2), p. 18. -/
noncomputable def betaL (M : Model) : ℝ :=
  1 + M.lamH * (1 - M.lam) * M.lamL * M.lam ^ (mfi M - 1) /
    (1 - M.lamH - M.lamL * M.lam ^ (mfi M - 1))

/-- `β_{H,sm} = 1 + (1−λ_H)(1−λ)λ_L λ^{m_fi−1} / (1 − λ_H − λ_L λ^{m_fi−1})`,
Proposition 3(2), p. 18. -/
noncomputable def betaH (M : Model) : ℝ :=
  1 + (1 - M.lamH) * (1 - M.lam) * M.lamL * M.lam ^ (mfi M - 1) /
    (1 - M.lamH - M.lamL * M.lam ^ (mfi M - 1))

/-- `f(λ_L, λ_H) = λ_L u_L(0) − λ_L ∑_{k=1}^{m_fi−1} (λ_H + λ_L)^k (u_L(k−1) − u_L(k))
− (1 − λ_H) u_L(m_fi − 1)` (App. C, proof of Proposition 3, p. 41). -/
noncomputable def fF (M : Model) : ℝ :=
  M.lamL * M.uL 0 -
    M.lamL * ∑ k ∈ Finset.Ico 1 (mfi M), (M.lamH + M.lamL) ^ k * (M.uL (k - 1) - M.uL k) -
    (1 - M.lamH) * M.uL (mfi M - 1)

end NeedPersuasion.FullInfo


