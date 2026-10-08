-- Prove2me | Definitions.Def_WorstCaseCVaR_Discrete_Setting
-- name    : WorstCaseCVaR_Discrete_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:56.471612+00:00
-- url     : https://prove2.me/theorems/cf88b29c-2dc1-4452-8390-a31919d367e4
-- title:
--   §2.2 — the function $G_\beta(x,\alpha,\pi)$, $\mathrm{CVaR}_\beta(x,\pi)$ and $\mathrm{WCVaR}_\beta(x)$ for discrete distributions
-- statement:
--   Let $f(x,y)$ be the loss associated with a decision vector $x \in \mathbb R^n$ and a realisation $y \in \mathbb R^m$ of a random vector. Suppose $y$ takes finitely many values, the **scenarios** $y_{[1]}, \dots, y_{[S]} \in \mathbb R^m$, with probabilities $\Pr\{y_{[k]}\} = \pi_k$, where $\pi = (\pi_1,\dots,\pi_S)^T$ satisfies $\pi_k \ge 0$ and $\sum_{k=1}^S \pi_k = 1$. Fix a confidence level $\beta$ and write $[t]^+ = \max\{t, 0\}$.
--
--   1. The **Rockafellar–Uryasev function** for the discrete distribution $\pi$ is
--   $$G_\beta(x,\alpha,\pi) = \alpha + \frac{1}{1-\beta}\sum_{k=1}^S \pi_k\,[f(x,y_{[k]}) - \alpha]^+, \qquad \alpha \in \mathbb R.$$
--   2. The **conditional value-at-risk** of the loss at $x$ under $\pi$ is
--   $$\mathrm{CVaR}_\beta(x,\pi) = \min_{\alpha \in \mathbb R} G_\beta(x,\alpha,\pi).$$
--   3. For a set $\mathcal P_\pi \subseteq \mathbb R^S$ of probability vectors, the **worst-case CVaR** at $x$ is
--   $$\mathrm{WCVaR}_\beta(x) = \sup_{\pi \in \mathcal P_\pi} \mathrm{CVaR}_\beta(x,\pi) = \sup_{\pi\in\mathcal P_\pi}\min_{\alpha\in\mathbb R} G_\beta(x,\alpha,\pi).$$
--
--   These are the objects of the paper's discrete-distribution model (§2.2): the worst-case CVaR is the risk of the decision $x$ when the scenario probabilities are only known to lie in the ambiguity set $\mathcal P_\pi$, and Theorem 2 rewrites it as a min–max of $G_\beta$.
--
--   **Formalization Note** Scenarios are indexed zero-based, `ys : Fin S → (Fin m → ℝ)`, and probability vectors are elements of `Fin S → ℝ`. $\mathrm{CVaR}_\beta(x,\pi)$ is the real infimum `sInf` of the values of $G_\beta(x,\cdot,\pi)$; for $\pi$ a probability vector and $0<\beta<1$ these values are bounded below (by the mean loss) and the infimum is attained, so it is the paper's minimum. $\mathrm{WCVaR}_\beta(x)$ is the real supremum `sSup` of the image of $\mathcal P_\pi$ under $\pi \mapsto \mathrm{CVaR}_\beta(x,\pi)$; it is the true supremum when $\mathcal P_\pi$ is a nonempty set of probability vectors and $0<\beta<1$, hypotheses that every theorem using these objects carries. The definitions are total: on other inputs the real `sInf`/`sSup` return junk values that no statement of the mission uses.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1158, §2.2 (definition of G_β); p. 1159, definitions of CVaR_β(x, π) and WCVaR_β(x)

import Mathlib

namespace WorstCaseCVaR.Discrete

/-- The function `G_β(x, α, π)` of Zhu & Fukushima (2009), §2.2, p. 1158: for the loss
`f(x, y)`, the scenarios `y_[1], …, y_[S]` (here `ys 0, …, ys (S-1)`, zero-based), a confidence
level `β`, a decision `x`, a threshold `α` and a probability vector `π`,
`G_β(x, α, π) = α + 1/(1 − β) ∑_{k=1}^S π_k [f(x, y_[k]) − α]⁺`, where `[t]⁺ = max{t, 0}`. -/
noncomputable def G {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (ys : Fin S → Fin m → ℝ)
    (β : ℝ) (x : Fin n → ℝ) (α : ℝ) (π : Fin S → ℝ) : ℝ :=
  α + (1 - β)⁻¹ * ∑ k, π k * max (f x (ys k) - α) 0

/-- `CVaR_β(x, π) ≜ min_{α ∈ ℝ} G_β(x, α, π)` (p. 1159), written as the infimum of the values of
`G_β(x, ·, π)`. For `π` a probability vector and `0 < β < 1` the set of values is bounded below and the
infimum is attained, so this real infimum is the paper's minimum. -/
noncomputable def cvar {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (ys : Fin S → Fin m → ℝ)
    (β : ℝ) (x : Fin n → ℝ) (π : Fin S → ℝ) : ℝ :=
  sInf (Set.range (fun α : ℝ => G f ys β x α π))

/-- The worst-case CVaR with respect to a set `P` (the paper's `𝒫_π`) of probability vectors (p. 1159):
`WCVaR_β(x) ≜ sup_{π ∈ 𝒫_π} CVaR_β(x, π)`, the real supremum of the image of `P` under
`π ↦ CVaR_β(x, π)`. It is the true supremum when `P` is a nonempty set of probability vectors
and `0 < β < 1` (the image is then nonempty and bounded above). -/
noncomputable def wcvar {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (ys : Fin S → Fin m → ℝ)
    (β : ℝ) (x : Fin n → ℝ) (P : Set (Fin S → ℝ)) : ℝ :=
  sSup ((fun π => cvar f ys β x π) '' P)

end WorstCaseCVaR.Discrete


