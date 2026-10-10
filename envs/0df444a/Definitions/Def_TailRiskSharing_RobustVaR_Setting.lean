-- Prove2me | Definitions.Def_TailRiskSharing_RobustVaR_Setting
-- name    : TailRiskSharing_RobustVaR_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:57:34.651271+00:00
-- url     : https://prove2.me/theorems/9a1dd313-9626-4634-89bd-5996bbe2a9d9
-- title:
--   §2.1–2.3, §6, §8.2, pp. 5–7, 19, 28 — atomless P, F_X, left/right VaR, L^∞, allocations, comonotonic allocations (22), constrained inf-convolution (23)
-- statement:
--   This file fixes the probabilistic setting and the risk-sharing objects of Liu, Mao, Wang and Wei.
--
--   **Probability space.** $(\Omega,\mathcal F,\mathbb P)$ is a probability space. It is **atomless** if every measurable set $A$ with $\mathbb P(A)>0$ contains a measurable $B\subseteq A$ with $0<\mathbb P(B)<\mathbb P(A)$. A random variable $X:\Omega\to\mathbb R$ represents a loss, and its **distribution function** is $F_X(x)=\mathbb P(X\le x)$.
--
--   **Value-at-Risk.** For a level $\alpha$, the **left** and **right** Value-at-Risk are
--
--   $$
--   \mathrm{VaR}^L_\alpha(X)=\inf\{x\in\mathbb R: F_X(x)\ge 1-\alpha\},\qquad
--   \mathrm{VaR}^R_\alpha(X)=\inf\{x\in\mathbb R: F_X(x)> 1-\alpha\}.
--   $$
--
--   A small $\alpha$ corresponds to a far tail of the loss. For $\Lambda\in\{L,R\}$, $\mathrm{VaR}^\Lambda_\alpha$ denotes the corresponding version.
--
--   **Domain.** $\mathcal X=L^\infty$ is the set of measurable random variables that are bounded almost surely.
--
--   **Allocations.** For $X\in\mathcal X$ and $n$ agents, an **allocation** of $X$ is a tuple $(X_1,\dots,X_n)$ in $\mathcal X^n$ with $X_1+\dots+X_n=X$; the set of allocations is $\mathbb A_n(X)$. Two random variables $X,Y$ are **comonotonic**, written $X/\!\!/Y$, if there is $\Omega_0\in\mathcal F$ with $\mathbb P(\Omega_0)=1$ and $(X(\omega)-X(\omega'))(Y(\omega)-Y(\omega'))\ge0$ for all $\omega,\omega'\in\Omega_0$. The **comonotonic allocations** are
--
--   $$
--   \mathbb A^+_n(X)=\{(X_1,\dots,X_n)\in\mathbb A_n(X): X_i/\!\!/X,\ i=1,\dots,n\},
--   $$
--
--   and the **constrained inf-convolution** of risk measures $\rho_1,\dots,\rho_n$ is
--
--   $$
--   \mathop{\boxplus}_{i=1}^n\rho_i(X)=\inf\Big\{\sum_{i=1}^n\rho_i(X_i):(X_1,\dots,X_n)\in\mathbb A^+_n(X)\Big\}.
--   $$
--
--   A tuple in $\mathbb A^+_n(X)$ attaining this infimum is an **optimal constrained allocation**.
--
--   These are the objects of the comonotonic risk-sharing problem: agents split an aggregate loss $X$ into pieces that move in the same direction as $X$, and the constrained inf-convolution is the smallest total risk they can achieve.
--
--   **Formalization Note** The constraint $\sum_i X_i=X$ is imposed pointwise. The constrained inf-convolution takes values in `EReal`, so an empty or unbounded-below set of totals gives $+\infty$ or $-\infty$, never Lean's junk value $0$. $L^\infty$ is the set of measurable, almost surely bounded functions (no quotient). Atomlessness is stated in the splitting form, which is stronger than Mathlib's `NoAtoms`. `VaRS P Λ` selects $\mathrm{VaR}^L$ or $\mathrm{VaR}^R$ according to $\Lambda$.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), pp. 5–7, §2.1–2.3, (4); p. 19, §6, (22)–(23); p. 28, §8.2 (𝒳 = L^∞)

import Mathlib
import Definitions.Def_TailRiskSharing_ComonoConv_Comonotone
import Definitions.Def_TailRiskSharing_TailConv_Setting
import Definitions.Def_TailRiskSharing_VaRConv_Setting

namespace TailRiskSharing.RobustVaR

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- p. 19: an optimal constrained allocation of `X` for `(ρ₁, …, ρₙ)`. -/
def IsOptimalComonoAllocation (P : Measure Ω) (dom : Set (Ω → ℝ)) {n : ℕ}
    (ρ : Fin n → (Ω → ℝ) → ℝ) (X : Ω → ℝ) (Xs : Fin n → Ω → ℝ) : Prop :=
  Xs ∈ TailRiskSharing.ComonoConv.ComonoAllocations P dom n X ∧ ((∑ i, ρ i (Xs i) : ℝ) : EReal) = TailRiskSharing.ComonoConv.comonoInfConv P dom ρ X

end TailRiskSharing.RobustVaR


