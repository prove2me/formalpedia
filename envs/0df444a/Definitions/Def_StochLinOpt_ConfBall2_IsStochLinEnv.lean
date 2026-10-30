-- Prove2me | Definitions.Def_StochLinOpt_ConfBall2_IsStochLinEnv
-- name    : StochLinOpt_ConfBall2_IsStochLinEnv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:50:18.286376+00:00
-- url     : https://prove2.me/theorems/dd8f3c25-ae07-4d6a-ab4c-9dc489a904b6
-- title:
--   Stochastic linear bandit model with bounded losses
-- statement:
--   Let $(\Omega,P)$ be a probability space, $D\subset\mathbb R^n$ a decision set and $\mu\in\mathbb R^n$ the unknown mean vector. Random losses $\ell_t$ and random decisions $x_t$ ($t\ge1$) follow the **stochastic linear model** if
--
--   1. $\mu^\top y\in[-1,1]$ for every $y\in D$;
--   2. each loss $\ell_t$ is measurable and takes values in $[-1,1]$;
--   3. each decision $x_t$ is $\mathcal H_t$-measurable, where $\mathcal H_t=\sigma(\ell_1,\dots,\ell_{t-1})$: the decision depends only on the history;
--   4. $\mathbb E(\ell_t\mid\mathcal H_t)=\mu^\top x_t$ almost surely.
--
--   Then the noise $\eta_t=\ell_t-\mu^\top x_t$ is a martingale difference sequence with respect to $(\mathcal H_t)$.
--
--   **Formalization Note** The paper assumes $\mathbb E(c_t(x)\mid\mathcal H_t)=\mu^\top x$ for the whole cost function $c_t$ and every $x\in D$; clause 4 is that assumption at the played decision, which is all the analysis uses. No independence and no sub-Gaussian assumption is made.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, §2, p. 3; §5.2, p. 8; proof of Lemma 13, p. 9

import Mathlib
import Definitions.Def_StochLinOpt_ConfBall2_lossHistory
open MeasureTheory
open Matrix

namespace StochLinOpt.ConfBall2

/-- **The stochastic linear bandit model** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, §2, p. 3: "Each such choice results in a
cost ℓt = ct(xt) ∈ [−1, 1]. We assume that, regardless of the history Ht, the conditional
expectation of ct is a fixed linear function, i.e., for all x ∈ D, E (ct(x) | Ht) = µ · x = µ†x ∈
[−1, 1]"; "the noise sequence, ηt = ct(xt) − µ · xt is a martingale difference sequence"; §5.2,
p. 8 for `H_t`; proof of Lemma 13, p. 9: "the history Ht fully determines x1, . . . , xt").

`IsStochLinEnv P μ D ℓ x` says, for random losses `ℓ t : Ω → ℝ` and random decisions
`x t : Ω → ℝⁿ` on a probability space `(Ω, P)`:
1. `μ ⬝ y ∈ [−1, 1]` for every `y ∈ D`;
2. every loss `ℓ t` (`t ≥ 1`) is measurable and takes values in `[−1, 1]`;
3. every decision `x t` (`t ≥ 1`) is `H_t`-measurable, `H_t = σ(ℓ_1, …, ℓ_{t−1})`;
4. `E(ℓ_t | H_t) = μ ⬝ x_t` almost surely for every `t ≥ 1`.

**Formalization Note** The model is stated at the level of the observed losses: the paper's
`E(c_t(x) | H_t) = μ ⬝ x` for all `x ∈ D` implies clause 4, because `x_t` is `H_t`-measurable.
No independence, no sub-Gaussian assumption and no bound on the noise beyond clause 2 is made.
Rounds are 1-based; index `0` is never constrained. -/
def IsStochLinEnv {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (μ : Fin n → ℝ) (D : Set (Fin n → ℝ)) (ℓ : ℕ → Ω → ℝ) (x : ℕ → Ω → Fin n → ℝ) : Prop :=
  (∀ y ∈ D, μ ⬝ᵥ y ∈ Set.Icc (-1 : ℝ) 1) ∧
  (∀ t, 1 ≤ t → Measurable (ℓ t)) ∧
  (∀ t, 1 ≤ t → ∀ ω, ℓ t ω ∈ Set.Icc (-1 : ℝ) 1) ∧
  (∀ t, 1 ≤ t → Measurable[lossHistory ℓ t] (x t)) ∧
  (∀ t, 1 ≤ t → P[ℓ t | lossHistory ℓ t] =ᵐ[P] fun ω => μ ⬝ᵥ x t ω)

end StochLinOpt.ConfBall2


