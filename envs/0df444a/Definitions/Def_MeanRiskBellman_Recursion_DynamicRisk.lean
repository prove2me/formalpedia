-- Prove2me | Definitions.Def_MeanRiskBellman_Recursion_DynamicRisk
-- name    : MeanRiskBellman_Recursion_DynamicRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:50.284892+00:00
-- url     : https://prove2.me/theorems/7c0999be-ffd1-4b36-9345-b52d32fe42f6
-- title:
--   §2.1–§2.2, pp. 4–6 — finite filtered probability space, dynamic convex risk measure (Definition 1), time consistency
-- statement:
--   This file fixes the probabilistic setting and the notion of a time consistent dynamic convex risk measure used throughout.
--
--   **Finite filtered probability space** (§2.1). On the finite horizon $\mathbb T=\{0,1,\dots,T\}$ let $(\Omega,\mathcal F,(\mathcal F_t)_{t\in\mathbb T},\mathbb P)$ be a filtered probability space with $\Omega$ finite, $\mathcal F_0$ trivial ($\mathcal F_0=\{\emptyset,\Omega\}$) and $\mathcal F_T=\mathcal F$, in which every nonempty event has positive probability:
--   $$\mathbb P(A)>0\quad\text{for all } A\in\mathcal F,\ A\neq\emptyset .$$
--   $L_t$ denotes the $\mathcal F_t$-measurable real random variables (automatically bounded on a finite space).
--
--   **Dynamic convex risk measure** (Definition 1). A family $(\rho_t)_{t\in\mathbb T}$ with $\rho_t:L_T\to L_t$ such that each $\rho_t$ satisfies $\rho_t(\mathbf 0)=0$ and, for $X,Y\in L_T$ and $\Lambda\in L_t$,
--   1. conditional translation invariance: $\rho_t(X+\Lambda)=\rho_t(X)-\Lambda$;
--   2. monotonicity: $X\le Y\Rightarrow \rho_t(X)\ge\rho_t(Y)$;
--   3. conditional convexity: $\rho_t(\Lambda X+(1-\Lambda)Y)\le\Lambda\rho_t(X)+(1-\Lambda)\rho_t(Y)$ for $0\le\Lambda\le1$.
--
--   **Time consistency** (p. 6). The family is time consistent if for all $X,Y\in L_T$ and $0\le t\le T-1$,
--   $$\rho_{t+1}(X)=\rho_{t+1}(Y)\ \Longrightarrow\ \rho_t(X)=\rho_t(Y).$$
--
--   These are the standing assumptions on the probability space and the risk measure of the mean-risk problem; Lemma 2.1 and every result of §5 rely on them.
--
--   **Formalization Note.** Each $\rho_t$ is required to be a conditional convex risk measure w.r.t. $\mathcal F_t$ in the sense of the published definition `CondConvexRisk.Representation.IsCondConvexRiskMeasure` (axioms $\mathbb P$-a.s. on $L^\infty$, which on a finite space is every measurable function). Random variables are functions $\Omega\to\mathbb R$, $\rho_t$ acts on functions, and time consistency is stated with pointwise equalities for $\mathcal F$-measurable $X, Y$: with positive probabilities, a.s. equality of measurable functions is equality everywhere. Values of $\rho_t$ on non-measurable functions and for $t>T$ are unconstrained and never used.
-- source:
--   Kováčová & Rudloff, Time consistency of the mean-risk problem, arXiv:1806.10981v2, pp. 4–6, §2.1, §2.2, Definition 1 and the definition of time consistency (p. 6)

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_CondConvexRiskMeasure

namespace MeanRiskBellman.Recursion

open MeasureTheory

/-- §2.1, p. 4: the standing assumptions on the probability space.  `(Ω, F, (F_t)_{t ∈ 𝕋}, P)` is a
finite filtered probability space on the horizon `𝕋 = {0, …, T}` (`F` is the ambient σ-algebra), with
`F_0` trivial and `F_T = F`, and every nonempty event has positive probability. -/
structure IsFinFilteredSpace {Ω : Type*} [Fintype Ω] [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (T : ℕ) (ℱ : Filtration ℕ mΩ) : Prop where
  /-- `P` is a probability measure. -/
  isProb : IsProbabilityMeasure P
  /-- `P(A) > 0` for every nonempty `A ∈ F`. -/
  pos : ∀ A : Set Ω, MeasurableSet A → A.Nonempty → 0 < P A
  /-- `F_T = F`. -/
  terminal : ℱ T = mΩ
  /-- `F_0` is trivial. -/
  initial : ℱ 0 = ⊥

/-- Definition 1, p. 5: a dynamic convex risk measure `(ρ_t)_{t ∈ 𝕋}`: every `ρ_t : L_T → L_t`
(`t = 0, …, T`) is a conditional convex risk measure with respect to `F_t` (normalization, conditional
translation invariance, monotonicity, conditional convexity), encoded by the published
`IsCondConvexRiskMeasure (ℱ t) P (ρ t)`. -/
structure IsDynamicConvexRiskMeasure {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (T : ℕ) (ℱ : Filtration ℕ mΩ) (ρ : ℕ → (Ω → ℝ) → Ω → ℝ) : Prop where
  /-- each `ρ_t`, `t ≤ T`, is a conditional convex risk measure w.r.t. `F_t`. -/
  risk : ∀ t ≤ T, CondConvexRisk.Representation.IsCondConvexRiskMeasure (ℱ t) P (ρ t)

/-- p. 6: a dynamic risk measure is time consistent if for any `X, Y ∈ L_T` and `0 ≤ t ≤ T - 1`,
`ρ_{t+1}(X) = ρ_{t+1}(Y)` implies `ρ_t(X) = ρ_t(Y)`.  `L_T` is the space of `F`-measurable random
variables (`F_T = F`); equalities are pointwise (on a finite space with positive probabilities
a.s. equality of measurable functions is equality). -/
def TimeConsistent {Ω : Type*} [MeasurableSpace Ω] (T : ℕ) (ρ : ℕ → (Ω → ℝ) → Ω → ℝ) : Prop :=
  ∀ t < T, ∀ X Y : Ω → ℝ, Measurable X → Measurable Y → ρ (t + 1) X = ρ (t + 1) Y → ρ t X = ρ t Y

end MeanRiskBellman.Recursion


