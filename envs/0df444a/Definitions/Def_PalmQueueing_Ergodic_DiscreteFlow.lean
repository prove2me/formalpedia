-- Prove2me | Definitions.Def_PalmQueueing_Ergodic_DiscreteFlow
-- name    : PalmQueueing_Ergodic_DiscreteFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T21:44:06.352483+00:00
-- url     : https://prove2.me/theorems/40cf26e7-4605-4049-a4e3-bf813562aa01
-- title:
--   Ergodic flows, additive and sub-additive sequences
-- statement:
--   The vocabulary §1.6's five quoted results are stated in.
--
--   A discrete flow $\theta$ is **ergodic** if all $\theta$-invariant events are of probability either
--   $0$ or $1$; equivalently, if all *strictly* invariant events are. Mathlib's `Ergodic` is reused
--   for this rather than redefined.
--
--   A sequence $\{g_n\}$, $n \ge 1$, is **additive** if for all $m, n \ge 1$,
--   $$ g_{m+n}(\omega) = g_m(\omega) + g_n(\theta^m(\omega)) \quad \text{a.s.} $$
--   The Birkhoff sums $g_n = \sum_{k=1}^{n} f(\theta^k\omega)$ of Theorem 1.6.1 are the motivating
--   example. The sequence $\{h_n\}$, $n \ge 1$, is **sub-additive** if
--   $$ h_{m+n}(\omega) \le h_m(\omega) + h_n(\theta^m(\omega)) \quad \text{a.s.} $$
--   "In fact, all sub-additive sequences that satisfy appropriate integrability conditions are such
--   that $\exists \lim_n \frac{1}{n}h_n = \bar h$ a.s., with $\bar h$ constant if $\theta$ is
--   ergodic" — which is Kingman's theorem.
--
--   The extremal characterisations (Theorems 1.6.3 and 1.6.5) are about the **absence** of a
--   decomposition $P = \alpha_1 Q_1 + \alpha_2 Q_2$ with $\alpha_1 + \alpha_2 = 1$, $\alpha_i > 0$,
--   into two *distinct* invariant probabilities; the continuous-time version requires $P_1$ and $P_2$
--   to be invariant under every $\theta_t$, not under one map.
--
--   **What Mathlib does not have**, verified on this workspace's checkout at the pinned revision: the
--   pointwise ergodic theorem (`Analysis/InnerProductSpace/MeanErgodic` is the *mean*, von Neumann,
--   $L^2$ theorem, not a.e. convergence) and Kingman's sub-additive ergodic theorem (no `Kingman`, no
--   sub-additive file under `Dynamics/`). The platform has neither.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, §1.6, pp. 46-50

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Ergodic flows, additive and sub-additive sequences (§1.6, pp.46-50)

§1.6 of Chapter 1 quotes five classical results of ergodic theory that the rest of the book uses.
This module is the vocabulary they are stated in.

Mathlib's `Ergodic` is reused for the discrete flow rather than redefined. What Mathlib does
**not** have, verified on this workspace's checkout at the pinned revision, is the pointwise
ergodic theorem — `Analysis/InnerProductSpace/MeanErgodic` is the *mean* (von Neumann, `L²`)
theorem, not a.e. convergence — nor Kingman's sub-additive ergodic theorem. Theorems 1.6.1, 1.6.2
and 1.6.4 are therefore genuinely absent substrate.
-/

namespace PalmQueueing.Ergodic

open MeasureTheory Filter Topology
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A sequence `{g_n}, n ≥ 1`, is **additive** with respect to a discrete flow `θ` (p.48):
`g_{m+n}(ω) = g_m(ω) + g_n(θ^m ω)` a.s. for all `m, n ≥ 1`.

The Birkhoff sums `g_n = Σ_{k=1}^{n} f(θ^k ω)` of Theorem 1.6.1 are the motivating example. -/
def IsAdditiveSeq (θ : Ω → Ω) (P0 : Measure Ω) (g : ℕ → Ω → ℝ) : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → ∀ᵐ ω ∂P0, g (m + n) ω = g m ω + g n (θ^[m] ω)

/-- A sequence `{h_n}, n ≥ 1`, is **sub-additive** (p.48):
`h_{m+n}(ω) ≤ h_m(ω) + h_n(θ^m ω)` a.s. for all `m, n ≥ 1`.

"In fact, all sub-additive sequences that satisfy appropriate integrability conditions are such
that `∃ lim_n (1/n) h_n = h̄` a.s., with `h̄` constant if `θ` is ergodic" — which is Kingman's
theorem, Theorem 1.6.2. -/
def IsSubAdditiveSeq (θ : Ω → Ω) (P0 : Measure Ω) (h : ℕ → Ω → ℝ) : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → ∀ᵐ ω ∂P0, h (m + n) ω ≤ h m ω + h n (θ^[m] ω)

/-- A **non-trivial convex decomposition** of a probability into two distinct invariant ones
(1.6.4): `P = α₁Q₁ + α₂Q₂` with `α₁ + α₂ = 1`, `α₁ > 0`, `α₂ > 0`, `Q₁` and `Q₂` invariant
probabilities and `Q₁ ≠ Q₂`.

Theorems 1.6.3 and 1.6.5 say that ergodicity is exactly the **non-existence** of such a
decomposition — the extremal characterisation. -/
def HasInvariantDecomposition (θ : Ω → Ω) (P : Measure Ω) : Prop :=
  ∃ (a₁ a₂ : ℝ) (Q₁ Q₂ : Measure Ω),
    IsProbabilityMeasure Q₁ ∧ IsProbabilityMeasure Q₂ ∧
    0 < a₁ ∧ 0 < a₂ ∧ a₁ + a₂ = 1 ∧ Q₁ ≠ Q₂ ∧
    Measure.map θ Q₁ = Q₁ ∧ Measure.map θ Q₂ = Q₂ ∧
    P = ENNReal.ofReal a₁ • Q₁ + ENNReal.ofReal a₂ • Q₂

/-- The continuous-time counterpart (1.6.6): a non-trivial convex decomposition of `P` into two
distinct probabilities invariant under **every** `θ_t`. -/
def HasFlowInvariantDecomposition (θ : Flow Ω) (P : Measure Ω) : Prop :=
  ∃ (b₁ b₂ : ℝ) (P₁ P₂ : Measure Ω),
    IsProbabilityMeasure P₁ ∧ IsProbabilityMeasure P₂ ∧
    0 < b₁ ∧ 0 < b₂ ∧ b₁ + b₂ = 1 ∧ P₁ ≠ P₂ ∧
    θ.Invariant P₁ ∧ θ.Invariant P₂ ∧
    P = ENNReal.ofReal b₁ • P₁ + ENNReal.ofReal b₂ • P₂

end PalmQueueing.Ergodic


