-- Prove2me | Definitions.Def_FairReplay_optRounds
-- name    : FairReplay_optRounds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:49:30.655008+00:00
-- url     : https://prove2.me/theorems/437c2c63-b4ff-45d8-b88e-b0223452552f
-- title:
--   Optimal null expected rounds $Q(d,\delta)$; $Q_{\mathrm{edge}}$, $Q_{\mathrm{vertex}}$
-- statement:
--   For a null $\nu_0$, an alternative $\nu_1$ and a level $\delta$, the **optimal null expected number of rounds** is
--
--   $$
--   Q(\delta;\nu_0,\nu_1)=\inf\bigl\{\mathbb E_{\nu_0}[\tau]:\ (\pi,\tau,\psi)\ \text{a }\delta\text{-correct tester}\bigr\}\in[0,\infty],
--   $$
--
--   the infimum over every adaptive, possibly randomized policy, every stopping time of the transcript filtration and every decision measurable for the stopped σ-algebra. Specializing to the one-edge family,
--
--   1. $Q_{\mathrm{edge}}(d,\delta)$ is $Q$ for the four-way replay model, and
--   2. $Q_{\mathrm{vertex}}(d,\delta)$ is $Q$ for the vertex-paired replay model,
--
--   each for the null $(p+s,p+s)$ against the alternative $(p+s+d,p+s)$.
--
--   **Formalization Note** The paper writes $Q_{\mathrm{edge}}$, $Q_{\mathrm{vertex}}$ in (37) without a displayed definition; its own usage ("the optimal expected null declared cost", Thm 10.9(vi), p.20; "the minimax null-expected round complexity", Prop. 10.10, p.23) fixes this reading. The infimum is $\infty$ when no $\delta$-correct tester exists.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.4, eq. (37), p.14 (PDF p.16); Theorem 10.9(vi), p.20; Proposition 10.10, p.23

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_FairReplay_IsDeltaCorrect
import Definitions.Def_FairReplay_expectedRounds
import Definitions.Def_FairReplay_fourWayModel
import Definitions.Def_FairReplay_vertexModel

open MeasureTheory

namespace FairReplay

/-- **Optimal null expected number of rounds** (Sah, Zhang, Lian, *Testing Fairness of Evolving
Software under Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03, sha256 e23940a0…,
Theorem 10.4, eq. (37), p.14 (PDF p.16); the paper's usage in Theorem 10.9(vi), p.20, "the optimal
expected null declared cost", and Proposition 10.10, p.23, "the minimax null-expected round
complexity").

`optRounds δ ν₀ ν₁` is the infimum of the null expected stopping time `E_{ν₀}[T]` over all
δ-correct testers `(π, τ, ψ)` for `ν₀` against `ν₁`: every adaptive, possibly randomized policy
`π`, every stopping time `τ` of the transcript filtration and every decision `ψ` measurable with
respect to the stopped σ-algebra.

**Formalization Note** The infimum is taken in `[0, ∞]` (it is `∞` when no δ-correct tester
exists). The paper writes `Q_edge(d, δ)` and `Q_vertex(d, δ)` without a displayed definition; this
is the reading under which its "Consequently" follows from the bounds (i)–(ii). -/
noncomputable def optRounds {k : ℕ} (δ : ℝ) (ν₀ ν₁ : BanditAlgorithm.StochasticBandit k) :
    ENNReal :=
  ⨅ (π : BanditAlgorithm.BanditPolicy k) (τ : (ℕ → Fin k × ℝ) → ℕ∞)
    (ψ : (ℕ → Fin k × ℝ) → Bool) (hτ : BanditAlgorithm.IsBanditStoppingTime τ)
    (_ : Measurable[hτ.measurableSpace] ψ) (_ : IsDeltaCorrect δ ν₀ ν₁ π τ ψ),
    expectedRounds ν₀ π τ

/-- `Q_edge(d, δ)`: the optimal null expected number of four-way replay rounds for testing the
one-edge null `(p + s, p + s)` against the alternative `(p + s + d, p + s)` at level `δ`. -/
noncomputable def Qedge (p s d δ : ℝ) : ENNReal :=
  optRounds δ (fourWayModel p s d false) (fourWayModel p s d true)

/-- `Q_vertex(d, δ)`: the optimal null expected number of vertex-paired replay rounds for the same
test. -/
noncomputable def Qvertex (p s d δ : ℝ) : ENNReal :=
  optRounds δ (vertexModel p s d false) (vertexModel p s d true)

end FairReplay


