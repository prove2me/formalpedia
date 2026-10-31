-- Prove2me | Definitions.Def_FoundationsRL_LinUCB_IsLinUCB
-- name    : FoundationsRL_LinUCB_IsLinUCB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:22:11.766329+00:00
-- url     : https://prove2.me/theorems/f8c74c4e-2ed8-46ed-8e3b-e44731a4f6fe
-- title:
--   The LinUCB algorithm with input $\beta$
-- statement:
--   A run **follows LinUCB** with input $\beta$ for the first $T$ rounds, with estimates $\widehat\theta^t$, if at each round:
--
--   1. $\widehat\theta^t\in\Theta$ minimizes $\theta\mapsto\sum_{i<t}\bigl(\langle\theta,\phi(x^i,\pi^i)\rangle-r^i\bigr)^2$ over $\Theta$;
--   2. the action $\pi^t$ maximizes the optimistic value
--
--   $$
--   \pi\ \mapsto\ \max_{\theta:\ \|\theta-\widehat\theta^t\|_{\widetilde\Sigma^t}^2\le16\beta+4}\ \langle\theta,\phi(x^t,\pi)\rangle;
--   $$
--
--   3. $p^t$ is the point mass at $\pi^t$, since the algorithm is deterministic given the history.
--
--   Ties in both optimizations are arbitrary. LinUCB adapts the generic optimism template of §3.1 to linear function classes.
--
--   **Formalization Note** No measurability of $\widehat\theta^t$ is required. A randomized tie-break is covered by putting its coin in $\mathcal G_t$. If $\Theta$ is infinite and the minimum is not attained there is no such run, as in the book, where $\widehat\theta^t$ is an $\arg\min$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, LinUCB algorithm box, p. 43

import Mathlib
import Definitions.Def_FoundationsRL_LinUCB_sqLoss
import Definitions.Def_FoundationsRL_LinUCB_designMatrix
import Definitions.Def_FoundationsRL_LinUCB_ucbValue
import Definitions.Def_FoundationsRL_LinUCB_linearFunction

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.LinUCB

/-- The run `R` follows LinUCB with input `β` for the rounds before `T`, with least-squares
estimates `thetaHat` (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, algorithm box, p. 43):

* `thetaHat t ω` lies in `Θ` and minimizes `θ ↦ ∑_{i<t} (⟨θ, ϕ(x^i, π^i)⟩ − r^i)²` over `Θ`;
* `π^t` maximizes `π ↦ max {⟨θ, ϕ(x^t, π)⟩ : ∥θ − θ̂^t∥²_{Σ̃^t} ≤ 16β + 4}`;
* LinUCB is deterministic given the history: `p^t` is the point mass at `π^t`.

**Formalization Note.** Ties in both `arg min` and `arg max` are arbitrary. No measurability of
`thetaHat` is required, and `π^t` is `𝓖 t`-measurable because `p^t = δ_{π^t}` is a conditional law
given `𝓖 t`; a randomized tie-break is covered by putting its coin in `𝓖 t`. If `Θ` is
infinite and the minimum is not attained, there is no such run, as in the book, where `θ̂^t` is
an `arg min`. -/
structure IsLinUCB {Ω X Act : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace X]
    [MeasurableSpace Act] {P : Measure Ω} {Mstar : Kernel (X × Act) ℝ} {d : ℕ}
    (Θ : Set (Fin d → ℝ)) (ϕ : X → Act → Fin d → ℝ) (β : ℝ) (T : ℕ)
    (R : ContextualBanditRun P Mstar) (thetaHat : ℕ → Ω → Fin d → ℝ) : Prop where
  thetaHat_mem : ∀ t < T, ∀ ω, thetaHat t ω ∈ Θ
  thetaHat_min : ∀ t < T, ∀ ω, ∀ θ ∈ Θ,
    sqLoss R (linearFunction ϕ (thetaHat t ω)) t ω ≤ sqLoss R (linearFunction ϕ θ) t ω
  act_max : ∀ t < T, ∀ ω, ∀ a,
    ucbValue (designMatrix ϕ R t ω) (thetaHat t ω) (16 * β + 4) (ϕ (R.x t ω) a) ≤
      ucbValue (designMatrix ϕ R t ω) (thetaHat t ω) (16 * β + 4) (ϕ (R.x t ω) (R.act t ω))
  dirac : ∀ t < T, ∀ ω, R.p t ω = Measure.dirac (R.act t ω)

end FoundationsRL.LinUCB


