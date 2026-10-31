-- Prove2me | Definitions.Def_EllsbergLearning_IsBrownianWrt
-- name    : EllsbergLearning_IsBrownianWrt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:13.344827+00:00
-- url     : https://prove2.me/theorems/33d84cac-0cdc-46c9-a892-699422920b8e
-- title:
--   Brownian motion with respect to a filtration, time $[0,\infty)$
-- statement:
--   Let $(\Omega,\mathcal F)$ be a measurable space with a filtration $\mathbb G=(\mathcal G_t)_{t\ge0}$ and a measure $Q$. A real process $W=(W_t)_{t\ge0}$ is a **$(\mathbb G,Q)$-Brownian motion** if
--
--   1. its finite-dimensional laws under $Q$ are those of standard Brownian motion and its paths are $Q$-a.s. continuous;
--   2. $W_t$ is $\mathcal G_t$-measurable for every $t$;
--   3. for $0\le s\le t$, the increment $W_t-W_s$ is independent of $\mathcal G_s$ under $Q$.
--
--   This is the notion in "$(W^\eta_t)$ is a Brownian motion under $P^\eta$" and "$(Z_t/\sigma)$ is a $\{\mathcal G_t\}$-adapted Brownian motion under $P_0$" in the construction of the predictive priors. It is a general object, reusable by any filtered Brownian model.
--
--   **Formalization Note** Built on Mathlib's `IsBrownianReal`, indexed by $t\in[0,\infty)$. The published `AtaBarjesteh23.Workload.IsDriftBM` is the same notion indexed by $\mathbb R$, which is why it is not reused.
-- source:
--   Epstein & Ji, Optimal Learning under Robustness and Time-Consistency, arXiv:1708.01890v2, §2, display (1), p.7; §2 Step 2, p.9

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EllsbergLearning

/-- `W` is a standard Brownian motion with respect to the filtration `𝔾` under the measure `Q`,
indexed by time `t ∈ [0, ∞)`: its finite-dimensional laws are those of standard Brownian motion
and its paths are `Q`-a.s. continuous (Mathlib's `IsBrownianReal`), `W t` is `𝔾 t`-measurable for
every `t`, and for `s ≤ t` the increment `W t - W s` is independent of `𝔾 s` under `Q`.

This is the notion behind "(W^η_t) is a Brownian motion under P^η" in Epstein & Ji, *Optimal
Learning under Robustness and Time-Consistency*, arXiv:1708.01890v2, §2, p.7, display (1), and
"(Z_t/σ) is a {G_t}-adapted Brownian motion under P0", §2, Step 2, p.9.

**Formalization Note.** Time is `ℝ≥0`, as in Mathlib's `IsBrownianReal`. A general (paper
independent) object; the published `AtaBarjesteh23.Workload.IsDriftBM` is the same notion indexed
by `ℝ`, which is why it is not reused here. -/
def IsBrownianWrt {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝔾 : Filtration ℝ≥0 mΩ) (Q : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) : Prop :=
  IsBrownianReal W Q ∧ (∀ t, StronglyMeasurable[𝔾 t] (W t)) ∧
    ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance) (𝔾 s) Q

end EllsbergLearning


