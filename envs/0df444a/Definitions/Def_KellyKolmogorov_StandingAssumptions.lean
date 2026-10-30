-- Prove2me | Definitions.Def_KellyKolmogorov_StandingAssumptions
-- name    : KellyKolmogorov_StandingAssumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:38:25.290912+00:00
-- url     : https://prove2.me/theorems/ca935e05-3e9d-488e-af12-d6f8fce8ec84
-- title:
--   Standing assumptions of §1.1 on a continuous-time Markov process
-- statement:
--   Let $X(t)$, $t\in\mathbb R$, be a process on a probability space with values in a countable state space $\mathcal S$. It satisfies the **standing assumptions** of §1.1 if
--
--   1. each $X(t)$ is a random variable;
--   2. $X$ is a Markov process;
--   3. $X$ is time homogeneous;
--   4. $X$ is irreducible;
--   5. almost every sample path is right-continuous with finitely many jumps in every bounded interval, i.e. the process remains in each state for a positive length of time and cannot pass through infinitely many states in finite time.
--
--   The book assumes these throughout ("throughout this work we shall assume that any continuous time Markov process with which we deal is not only time homogeneous and irreducible but also remains in each state for a positive length of time and is incapable of passing through an infinite number of states in a finite time"). They are hypotheses of every theorem of this mission about a process.
--
--   **Formalization Note** Nothing else is bundled: no finiteness of $\mathcal S$, no bound on the rates, no stationarity (stated separately where the book says "stationary").
-- source:
--   Kelly, Reversibility and Stochastic Networks (Wiley 1979), §1.1, pp. 1–3 (PDF pp. 4–6)

import Mathlib
import Definitions.Def_KellyKolmogorov_IsMarkov
import Definitions.Def_KellyKolmogorov_IsTimeHomogeneous
import Definitions.Def_KellyKolmogorov_IsIrreducible
import Definitions.Def_KellyKolmogorov_HasRegularPaths

open MeasureTheory

namespace KellyKolmogorov

/-- **The standing assumptions on a continuous-time Markov process (§1.1).**
Kelly, *Reversibility and Stochastic Networks* (Wiley 1979), §1.1, pp. 1–3. The process
`X(t)`, `t ∈ ℝ`, takes values in a countable state space `𝒮` (p. 1); it is a Markov process
(p. 1); and "throughout this work we shall assume that any continuous time Markov process with
which we deal is not only time homogeneous and irreducible but also remains in each state for a
positive length of time and is incapable of passing through an infinite number of states in a
finite time" (pp. 2–3).

Fields:
1. `measurable`: each `X(t)` is a random variable;
2. `markov`: the Markov property (`IsMarkov`);
3. `homogeneous`: time homogeneity (`IsTimeHomogeneous`);
4. `irreducible`: irreducibility (`IsIrreducible`);
5. `regular`: right-continuous paths with finitely many jumps on bounded intervals
   (`HasRegularPaths`).

**Formalization Note.** Nothing beyond §1.1 is bundled: no finiteness of `𝒮`, no bound on the
rates, no stationarity (stationarity is a separate hypothesis where the book says "stationary"). -/
structure StandingAssumptions {Ω 𝒮 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒮]
    (μ : Measure Ω) (X : ℝ → Ω → 𝒮) : Prop where
  measurable : ∀ t, Measurable (X t)
  markov : IsMarkov μ X
  homogeneous : IsTimeHomogeneous μ X
  irreducible : IsIrreducible μ X
  regular : HasRegularPaths μ X

end KellyKolmogorov


