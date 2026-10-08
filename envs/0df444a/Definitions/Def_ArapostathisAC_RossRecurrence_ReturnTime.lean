-- Prove2me | Definitions.Def_ArapostathisAC_RossRecurrence_ReturnTime
-- name    : ArapostathisAC_RossRecurrence_ReturnTime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T15:07:00.897278+00:00
-- url     : https://prove2.me/theorems/93ccd8e9-b9bc-4b5b-aac7-7538537fb3e3
-- title:
--   The return time τ = min{t ≥ 1 : X_t = 0}, its mean E^f_i[τ] and E^f_i[β^τ]
-- statement:
--   For a path $\omega=((x_0,a_0),(x_1,a_1),\dots)$ of the countable-state controlled Markov process of §5, the **return time** to state $0$ is
--   $$\tau(\omega)=\min\{t\ge1:\ x_t=0\},$$
--   with $\tau(\omega)=\infty$ when the path never visits $0$ at a time $t\ge1$. The minimum is over $t\ge1$, so $\tau\ge1$ even when $x_0=0$. The discount factor at the return time is $\beta^{\tau}$, which is $0$ when $\tau=\infty$.
--
--   For a stationary deterministic policy $f\in\Pi_{SD}$ and an initial state $i$, the definitions give the mean return time $E^f_i[\tau]$ and the expected discount factor $E^f_i[\beta^\tau]$, both under the path measure $P^f_i$ of the process controlled by $f$.
--
--   These quantities enter Ross's recurrence condition (5.7), $E^f_i[\tau]<K$ for all $f\in\Pi_{SD}$ and $i\in S$, and the proof of Theorem 5.3.
--
--   **Formalization Note.** $\tau$ is valued in $\mathbb N\cup\{\infty\}$ (`ℕ∞`), and both expectations are lower Lebesgue integrals in $[0,\infty]$. Hence a finite mean return time forces $\tau<\infty$ almost surely; this is not a separate assumption.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), pp. 301–302, Theorem 5.3 (definition of τ, (5.7)) and its proof ((5.8))

import Mathlib
import Definitions.Def_ArapostathisAC_RossRecurrence_CMP
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ArapostathisAC.RossRecurrence

/-- The return time to state `0`, `τ(ω) = min{t ≥ 1 : X_t = 0}` (Theorem 5.3, p. 301), of a path
`ω = ((x₀, a₀), (x₁, a₁), …)`, valued in `ℕ∞`: it is `⊤` if the path never returns to `0`. -/
noncomputable def returnTime {A : Type*} (ω : ℕ → ℕ × A) : ℕ∞ :=
  sInf ((fun t : ℕ => (t : ℕ∞)) '' {t : ℕ | 1 ≤ t ∧ (ω t).1 = 0})

/-- The discount factor at the return time, `β^τ(ω)`, with `β^τ = 0` when `τ = ∞`. -/
noncomputable def discAtReturn {A : Type*} (β : ℝ) (ω : ℕ → ℕ × A) : ℝ≥0∞ :=
  if returnTime ω = ⊤ then 0 else ENNReal.ofReal (β ^ (returnTime ω).toNat)

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- The mean return time `E^f_i[τ]` to state `0` of the process run under `f ∈ Π_SD` from `i`. -/
noncomputable def meanReturnTime (M : CMP A) (f : StationaryPolicy M) (i : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, (returnTime ω : ℝ≥0∞) ∂(pathMeasure M f.toPolicy i)

/-- `E^f_i[β^τ]`, the expected discount factor at the return time to `0` under `f ∈ Π_SD`. -/
noncomputable def expDiscAtReturn (M : CMP A) (f : StationaryPolicy M) (β : ℝ) (i : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, discAtReturn β ω ∂(pathMeasure M f.toPolicy i)

end ArapostathisAC.RossRecurrence


