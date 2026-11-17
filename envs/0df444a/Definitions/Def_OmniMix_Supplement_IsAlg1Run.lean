-- Prove2me | Definitions.Def_OmniMix_Supplement_IsAlg1Run
-- name    : OmniMix_Supplement_IsAlg1Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:36:55.980197+00:00
-- url     : https://prove2.me/theorems/b238db23-24b6-4853-b560-9100972e4bf1
-- title:
--   A run of Algorithm 1
-- statement:
--   Fix a finite class $F$, a horizon $T$, a learning rate $\eta$ and a context–outcome sequence $(x_t,y_t)_{t\le T}$. A sequence of probability measures $D_1,\dots,D_T$ on $[0,1]$ is a **run of Algorithm 1** if in every round $t$ it solves the round's EVI with precision $\epsilon_t=1/T$:
--   $$
--   \mathbb E_{P\sim D_t}\big[G_t(P)\,(y-P)\big]\le\frac1T\qquad\text{for both }y\in\{0,1\},
--   $$
--   where $G_t$ is computed from $D_1,\dots,D_{t-1}$, the earlier outcomes and the current context.
--
--   Any EVI solver produces such a run; guarantees of Algorithm 1 are statements about every run.
--
--   **Formalization Note** The integrand is bounded ($|G_t|\le\eta$) and Borel in $P$, so the integral is the expectation. The learning rate is a parameter; theorems fix it.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Algorithm 1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_OmniMix_Supplement_alg1G

namespace OmniMix.Supplement

open OmniMix

/-- **A run of Algorithm 1.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and
Beyond*, arXiv:2610.41023, Algorithm 1, p.11: "Use the EVI solver to find a distribution `D_t`
over `[0, 1]`, satisfying `E_{P∼D_t}[G_t(P)(y − P)] ≤ ϵ_t`, for all `y ∈ {0, 1}`", with `ϵ_t = 1/T`.

`IsAlg1Run F T η x y D` says that on the context–outcome sequence `(x, y)`, for every round `t`,
the forecast `D_t` (a probability measure on `[0,1]`) satisfies the EVI condition for the test
function `G_t` computed from `D_0, …, D_{t−1}`, `x` and `y` (rounds `< t`) and the current context
`x_t`.

**Formalization Note.** "An EVI solver" is any rule meeting the EVI condition; a run is any
sequence of forecast measures meeting it in every round. The integrand `G_t(P)(y − P)` is bounded
(`|G_t| ≤ η`) and Borel in `P`, so the Bochner integral is the paper's expectation. The learning
rate `η` (`0 < η ≤ 1/2` in the paper) is a parameter; theorems fix it. Rounds are 0-based. -/
def IsAlg1Run {X : Type*} (F : Finset (X → unitInterval)) (T : ℕ) (η : ℝ) (x : Fin T → X)
    (y : Fin T → Bool) (D : Fin T → MeasureTheory.ProbabilityMeasure unitInterval) : Prop :=
  ∀ t : Fin T, ∀ y' : Bool,
    ∫ P, alg1G F η x y D t P * (outVal y' - P) ∂(D t : MeasureTheory.Measure unitInterval) ≤
      1 / (T : ℝ)

end OmniMix.Supplement


