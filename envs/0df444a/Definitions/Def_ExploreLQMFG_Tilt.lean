-- Prove2me | Definitions.Def_ExploreLQMFG_Tilt
-- name    : ExploreLQMFG_Tilt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:37.433366+00:00
-- url     : https://prove2.me/theorems/7bb0c4a0-b992-428d-8644-f37985a860f7
-- title:
--   The stochastic exponential $\mathcal E(H/\varepsilon)$ and the tilted measure $\mathbb P^{H/\varepsilon}$ (1.15)
-- statement:
--   Let $W$ be a $d$-dimensional Brownian motion on $(\Omega,\mathcal A,\mathbb P)$ with filtration $\mathbb F$, $T>0$, $\varepsilon>0$, and $H$ an $\mathbb R^d$-valued progressive process. The stochastic exponential (1.15) is
--   $$\mathcal E\big(\tfrac1\varepsilon H\big)=\exp\Big(-\frac1\varepsilon\int_0^T H_t\cdot dW_t-\frac1{2\varepsilon^2}\int_0^T|H_t|^2\,dt\Big),$$
--   with $\int_0^T H\cdot dW=\sum_j\int_0^T H^j\,dW^j$ the Itô integral, and the tilted measure is $\mathbb P^{H/\varepsilon}:=\mathcal E(\frac1\varepsilon H)\cdot\mathbb P$.
--
--   The paper uses $\mathbb P^{\varpi h^n/\varepsilon}$, the measure under which the $(n+1)$-st best response is computed, and $\mathbb P^{h/\varepsilon}=\mathbb P^{\varpi h^\varpi/\varepsilon}$, the measure of the limiting equilibrium. For bounded $H$, Novikov's criterion makes $\mathbb P^{H/\varepsilon}$ a probability measure, and by Girsanov's theorem $W^{H/\varepsilon}=W+\frac1\varepsilon\int_0^\cdot H\,dt$ is a Brownian motion under it.
--
--   **Formalization Note** Each scalar Itô integral is the value at $T$ of an Itô integral process in the sense of the published `Peng1990.SMP.IsItoIntegral`, chosen by `Classical.choose`; it is unique almost surely, so the measure does not depend on the choice. The measure is `Measure.withDensity` of the exponential.
-- source:
--   Delarue & Vasileiadis, Exploration Noise for Learning Linear-Quadratic Mean Field Games, arXiv:2107.00839v2 (https://arxiv.org/abs/2107.00839v2), (1.15) p.7; (2.1), (2.4) pp.19–20

import Mathlib
import Definitions.Def_ExploreLQMFG_Model

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Matrix

namespace ExploreLQMFG

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

open Classical in
/-- The stochastic integral `∫₀ᵀ H_t · dW_t = Σⱼ ∫₀ᵀ Hʲ_t dWʲ_t` of an `ℝᵈ`-valued process `H`
against the `d`-dimensional Brownian motion `W`, at the terminal time `T`.

**Formalization Note.** Each scalar integral `∫₀ᵀ Hʲ dWʲ` is the value at time `T` of an Itô
integral process in the sense of the published `Peng1990.SMP.IsItoIntegral` (the L²
construction, for the filtration `𝔽`), chosen by `Classical.choose`. The Itô integral is unique
almost surely, so every choice gives the same random variable up to a `P`-null set, and the
measure `tilt` below does not depend on the choice. If `Hʲ` has no Itô integral (it is not in
`L²_𝔽`) the term is `0`; every process to which the mission applies `tilt` is progressive and
bounded, so this default is never used. -/
noncomputable def itoDotT {d : ℕ} (𝔽 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → Fin d → ℝ) (H : ℝ≥0 → Ω → Fin d → ℝ) : Ω → ℝ :=
  fun ω => ∑ j : Fin d,
    if hJ : ∃ J, Peng1990.SMP.IsItoIntegral 𝔽 P T (fun s ω => W s ω j) (fun s ω => H s ω j) J
    then Classical.choose hJ T ω else 0

/-- The stochastic exponential (1.15) of arXiv:2107.00839v2 (p.7):
`ℰ((1/ε)H) = exp(−(1/ε) ∫₀ᵀ H_t · dW_t − (1/(2ε²)) ∫₀ᵀ |H_t|² dt)`.

**Formalization Note.** The time integral is the Bochner integral over `[0, T] ⊂ ℝ` of
`s ↦ |H_s|²`, with `H` read at `s.toNNReal`; for the bounded, path-continuous processes to
which the mission applies it, it is a genuine Lebesgue integral. -/
noncomputable def stochExp {d : ℕ} (𝔽 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → Fin d → ℝ) (ε : ℝ) (H : ℝ≥0 → Ω → Fin d → ℝ) : Ω → ℝ :=
  fun ω => Real.exp (-(1 / ε) * itoDotT 𝔽 P T W H ω
    - 1 / (2 * ε ^ 2) * ∫ s in Set.Icc (0 : ℝ) T, eSq (H s.toNNReal ω))

/-- The tilted probability measure `ℙ^{H/ε} := ℰ((1/ε)H) · ℙ` of arXiv:2107.00839v2, (1.15),
p.7: the measure with density `ℰ((1/ε)H)` with respect to `ℙ`. The paper uses
`ℙ^{ϖhⁿ/ε}` (`H = ϖhⁿ`) and `ℙ^{h/ε} = ℙ^{ϖh^ϖ/ε}` (`H = ϖh^ϖ`).

**Formalization Note.** Defined with `Measure.withDensity`. For a bounded progressive `H`,
Novikov's criterion makes the density a true martingale at time `T`, so this is a probability
measure; the definition itself asserts nothing about its mass. -/
noncomputable def tilt {d : ℕ} (𝔽 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → Fin d → ℝ) (ε : ℝ) (H : ℝ≥0 → Ω → Fin d → ℝ) : Measure Ω :=
  P.withDensity fun ω => ENNReal.ofReal (stochExp 𝔽 P T W ε H ω)

end ExploreLQMFG


