-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_pathMeasure
-- name    : BauerleRiederMDP_RegimeSwitching_pathMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:55.996075+00:00
-- url     : https://prove2.me/theorems/f3ce08e2-93ad-45eb-ba60-642468401e08
-- title:
--   Law $\mathbb P^\pi_{nx}$ of the controlled state process (Ionescu–Tulcea)
-- statement:
--   For a Markov policy $\pi$, a time $n$ and a state $x$, $\mathbb P^\pi_{nx}$ is the law of the controlled state process started in $x$ at time $n$: the unique probability measure on paths $(x_0,x_1,\dots)$ with $x_0=x$ and
--
--   $$
--   \mathbb P\big(X_{l+1}\in B\mid X_0,\dots,X_l\big)=Q_{n+l}\big(B\mid X_l,f_{n+l}(X_l)\big),
--   $$
--
--   given by the Ionescu–Tulcea theorem. Coordinate $l$ is the state at time $n+l$.
--
--   **Formalization Note** Paths are indexed by all of $\mathbb N$; an $N$-stage criterion reads only the coordinates up to $N-n$, whose joint law is the book's measure on $E^{N-n+1}$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), pp.16–17 (PDF pp.31–32)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_stepKernel
open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.RegimeSwitching

/-- The law `ℙ^π_{nx}` of the controlled state process started in state `x` at time `n`
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §2.1, pp.16–17, PDF pp.31–32): by the Ionescu–Tulcea theorem the unique probability
measure on paths `ω = (ω_0, ω_1, …)` with `ω_0 = x` and `ℙ(ω_{l+1} ∈ B | ω_0, …, ω_l) =
Q_{n+l}(B | ω_l, f_{n+l}(ω_l))`. Coordinate `ω_l` is the state `X_{n+l}` at time `n + l`.

**Formalization Note.** Built with Mathlib's `Kernel.trajMeasure` (Ionescu–Tulcea) from the
initial law `δ_x` and the kernels `stepKernel M π (n + l)` applied to the last coordinate. Paths
are indexed by all of `ℕ`; an `N`-stage criterion only reads the coordinates `l ≤ N - n`, whose
joint law is the book's `ℙ^π_{nx}` on `E^{N-n+1}`. -/
noncomputable def pathMeasure {E A Z : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [MeasurableSpace Z] (M : DisturbanceMDM E A Z) (π : MarkovPolicy E A) (n : ℕ) (x : E) :
    Measure (ℕ → E) :=
  Kernel.trajMeasure (X := fun _ => E) (Measure.dirac x)
    (fun k => (stepKernel M π (n + k)).comap (fun h => h ⟨k, Finset.mem_Iic.2 le_rfl⟩)
      (measurable_pi_apply _))

end BauerleRiederMDP.RegimeSwitching


