-- Prove2me | Definitions.Def_HighDimProb_RandomProcesses_CanonicalMetric
-- name    : HighDimProb_RandomProcesses_CanonicalMetric
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:31:49.400407+00:00
-- url     : https://prove2.me/theorems/3294be22-fe42-4e9e-bd35-3c49cdc2af13
-- title:
--   The canonical (pseudo-)metric $d(t,s) = \lVert X_t - X_s\rVert_{L^2}$ of a random process
-- statement:
--   This is the **canonical (pseudo-)metric** of a random process, defined from the $L^2$ size of
--   its increments and used, in Section 7.4, to measure the geometry of the index set $T$.
--
--   Fix a probability space $(\Omega,\mathcal F,P)$ and a family $(X_t)_{t\in T}$ of real random
--   variables (with finite second moments) indexed by a set $T$. The canonical metric is
--
--   $$
--   d(t,s) \;:=\; \lVert X_t - X_s \rVert_{L^2} \;=\; \bigl(E\,(X_t - X_s)^2\bigr)^{1/2}, \qquad t,s \in T.
--   $$
--
--   As Remark 7.1.7 observes, $d$ turns the otherwise unstructured index set $T$ into a metric
--   space automatically — although in general it is only a *pseudo*metric: two distinct points
--   $t \ne s$ can have $d(t,s) = 0$ (e.g. if $X_t = X_s$ almost surely).
--
--   **Formalization Note** No positive-definiteness (`d(t,s)=0 → t=s`) is assumed or asserted, in
--   line with the book's own remark that $d$ is a pseudometric in general.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 158, Remark 7.1.7; restated as Eq. (7.13), p. 170

import Mathlib

open MeasureTheory

namespace HighDimProb.RandomProcesses

/-- The **canonical (pseudo-)metric** of a random process `(X_t)_{t∈T}` on a probability space
`(Ω, P)`:

`d(t, s) := ‖X_t − X_s‖_{L²} = (E (X_t − X_s)²)^{1/2}`.

Vershynin, *High-Dimensional Probability* (2018), p. 158 (PDF p. 166), Remark 7.1.7, restated as
Eq. (7.13) on p. 170 (PDF p. 178) for Section 7.4. As the book's own footnote to Remark 7.1.7
observes, `d` is in general only a *pseudo*metric on `T`: two distinct points can have
`d(t, s) = 0`. -/
noncomputable def canonicalMetric {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {T : Type}
    (X : T → Ω → ℝ) (t s : T) : ℝ :=
  Real.sqrt (∫ ω, (X t ω - X s ω) ^ 2 ∂P)

end HighDimProb.RandomProcesses


