-- Prove2me | Definitions.Def_MetricMinTest_sharedTester
-- name    : MetricMinTest_sharedTester
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:35.92621+00:00
-- url     : https://prove2.me/theorems/253018cf-61b2-449e-9017-a61cd882ec57
-- title:
--   The shared allocation tester
-- statement:
--   For a feasible allocation $w$ of (1.1) with mass $W$: draw $I_t\sim w/W$ independently, query $I_t$, and update the statistic $S_i$ of Lemma B.1 with $r=0$ for every target $i$ simultaneously. Mark $i$ at its first crossing of $L=\ln(1/\delta)$. Accept when all targets are marked, and otherwise reject after
--   $$N_w=\big\lceil16W\big(\ln(k/\delta)+\tfrac12\ln(1/\delta)\big)\big\rceil$$
--   queries.
--
--   **Formalization Note** The private randomness is the i.i.d. draw sequence; the statistics are computed from the tester's history.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Appendix B, p.23

import Mathlib
import Definitions.Def_MetricMinTest_Tester
import Definitions.Def_MetricMinTest_drawLaw

namespace MetricMinTest

/-- **The shared tester** (Appendix B). Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Appendix B, p.23: "For a
feasible w in (1.1) with mass W, draw Iₜ ∼ w/W independently, query Iₜ, and update the statistic
Sᵢ of Lemma B.1 with r = 0 for every target i ∈ [k] simultaneously. Mark i at its first crossing
of L. Accept when all targets are marked, and otherwise reject after
N_w = ⌈16W(ln(k/δ) + ½ ln(1/δ))⌉ queries."

**Formalization Note.** Private randomness is the i.i.d. draw sequence `ξ : ℕ → ι` with law
`(w/W)^⊗ℕ`; the `n`-th query (0-based) is `ξ n`. On a history `h` of `(index, observation)` pairs,
target `i`'s statistic after `t` steps is `∑_{s<t} [a(xₛ − d(i, jₛ)) − a²/2]` with
`a = (γ − d(i, jₛ))₊` (Lemma B.1 with `z = i`, `r = 0`), and `i` is marked once some `t ≤ |h|` has
statistic `≥ L = ln(1/δ)`. The tester stops when every target is marked or after `N_w` queries,
and accepts iff every target is marked. `k = |ι|`. -/
noncomputable def sharedTester {ι : Type} [Fintype ι] [MeasurableSpace ι] (d : ι → ι → ℝ)
    (γ δ : ℝ) (w : ι → ℝ) : Tester ι :=
  let L : ℝ := Real.log (1 / δ)
  let Nw : ℕ := ⌈16 * (∑ j, w j) *
    (Real.log ((Fintype.card ι : ℝ) / δ) + 1 / 2 * Real.log (1 / δ))⌉₊
  let stat : ι → List (ι × ℝ) → ℕ → ℝ := fun i h t =>
    ((h.take t).map (fun p => max (γ - d i p.1) 0 * (p.2 - d i p.1) -
      (max (γ - d i p.1) 0) ^ 2 / 2)).sum
  let allMarked : List (ι × ℝ) → Prop := fun h => ∀ i, ∃ t ≤ h.length, L ≤ stat i h t
  { Ξ := ℕ → ι
    μξ := MeasureTheory.Measure.infinitePi (fun _ : ℕ => drawLaw w)
    next := fun ξ h =>
      haveI := Classical.propDecidable (allMarked h ∨ Nw ≤ h.length)
      if allMarked h ∨ Nw ≤ h.length then none else some (ξ h.length)
    accept := fun _ h =>
      haveI := Classical.propDecidable (allMarked h)
      decide (allMarked h) }

end MetricMinTest


