-- Prove2me | Definitions.Def_MetricMinTest_streamLaw
-- name    : MetricMinTest_streamLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:51.746382+00:00
-- url     : https://prove2.me/theorems/1abcd55a-6546-4faf-a397-fcbabfeca3e6
-- title:
--   Law of the observation table (stack of streams)
-- statement:
--   Observations are generated as a table $\omega=(\omega_{j,n})_{j,\,n\ge0}$ of independent entries with $\omega_{j,n}\sim P_j$. The $n$-th query to index $j$ (counted from $0$) reads $\omega_{j,n}$. This gives the same law of transcripts as the paper's description: at each query the tester receives a fresh observation from the queried law, conditionally independent of the past.
--
--   **Formalization Note** The table law is the infinite product measure $\bigotimes_j\bigotimes_{n\in\mathbb N}P_j$ on $\iota\to\mathbb N\to\mathbb R$. The tester's private randomness is drawn independently of it.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §2, p.6

import Mathlib
import Definitions.Def_MetricMinTest_Instance

namespace MetricMinTest

/-- **Law of the observation table.** Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §2 p.6: "At query t, the
tester chooses Iₜ from the past and receives a fresh observation from P_{Iₜ}, conditionally
independent of the past."

**Formalization Note.** Stack-of-streams encoding: the table `ω : ι → ℕ → ℝ` has independent
entries, `ω j n ∼ P_j`, and the `n`-th query (0-based) to index `j` reads `ω j n`. This gives
the same law of transcripts as fresh conditionally independent observations. The instance is
fixed before the tester's private randomness, which is independent of the table. -/
noncomputable def streamLaw {ι : Type} (P : Instance ι) : MeasureTheory.Measure (ι → ℕ → ℝ) :=
  MeasureTheory.Measure.infinitePi (fun i => MeasureTheory.Measure.infinitePi (fun _ : ℕ => P.law i))

instance streamLaw.instIsProbabilityMeasure {ι : Type} (P : Instance ι) :
    MeasureTheory.IsProbabilityMeasure (streamLaw P) := by
  unfold streamLaw; infer_instance

end MetricMinTest


