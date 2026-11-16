-- Prove2me | Definitions.Def_MetricMinTest_Supplement_seqTester
-- name    : MetricMinTest_Supplement_seqTester
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:28:16.075972+00:00
-- url     : https://prove2.me/theorems/124e12dc-4ea9-4d6f-a6be-910ac4feb98e
-- title:
--   Conjunction of one-stream tests run in sequence (deterministic tester)
-- statement:
--   Given a list of one-stream threshold tests $(j_t,a_t,\eta_t,\beta_t,N_t)$, the tester runs them in order, each on fresh observations of its index $j_t$, rejects at the first failed test and accepts if all pass.
--
--   With the tests $(j_t,r_t,\gamma-r_t,L,\lceil32(\gamma-r_t)^{-2}\ln(\nu/\delta)\rceil)$ of an integral cover this is the **cover tester** of Appendix I; with one test per index against threshold $0$ it is the **index-wise conjunction** of Theorem J.1.
--
--   **Formalization Note** No private randomness. In the stack-of-streams model every query to index $j$ reads a new entry of stream $j$, so different tests at the same index use different samples.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Appendix I, p.30; Theorem J.1, p.31

import Mathlib
import Definitions.Def_MetricMinTest_Tester
import Definitions.Def_MetricMinTest_Supplement_seqStatus

namespace MetricMinTest.Supplement

/-- **Deterministic conjunction of one-stream tests run in sequence.** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Appendix I, p.30:
"For an integral cover (j_t, r_t), t = 1, …, ν, … Run threshold tests at boundary L with caps
⌈32 a_t⁻² ln(ν/δ)⌉, accepting only if all pass"; Theorem J.1, p.31 ("An index-wise
conjunction").

**Formalization Note.** No private randomness (`Ξ = Unit`, `μξ = δ_()`). The tests are run in
the order of the list, each on fresh samples of its index (the stack-of-streams model of
`Tester.hist` gives a fresh entry of stream `j` at each query), with the status of
`seqStatus`; the observations of the history are read in order. -/
noncomputable def seqTester {ι : Type} (tests : List (ι × ℝ × ℝ × ℝ × ℕ)) : Tester ι where
  Ξ := Unit
  μξ := MeasureTheory.Measure.dirac ()
  next := fun _ h => (seqStatus tests (h.map Prod.snd)).elim some (fun _ => none)
  accept := fun _ h => (seqStatus tests (h.map Prod.snd)).elim (fun _ => false) id

end MetricMinTest.Supplement


