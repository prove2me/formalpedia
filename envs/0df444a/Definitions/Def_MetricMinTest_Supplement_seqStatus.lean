-- Prove2me | Definitions.Def_MetricMinTest_Supplement_seqStatus
-- name    : MetricMinTest_Supplement_seqStatus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:27:41.988405+00:00
-- url     : https://prove2.me/theorems/6836ec1d-eb7c-4555-9363-1703fe1467a7
-- title:
--   Status of a sequence of one-stream threshold tests
-- statement:
--   A **one-stream threshold test** with index $j$, threshold $a$, gap $\eta$, boundary $\beta$ and cap $N$ reads observations $X_1,X_2,\dots$ of index $j$, forms
--   $$S_n=\eta\sum_{t=1}^n(X_t-a)-\frac{n\eta^2}{2},\qquad T=\inf\{n\ge1:S_n\ge\beta\},$$
--   and passes if $T\le N$; otherwise it fails after $N$ samples (§A.1). The paper runs such tests one after another on fresh samples, rejecting at the first failure and accepting if all pass (the clean-up phase of TwoPhase, RandBall, the cover tester).
--
--   Given the list of tests and the observations read so far, this function returns the next index to query, or the decision.
--
--   **Formalization Note** A test is the tuple $(j,a,\eta,\beta,N)$. The current test passes at the first $n\in\{1,\dots,N\}$ with $S_n\ge\beta$, its $n$ observations are consumed and the next test starts; it fails once $N$ observations were read without crossing. An empty list accepts.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), §A.1, p.21; Appendix C, p.23; Appendix D, p.26; Appendix I, p.30

import Mathlib
import Definitions.Def_MetricMinTest_oneStreamStat

namespace MetricMinTest.Supplement

open Classical in
/-- **Status of a run of one-stream tests in sequence.** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), §A.1 p.21 (the one-stream test:
"S_n = η ∑_{t=1}^n (X_t − a) − nη²/2, T = inf{n ≥ 1 : S_n ≥ β}. The test passes if T ≤ N and
otherwise fails after N samples"), as run in sequence on fresh samples by the clean-up phase of
TwoPhase (p.23), by RandBall (p.26) and by the cover tester (p.30): "Reject at the first failure,
and accept if all pass."

**Formalization Note.** A test is `(j, a, η, β, N)`: index `j`, threshold `a`, gap `η`,
boundary `β`, cap `N`. Given the list of tests and the observations `xs` read so far (in
order), the result is `Sum.inl j` (query index `j` next) or `Sum.inr b` (stop with decision
`b`, `true` = accept). The current test passes at the first `n ∈ {1, …, N}` with
`S_n ≥ β`; its `n` observations are consumed and the next test starts. It fails (reject) once
`N` observations have been read without crossing. An empty list accepts. -/
noncomputable def seqStatus {ι : Type} : List (ι × ℝ × ℝ × ℝ × ℕ) → List ℝ → ι ⊕ Bool
  | [], _ => Sum.inr true
  | (j, a, η, β, N) :: rest, xs =>
    match (List.range' 1 N).find?
        (fun n => decide (n ≤ xs.length ∧ β ≤ oneStreamStat η a (fun t => xs.getD t 0) n)) with
    | some n => seqStatus rest (xs.drop n)
    | none => if N ≤ xs.length then Sum.inr false else Sum.inl j

end MetricMinTest.Supplement


