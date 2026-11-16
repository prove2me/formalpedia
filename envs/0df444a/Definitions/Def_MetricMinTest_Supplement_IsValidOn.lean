-- Prove2me | Definitions.Def_MetricMinTest_Supplement_IsValidOn
-- name    : MetricMinTest_Supplement_IsValidOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:25:56.233199+00:00
-- url     : https://prove2.me/theorems/001e1b20-2a4c-4445-ba4f-4e0077633e4e
-- title:
--   Validity of a tester on a general instance class
-- statement:
--   Let $\mathcal C$ be a class of instances (laws on $[-1,1]$ indexed by a finite set), $\mathcal N$ the instances that must be rejected and $\mathcal A$ those that must be accepted. A tester is **valid at level $\delta$ on $(\mathcal C,\mathcal N,\mathcal A)$** if on every $P\in\mathcal C$ it stops almost surely, and
--   $$\Pr_P(\text{accept})\le\delta\quad(P\in\mathcal C\cap\mathcal N),\qquad \Pr_P(\text{accept})\ge1-\delta\quad(P\in\mathcal C\cap\mathcal A).$$
--
--   This is the contract of Definition 2.1 transported to the paper's non-metric classes: known blocks with block-dependent margins (Appendix H), instances with at most two laws (Theorem J.1), finite certificate systems (Theorem K.2) and superharmonic chains (Theorem K.3). With $\mathcal C=\mathcal P_d$, $\mathcal N=\{\min_i\mu_i<0\}$, $\mathcal A=\mathcal P_d^+(\gamma)$ it is $(\gamma,\delta)$-validity.
--
--   **Formalization Note** As in the published validity predicate, probabilities are over the private randomness (a probability measure) times the observation table, and the acceptance event and the stopping time are required to be measurable.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition 2.1, p.6; Appendix H, p.29; Theorem J.1, p.31; Definition K.1, p.32; §K.1, p.33

import Mathlib
import Definitions.Def_MetricMinTest_Tester_stopTime
import Definitions.Def_MetricMinTest_Tester_Accepts
import Definitions.Def_MetricMinTest_streamLaw

namespace MetricMinTest.Supplement

open MeasureTheory

/-- **Validity of a tester on an instance class** (the contract of Definition 2.1 on a general
class). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Definition 2.1 p.6, and its use for the known-block class (Appendix H, p.29: "Validity
is understood with block-dependent margins"), the two-law class (Theorem J.1, p.31), finite
certificate systems (Definition K.1, p.32: "both errors at most δ") and superharmonic chains
(§K.1, p.33: "The testing contract is unchanged").

**Formalization Note.** `cls` is the instance class, `neg` the instances that must be rejected and
`pos` the instances that must be accepted. The tester stops almost surely on every instance of
`cls`; on instances of `cls ∩ neg` it accepts with probability at most `δ`; on instances of
`cls ∩ pos` with probability at least `1 − δ`. As in the published `Tester.IsValid`,
probabilities are over `μξ ⊗ streamLaw P`, `μξ` is a probability measure, and the acceptance event
and the stopping time are measurable. For `cls = P_d`, `neg` = some mean negative and
`pos = P_d^+(γ)` this is exactly `Tester.IsValid d γ δ`. -/
def IsValidOn {ι : Type} [DecidableEq ι] (T : Tester ι) (cls neg pos : Set (Instance ι))
    (δ : ℝ) : Prop :=
  IsProbabilityMeasure T.μξ ∧
  MeasurableSet {p : T.Ξ × (ι → ℕ → ℝ) | T.Accepts p.1 p.2} ∧
  Measurable (fun p : T.Ξ × (ι → ℕ → ℝ) => ((T.stopTime p.1 p.2 : ℕ∞) : ENNReal)) ∧
  ∀ P ∈ cls,
    (T.μξ.prod (streamLaw P)) {p | T.stopTime p.1 p.2 = ⊤} = 0 ∧
    (P ∈ neg → (T.μξ.prod (streamLaw P)) {p | T.Accepts p.1 p.2} ≤ ENNReal.ofReal δ) ∧
    (P ∈ pos → ENNReal.ofReal (1 - δ) ≤ (T.μξ.prod (streamLaw P)) {p | T.Accepts p.1 p.2})

end MetricMinTest.Supplement


