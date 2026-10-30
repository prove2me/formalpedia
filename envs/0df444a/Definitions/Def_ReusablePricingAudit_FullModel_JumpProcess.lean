-- Prove2me | Definitions.Def_ReusablePricingAudit_FullModel_JumpProcess
-- name    : ReusablePricingAudit_FullModel_JumpProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:47:41.960993+00:00
-- url     : https://prove2.me/theorems/3e924ab6-2ba1-40f0-82ba-3aa70ddd5370
-- title:
--   Marked Poisson clocks and observable-history controls
-- statement:
--   A **marked jump system** has a positive clock rate $\nu$, a probability law for independent event marks, and a transition mapping the current state, current action, and current mark to a new state and an optional observable event. The primitive law is the independent product of exponential clock gaps, event marks, and uniform randomization for the controller.
--
--   If $E_n$ is the $n$th clock gap, its event time is
--   $$\tau_n=\sum_{j=0}^{n}E_j.$$
--   At that time the control uses $\tau_n$, the state and observable events strictly before $\tau_n$, and its independent random seed. It cannot use the current mark. The state and history are computed recursively by applying the transition; silent ticks are omitted from the observable history. At a time $t$, the state includes all transitions with $\tau_n\le t$. The predictable decision uses only $\tau_n<t$.
--
--   This general construction separates the underlying controlled process from its pricing application. The signed expectation is the difference between the lower Lebesgue integrals of positive and negative parts. Application theorems establish finiteness; no Bochner default is used.
--
--   **Formalization Note** Histories are finite lists with the Borel sigma algebra induced by their length and padded entries. States and observation labels are natural numbers. Invalid or explosive clock paths use a fallback event count of zero; their nullity under the specified law is a theorem obligation.
--
--   Differences from the source:
--   - encoding: Poisson customers and independent exponential service times with non-anticipating pricing → independent marked exponential clocks, observable event histories, and independent uniform randomization; reason: uniformization generates the same loss-system law; dummy clock ticks are hidden and policies never see future marks
--   - encoding: expected real long-run liminf objectives → extended signed Lebesgue expectation and EReal liminf over real horizons; reason: finiteness is a separate theorem conclusion, so nonintegrable integrals or unbounded real suprema cannot silently become zero
-- source:
--   Besbes, Elmachtoub and Sun, Static Pricing: Universal Guarantees for Reusable Resources, arXiv:1905.00731v3 (11 February 2020), pp. 7–10, §§2.1–2.3; p. ec3 (PDF 24), §EC.2, uniformization preceding (EC.1)

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace ReusablePricingAudit.FullModel

/-- A finite observable history. Codes are supplied by the application; silent clock
ticks are never passed to a policy. Histories are in chronological order. -/
abbrev EventHistory := List (ℝ × ℕ)

/-- The usual Borel sigma algebra on finite histories, encoded by their length
and their sequence of entries padded with zero. -/
instance eventHistoryMeasurableSpace : MeasurableSpace EventHistory :=
  MeasurableSpace.comap (fun h : EventHistory =>
    (h.length, fun i : ℕ => h.getD i (0, 0))) inferInstance

/-- Independent auxiliary randomization, available to the controller from time zero. -/
abbrev Seed := ℕ → ℝ

/-- A jointly measurable decision rule using only the current time, current observable
state and strictly past observations, together with independent randomization. The
rule does not receive the current clock mark or any future primitive. -/
structure HistoryControl where
  rule : Seed → ℝ → ℕ → EventHistory → ℝ
  measurable_rule : Measurable (fun x : Seed × ℝ × ℕ × EventHistory =>
    rule x.1 x.2.1 x.2.2.1 x.2.2.2)

/-- A marked, constant-rate Poisson clock with a controlled transition and an optional
observable event. This is a general jump-process construction, separate from pricing.
The state is a natural number; bounded state spaces are enforced by transitions. -/
structure JumpSystem (Mark : Type) [MeasurableSpace Mark] where
  clockRate : ℝ
  clockRate_pos : 0 < clockRate
  markLaw : Measure Mark
  markLaw_probability : IsProbabilityMeasure markLaw
  transition : ℕ → ℝ → Mark → ℕ × Option ℕ

variable {Mark : Type} [MeasurableSpace Mark]

abbrev ClockPath (Mark : Type) := ℕ → ℝ × Mark

abbrev Experiment (Mark : Type) := Seed × ClockPath Mark

/-- Product primitives: independent uniforms for policy randomization, and i.i.d.
exponential gaps independently marked with the system's mark law. -/
noncomputable def experimentLaw (J : JumpSystem Mark) : Measure (Experiment Mark) :=
  (Measure.infinitePi (fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1))).prod
    (Measure.infinitePi (fun _ : ℕ => (expMeasure J.clockRate).prod J.markLaw))

/-- The time of clock event n (the first event has index zero). -/
noncomputable def eventTime (ω : ClockPath Mark) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (ω k).1

/-- State and observable history after n clock events, obtained by recursion from
the primitives, not from assumed occupation or performance identities. -/
noncomputable def evolution (J : JumpSystem Mark) (π : HistoryControl) (q₀ : ℕ)
    (ω : Experiment Mark) : ℕ → ℕ × EventHistory
  | 0 => (q₀, [])
  | n + 1 =>
    let old := evolution J π q₀ ω n
    let t := eventTime ω.2 n
    let a := π.rule ω.1 t old.1 old.2
    let new := J.transition old.1 a (ω.2 n).2
    (new.1, old.2 ++ (new.2.toList.map fun code => (t, code)))

/-- Number of clock events up to and including t. The fallback is used only on
explosive or invalid primitive paths, a null set under the specified law. -/
noncomputable def eventsBy (ω : ClockPath Mark) (t : ℝ) : ℕ := by
  classical
  exact if h : ∃ n, t < eventTime ω n then Nat.find h else 0

/-- Number of events strictly before t, for a predictable pre-event decision. -/
noncomputable def eventsBefore (ω : ClockPath Mark) (t : ℝ) : ℕ := by
  classical
  exact if h : ∃ n, t ≤ eventTime ω n then Nat.find h else 0

/-- The right-continuous state, including every transition at time t. -/
noncomputable def stateAt (J : JumpSystem Mark) (π : HistoryControl) (q₀ : ℕ)
    (ω : Experiment Mark) (t : ℝ) : ℕ :=
  (evolution J π q₀ ω (eventsBy ω.2 t)).1

/-- The action chosen just before clock event n. It depends on the pre-event state
and history and the event's time, but not its independent mark. -/
noncomputable def actionAtEvent (J : JumpSystem Mark) (π : HistoryControl) (q₀ : ℕ)
    (ω : Experiment Mark) (n : ℕ) : ℝ :=
  let old := evolution J π q₀ ω n
  π.rule ω.1 (eventTime ω.2 n) old.1 old.2

/-- The observation emitted at clock event n; none means an unobserved dummy tick. -/
noncomputable def observationAtEvent (J : JumpSystem Mark) (π : HistoryControl)
    (q₀ : ℕ) (ω : Experiment Mark) (n : ℕ) : Option ℕ :=
  (J.transition (evolution J π q₀ ω n).1 (actionAtEvent J π q₀ ω n) (ω.2 n).2).2

/-- Extended signed expectation, using the two nonnegative Lebesgue integrals.
This does not replace a nonintegrable random variable by zero. Applications
prove finiteness of the negative part before using extended subtraction. -/
noncomputable def signedExpectation {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) : EReal :=
  ((∫⁻ ω, ENNReal.ofReal (f ω) ∂P) : EReal) -
    ((∫⁻ ω, ENNReal.ofReal (-f ω) ∂P) : EReal)

end ReusablePricingAudit.FullModel


