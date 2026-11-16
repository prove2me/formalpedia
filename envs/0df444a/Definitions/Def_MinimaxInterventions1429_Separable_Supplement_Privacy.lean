-- Prove2me | Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Privacy
-- name    : MinimaxInterventions1429_Separable_Supplement_Privacy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:12:16.533539+00:00
-- url     : https://prove2.me/theorems/65b7a4c5-29c5-41f1-acde-d5a91da7cdf8
-- title:
--   Simultaneous query accuracy and infimal private errors
-- statement:
--   A synopsis is an arbitrary measurable random object with a public deterministic decoder into $\Delta_k$. Its success event is a single measurable event on which every query in a specified set $Q$ is $\alpha$-optimal. Decoder randomness is included in the synopsis. For a database domain $D$, its specified adjacency relation, and a public table map $L:D\to[0,1]^{m\times k}$, define
--   $$\mathrm{err}_L=\inf\{r\ge0:\text{an }(\varepsilon,\delta)\text{-DP real-table release has }d_q\text{ error }\le r\text{ with probability }\ge1-\beta\text{ at every database}\},$$
--   and define $\mathrm{dec}_{L,Q}$ as the infimum of achievable simultaneous decision tolerances on $Q$ with the identical privacy and failure parameters.
--
--   Privacy uses the published event-form differential privacy definition and always holds on the full database domain. An optional accuracy class restricts only the success guarantee. Arbitrary measurable synopsis spaces are quantified in a universe, with no support, finite-domain, sensitivity, or public-contrast restriction. No infimum is assumed attained. This is the common interface for the private reductions.
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Section 2 and Section 6.1, printed pp.9, 18–19 (PDF pp.11, 20–21)

import Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Interfaces
set_option autoImplicit false
universe uPrivacy

noncomputable section

namespace MinimaxInterventions1429.Separable.Supplement
open MeasureTheory

/-- One measurable success event supports all later adaptive calls. -/
def Success {S : Type*} [MeasurableSpace S] (μ : Measure S) (β : ℝ)
    (P : S → Prop) : Prop :=
  ∃ E : Set S, MeasurableSet E ∧ ENNReal.ofReal (1 - β) ≤ μ E ∧ ∀ s ∈ E, P s

def AccurateOn {m k : ℕ} {S : Type*} (Dec : S → Table m k → Mixture k)
    (Q : Set (Table m k)) (L : Table m k) (α : ℝ) (s : S) : Prop :=
  ∀ B ∈ Q, Optimal (L + B) α (Dec s B)

/-- Only the decoder is public. No correctness, privacy, or reconstruction is a field. -/
structure Synopsis (S : Type*) (m k : ℕ) [MeasurableSpace S] where
  decode : S → Table m k → Mixture k
  measurable_decode : ∀ B, Measurable (fun s => (decode s B).val)

def PrivateSynopsis {D S : Type*} [MeasurableSpace S] {m k : ℕ}
    (adj : D → D → Prop) (L : D → Table m k) (Q : Set (Table m k))
    (ε δ β α : ℝ) (syn : Synopsis S m k) (law : D → Measure S)
    (X : Set D := Set.univ) : Prop :=
  (∀ d, IsProbabilityMeasure (law d)) ∧ DifferentiallyPrivate adj ε δ law ∧
    ∀ d ∈ X, Success (law d) β (AccurateOn syn.decode Q (L d) α)

def ReleaseAccurate {D : Type*} {m k : ℕ} (L : D → Table m k)
    (law : D → Measure (Table m k)) (β r : ℝ) (X : Set D := Set.univ) : Prop :=
  ∀ d ∈ X, Success (law d) β (fun M => quotientDist M (L d) ≤ r)

/-- Infima range over all measurable synopsis spaces in an arbitrary universe. -/
def achievableDecision {D : Type uPrivacy} {m k : ℕ} (adj : D → D → Prop)
    (L : D → Table m k) (Q : Set (Table m k)) (ε δ β α : ℝ)
    (X : Set D := Set.univ) : Prop :=
  0 ≤ α ∧ ∃ (S : Type uPrivacy) (ms : MeasurableSpace S) (syn : @Synopsis S m k ms)
    (law : D → @Measure S ms), @PrivateSynopsis D S ms m k adj L Q ε δ β α syn law X

def decisionError {D : Type uPrivacy} {m k : ℕ} (adj : D → D → Prop)
    (L : D → Table m k) (Q : Set (Table m k)) (ε δ β : ℝ)
    (X : Set D := Set.univ) : ℝ :=
  sInf {α | achievableDecision adj L Q ε δ β α X}

def achievableRelease {D : Type*} {m k : ℕ} (adj : D → D → Prop)
    (L : D → Table m k) (ε δ β r : ℝ) : Prop :=
  0 ≤ r ∧ ∃ law : D → Measure (Table m k),
    (∀ d, IsProbabilityMeasure (law d)) ∧ DifferentiallyPrivate adj ε δ law ∧
      ReleaseAccurate L law β r

def releaseError {D : Type*} {m k : ℕ} (adj : D → D → Prop)
    (L : D → Table m k) (ε δ β : ℝ) : ℝ :=
  sInf {r | achievableRelease adj L ε δ β r}

end MinimaxInterventions1429.Separable.Supplement


