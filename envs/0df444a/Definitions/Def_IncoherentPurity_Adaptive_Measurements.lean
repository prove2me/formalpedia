-- Prove2me | Definitions.Def_IncoherentPurity_Adaptive_Measurements
-- name    : IncoherentPurity_Adaptive_Measurements
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:30.205617+00:00
-- url     : https://prove2.me/theorems/a418267c-18be-4293-b7e6-5c7ecff88cfb
-- title:
--   Arbitrary measurable POVMs and adaptive single-copy protocols
-- statement:
--   A state is a positive semidefinite complex matrix of trace one, using the published density-matrix predicate. For a positive operator valued measure $M$, its effects satisfy $M(\Omega)=I$, and the scalar outcome kernel is the Born law $\Pr_\rho(A)=\operatorname{Re}\operatorname{tr}(\rho M(A))$. Outcomes and independent classical seeds have arbitrary measurable spaces. A protocol chooses each such measurement from its classical history and seed, and has a measurable real readout independent of the unknown state. Only classical information passes between copies.
--
--   Success means that the same protocol has $\Pr(|\widehat P-\operatorname{tr}\rho^2|\le\varepsilon\operatorname{tr}\rho^2)\ge2/3$ for every state at a fixed worst-case budget. Histories use a countable sequence of tagged outcomes; unused slots contain a fixed tag. The law is computed by successive Born kernels, and non-adaptivity means history-independent measurements.
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, definitions and constructions, PDF pp.3,8,24–25 = printed pp.3,8,24–25; Definition 1.1; Section 2 measurement conventions; Appendix A equations (A.1)–(A.9)

import Mathlib
import Definitions.Def_pme_quantum_basics

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder
noncomputable section

namespace IncoherentPurity.Adaptive

abbrev Op (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
instance (d : ℕ) : MeasurableSpace (Op d) := borel (Op d)
instance (d : ℕ) : BorelSpace (Op d) := ⟨rfl⟩

abbrev State (d : ℕ) := {ρ : Op d // ProjectiveMeasurementEquilibration.IsDensityMatrix ρ}
def powerSum {d : ℕ} (ρ : Op d) (k : ℕ) : ℝ := (ρ ^ k).trace.re

/-- A normalized operator-valued measure on an arbitrary measurable outcome space.
The Born kernel is part of its measure representation, fixed on every state by `born_eq`.
Its countable additivity is inherited from the scalar Born measures (which separate effects).
Source: §§1–2, pp.3,8; Appendix A, pp.24–25. -/
structure POVM (d : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  effect : Set Ω → Op d
  positive : ∀ A, MeasurableSet A → (effect A).PosSemidef
  total : effect Set.univ = 1
  born : Kernel (State d) Ω
  markov : IsMarkovKernel born
  born_eq : ∀ (ρ : State d) A, MeasurableSet A →
    born ρ A = ENNReal.ofReal ((ρ.val * effect A).trace.re)

/-- Classical seed, history-dependent single-copy Born kernels, and a state-independent
readout. No finiteness or standard Borel assumption on the classical spaces. -/
structure Protocol (d : ℕ) where
  Seed : Type
  Outcome : Type
  seedMS : MeasurableSpace Seed
  outcomeMS : MeasurableSpace Outcome
  seedLaw : @Measure Seed seedMS
  seed_probability : @IsProbabilityMeasure Seed seedMS seedLaw
  measurement : letI := outcomeMS; ℕ → Seed × (ℕ → (Unit ⊕ Outcome)) → POVM d Outcome
  step : letI := seedMS; letI := outcomeMS;
    ℕ → Kernel (State d × (Seed × (ℕ → (Unit ⊕ Outcome)))) Outcome
  step_markov : letI := seedMS; letI := outcomeMS; ∀ t, IsMarkovKernel (step t)
  step_eq : letI := seedMS; letI := outcomeMS;
    ∀ t (ρ : State d) h, step t (ρ,h) = (measurement t h).born ρ
  output : Seed × (ℕ → (Unit ⊕ Outcome)) → ℝ
  measurable_output : letI := seedMS; letI := outcomeMS; Measurable output

attribute [instance] Protocol.seedMS Protocol.outcomeMS

def transcriptLaw {d : ℕ} (P : Protocol d) (ρ : State d) :
    ℕ → Measure (P.Seed × (ℕ → (Unit ⊕ P.Outcome)))
  | 0 => P.seedLaw.map (fun r => (r, fun _ => Sum.inl ()))
  | t+1 => (transcriptLaw P ρ t).bind (fun h =>
      (P.step t (ρ,h)).map (fun y => (h.1, fun i => if i = t then Sum.inr y else h.2 i)))

def IsNonadaptive {d : ℕ} (P : Protocol d) : Prop :=
  ∀ t r h h', P.measurement t (r,h) = P.measurement t (r,h')

def Succeeds {d : ℕ} (P : Protocol d) (N : ℕ) (ε : ℝ) : Prop :=
  ∀ ρ : State d,
    ENNReal.ofReal (2/3 : ℝ) ≤ (transcriptLaw P ρ N)
      {h | |P.output h - powerSum ρ.val 2| ≤ ε * powerSum ρ.val 2}

def rate (d : ℕ) (ε : ℝ) : ℝ :=
  min ((d : ℝ) / ε^2 + (d : ℝ) * Real.sqrt d / ε)
      ((d : ℝ)^2 / ε + Real.sqrt d / ε^2)

end IncoherentPurity.Adaptive


