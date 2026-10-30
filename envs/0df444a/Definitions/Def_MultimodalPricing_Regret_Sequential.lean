-- Prove2me | Definitions.Def_MultimodalPricing_Regret_Sequential
-- name    : MultimodalPricing_Regret_Sequential
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:01:48.626929+00:00
-- url     : https://prove2.me/theorems/822e3861-5fe8-4b79-b36b-3c57a5406c1e
-- title:
--   Sequential bounded demand and observation laws
-- statement:
--   A history is an ordered list of real price-demand pairs, with every repeated observation retained. Its measurable representation is the disjoint union of finite Euclidean products. A demand kernel takes a history and a current price to a probability law on real demands; at every feasible price it is supported in $[0,1]$, has an integrable identity function, and has mean $f(p)$.
--
--   An observation process has a filtration of predecision information, predictable real prices and next-step measurable demands. It realizes such a kernel when, for each predecision measurable event $A$ and Borel demand set $S$, the probability of $A\cap\{d_n\in S\}$ equals the integral over $A$ of the kernel's probability of $S$ at the observed prefix and current price. Prices and demands are feasible almost surely. Time is indexed from zero. The filtration may include private randomization and other information preserving this conditional law. No independence or regret conclusion is part of admissibility.
-- source:
--   Wang, Chen, Simchi-Levi, Multi-Modal Dynamic Pricing, https://doi.org/10.1287/mnsc.2020.3819, supplied artifact (published metadata; SSRN 3489355 footer), §2, printed/PDF p. 9; companion, p. 32

import Mathlib

open MeasureTheory ProbabilityTheory

noncomputable section

namespace MultimodalPricing.Regret

/-- Ordered price-demand pairs, retaining multiplicity. -/
abbrev History := List (ℝ × ℝ)

/-- Past observations at the start of round n (paper round n+1). -/
def history {Ω : Type*} (p d : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : History :=
  List.ofFn (fun i : Fin n => (p i ω, d i ω))

/-- The same finite history in a disjoint union of finite Euclidean products,
with its canonical measurable space. -/
abbrev ObservationPrefix := Σ n : ℕ, Fin n → ℝ × ℝ

def observationPrefix {Ω : Type*} (p d : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ObservationPrefix :=
  ⟨n, fun i => (p i ω, d i ω)⟩

/-- A measurable sequential demand kernel; the domain includes current price. -/
abbrev DemandKernel := Kernel (ObservationPrefix × ℝ) ℝ

/-- Bounded probability laws with the stated mean, for every history and feasible price. -/
def IsDemandKernel (a b : ℝ) (f : ℝ → ℝ) (K : DemandKernel) : Prop :=
  IsMarkovKernel K ∧ ∀ h p, p ∈ Set.Icc a b →
    K (h, p) (Set.Icc (0 : ℝ) 1) = 1 ∧
    Integrable (fun d : ℝ => d) (K (h, p)) ∧
    (∫ d : ℝ, d ∂K (h, p)) = f p

/-- Predecision information includes private randomization; demand arrives one step later. -/
structure Observation (Ω : Type*) [mΩ : MeasurableSpace Ω] where
  info : Filtration ℕ mΩ
  price : ℕ → Ω → ℝ
  demand : ℕ → Ω → ℝ

/-- A kernel realization, expressed by the defining conditional-law integral identity.
No independence, concentration, or confidence conclusion is an admissibility condition. -/
def IsObservation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : ℕ) (a b : ℝ) (f : ℝ → ℝ) (O : Observation Ω) : Prop :=
  ∃ K : DemandKernel, IsDemandKernel a b f K ∧
    (∀ n < T, Measurable[O.info n] (O.price n)) ∧
    (∀ n < T, Measurable[O.info (n + 1)] (O.demand n)) ∧
    (∀ᵐ ω ∂μ, ∀ n < T,
      O.price n ω ∈ Set.Icc a b ∧ O.demand n ω ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ n < T, ∀ A : Set Ω, MeasurableSet[O.info n] A →
      ∀ S : Set ℝ, MeasurableSet S →
      μ (A ∩ O.demand n ⁻¹' S) =
        ∫⁻ ω in A, K (observationPrefix O.price O.demand n ω, O.price n ω) S ∂μ)

end MultimodalPricing.Regret


