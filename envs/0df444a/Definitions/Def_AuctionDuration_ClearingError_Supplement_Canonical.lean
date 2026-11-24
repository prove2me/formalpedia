-- Prove2me | Definitions.Def_AuctionDuration_ClearingError_Supplement_Canonical
-- name    : AuctionDuration_ClearingError_Supplement_Canonical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:46:51.322581+00:00
-- url     : https://prove2.me/theorems/9e438bab-f7ce-4851-b0d3-2c46c81796d6
-- title:
--   Appendix C.1 — canonical Poisson pair, natural filtration and controlled likelihood
-- statement:
--   A **canonical counting path** starts at zero, is nondecreasing and right-continuous, takes values in the natural numbers, and has only unit jumps on bounded time intervals. The path property uses the published simple-counting-process interface. The sample space consists of two such paths, with coordinate-generated sigma algebra and natural filtration. Under the reference probability $P$, increments on disjoint time intervals in both coordinates are independent Poisson variables with mean $\lambda_0$ times the interval length.
--
--   Fix a finite horizon $h\ge0$, bounds $0<\lambda_-\le\lambda_+$ and $0<\lambda_0<\lambda_+$. Admissible controls are all predictable processes with values in $[\lambda_-,\lambda_+]$. Their controlled law is constructed by
--   $$
--   \frac{dP^{a,b}}{dP}=\exp\left(\sum_{0<t\le h:\,\Delta N^a_t=1}\log\frac{a_t}{\lambda_0}+\sum_{0<t\le h:\,\Delta N^b_t=1}\log\frac{b_t}{\lambda_0}-\int_0^h(a_t+b_t-2\lambda_0)\,dt\right).
--   $$
--   Shifted counts are $X^{s,x}_u=x+X_u-X_s$. The Euclidean norm and its actual path supremum define the moment functional in Lemma C.1. This is a controlled point-process interface, independent of the original mission's efficient-price and imbalance model.
--
--   **Formalization Note** Time is nonnegative real; real-time density integrals are composed with the nonnegative-time inclusion. Coordinate 0 is a and coordinate 1 is b. Pre-jump counts use left limits, and initial counts are deterministic shifts. Counts before real time zero have no observable role. The reference law is explicitly the independent Poisson pair, the multivariate point-process convention used by Appendix C; two arbitrary compensated martingales alone would not determine it. The model contains no equilibrium, moment estimate or PDE existence assumption.
-- source:
--   Jusselin, Mastrolia & Rosenbaum, Optimal auction duration: a price formation viewpoint, arXiv:1906.01713v3, https://arxiv.org/abs/1906.01713v3, pp.12,22–24,27, admissible controls, canonical law and Lemma C.1 shift

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Deterministic_CountingProcess

noncomputable section

namespace AuctionDuration.ClearingError.Supplement

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology ENNReal NNReal

/-- General simple nonexplosive paths, using the published counting-process interface. -/
def CountPath := {q : ℝ → ℕ // ∀ T : ℝ, 0 ≤ T →
  NearlyUnstableHawkes.Deterministic.IsCountingProcess T (fun t (_ : Unit) => q t)}

/-- The canonical sample space of two simple counting paths starting at zero. -/
def Sample := Fin 2 → CountPath

/-- Canonical counts. Coordinate 0 is buyer a, coordinate 1 seller b. -/
def X (t : ℝ≥0) (ω : Sample) (i : Fin 2) : ℕ := (ω i).val t

/-- Only the coordinate observations generate the canonical sigma algebra. -/
instance sampleMeasurableSpace : MeasurableSpace Sample :=
  ⨆ t : ℝ≥0, MeasurableSpace.comap (X t) inferInstance

/-- The uncompleted natural filtration of the canonical pair. -/
def naturalFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace Sample) where
  seq t := ⨆ s : ℝ≥0, ⨆ (_ : s ≤ t), MeasurableSpace.comap (X s) inferInstance
  mono' := by
    intro t u htu
    refine iSup_le fun s => iSup_le fun hs => ?_
    exact le_iSup_of_le s (le_iSup_of_le (le_trans hs htu) le_rfl)
  le' t := by
    refine iSup_le fun s => iSup_le fun _ => ?_
    exact le_iSup (fun r : ℝ≥0 => MeasurableSpace.comap (X r) inferInstance) s

/-- Reference law: all increments on successive intervals in both coordinates are
independent Poisson variables. This fixes the independent Poisson pair, rather than
merely specifying two compensators (which would allow common jumps). -/
def IsPoissonPair (rate : ℝ) (P : Measure Sample) : Prop :=
  IsProbabilityMeasure P ∧ ∀ m : ℕ, ∀ t : Fin (m + 1) → ℝ≥0, Monotone t →
    Measure.map (fun ω (j : Fin m × Fin 2) =>
      X (t j.1.succ) ω j.2 - X (t j.1.castSucc) ω j.2) P =
    Measure.pi (fun j : Fin m × Fin 2 => poissonMeasure
      (Real.toNNReal (rate * ((t j.1.succ : ℝ) - (t j.1.castSucc : ℝ)))))

/-- Finite horizon and bounds; no conclusion of any target is part of the data. -/
structure Game where
  h : ℝ
  lower : ℝ
  upper : ℝ
  rate : ℝ
  P : Measure Sample

/-- Appendix C's standing context, also allowing h=0 for Theorem 3.1. -/
def Game.Standing (G : Game) : Prop :=
  0 ≤ G.h ∧ 0 < G.lower ∧ G.lower ≤ G.upper ∧
  0 < G.rate ∧ G.rate < G.upper ∧ IsPoissonPair G.rate G.P

abbrev Process := ℝ≥0 → Sample → ℝ

/-- All predictable bounded controls, without any Markov restriction on deviations. -/
def Game.Admissible (G : Game) (a : Process) : Prop :=
  IsStronglyPredictable naturalFiltration a ∧
  ∀ t : ℝ≥0, ∀ ω, G.lower ≤ a t ω ∧ a t ω ≤ G.upper

/-- Left counts, with initial count zero at t=0. -/
def preX (t : ℝ≥0) (ω : Sample) (i : Fin 2) : ℕ :=
  if t = 0 then 0 else
  ⌊Function.leftLim (fun s : ℝ => ((ω i).val s : ℝ)) (t : ℝ)⌋₊

/-- Actual unit jump times in (0,h]; there are only finitely many on each path. -/
def jumps (h : ℝ) (ω : Sample) (i : Fin 2) : Set ℝ :=
  {t | 0 < t ∧ t ≤ h ∧
    ((ω i).val t : ℝ) - Function.leftLim (fun s : ℝ => ((ω i).val s : ℝ)) t = 1}

/-- Log likelihood on p.23; the Stieltjes integrals are finite sums over jumps. -/
def Game.logLikelihood (G : Game) (a b : Process) (ω : Sample) : ℝ :=
  (∑ᶠ t ∈ jumps G.h ω 0, Real.log (a (Real.toNNReal t) ω / G.rate)) +
  (∑ᶠ t ∈ jumps G.h ω 1, Real.log (b (Real.toNNReal t) ω / G.rate)) -
  ∫ t in Icc (0 : ℝ) G.h,
    (a (Real.toNNReal t) ω - G.rate) + (b (Real.toNNReal t) ω - G.rate)

/-- The controlled measure is constructed from the exponential likelihood, not
an arbitrary measure bearing a prescribed compensator. -/
def Game.law (G : Game) (a b : Process) : Measure Sample :=
  G.P.withDensity (fun ω => ENNReal.ofReal (Real.exp (G.logLikelihood a b ω)))

/-- Counts shifted to start at x at time s. Natural subtraction only removes an
already observed increment, and is nontruncated whenever s ≤ u. -/
def shifted (s u : ℝ≥0) (x : Fin 2 → ℕ) (ω : Sample) (i : Fin 2) : ℕ :=
  x i + (X u ω i - X s ω i)

/-- The paper's norm with subscript 1 is Euclidean, not Manhattan. -/
def countNorm (x : Fin 2 → ℕ) : ℝ :=
  Real.sqrt ((x 0 : ℝ) ^ 2 + (x 1 : ℝ) ^ 2)

/-- The actual path supremum in Lemma C.1. -/
def momentRange (G : Game) (s : ℝ≥0) (x : Fin 2 → ℕ) (ρ : ℝ)
    (ω : Sample) : Set ℝ :=
  {r | ∃ u : ℝ≥0, s ≤ u ∧ (u : ℝ) ≤ G.h ∧
    r = (countNorm (shifted s u x ω)) ^ ρ}

def supremumMoment (G : Game) (s : ℝ≥0) (x : Fin 2 → ℕ) (ρ : ℝ)
    (ω : Sample) : ℝ := sSup (momentRange G s x ρ ω)

end AuctionDuration.ClearingError.Supplement


