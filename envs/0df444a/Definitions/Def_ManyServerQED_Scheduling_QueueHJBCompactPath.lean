-- Prove2me | Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
-- name    : ManyServerQED_Scheduling_QueueHJBCompactPath
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T03:17:58.588636+00:00
-- url     : https://prove2.me/theorems/42e3947d-fb73-4f8a-ab5c-2aeae1b67258
-- title:
--   Joint queue observations for HJB limit paths
-- statement:
--   The joint observation vector contains the centered queue state, the normalized driving noise, the integrated diffusion drift, the discounted accumulated cost, and the discounted accumulated Hamiltonian gap. The subsequence structure records a common probability space, evaluation laws for the row paths, and local uniform convergence to a continuous limit. The five projections name those limit processes.
-- source:
--   Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_HJBCostLimit
import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ManyServerQED.Scheduling

open BellWilliams2001.ThresholdPolicy

/-- The state, normalized noise, accumulated diffusion drift, discounted cost,
and discounted Hamiltonian gap for one queue row. -/
noncomputable def queueHJBObservation {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (γ : ℝ)
    (u0 : Fin k → ℝ) (f : (Fin k → ℝ) → ℝ)
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ) (n : ℕ) (ω : Ω) (t : ℝ) :
    Fin (k+k+k+2) → ℝ :=
  let z := M.Xhat n (X n) ω
  let u := uProc n u0 (X n) (Ψ n) ω
  let D := M.diffData
  let w (i : Fin k) :=
    (M.Ahat n ω t i - M.Shat n ω (busyTime (Ψ n) ω i t/n) i -
      M.Rhat n ω (queueTime (X n) (Ψ n) ω i t/n) i)/D.r i
  let a (i : Fin k) := ∫ s in (0:ℝ)..t, drift D (z s) (u s) i
  let c := ∫ s in (0:ℝ)..t, Real.exp (-γ*s)*L (z s) (u s)
  let g := ∫ s in (0:ℝ)..t, Real.exp (-γ*s) *
    ((∑ i, drift D (z s) (u s) i * grad f (z s) i) + L (z s) (u s) -
      hamiltonian D L (z s) (grad f (z s)))
  Fin.append (Fin.append (Fin.append (z t) w) a) ![c,g]

/-- Jointly represented queue observations on a subsequence, with a continuous
locally uniform limit. The laws are evaluation laws on nonnegative time. -/
structure QueueHJBPathSubseq {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (P : Measure Ω) (Z : ℕ → Ω → ℝ → Fin (k+k+k+2) → ℝ) (s : ℕ → ℕ) where
  Ω' : Type
  [mΩ' : MeasurableSpace Ω']
  Q : Measure Ω'
  isProb : IsProbabilityMeasure Q
  r : ℕ → ℕ
  r_cofinal : Tendsto r atTop atTop
  row : ℕ → Ω' → ℝ → Fin (k+k+k+2) → ℝ
  limit : Ω' → ℝ → Fin (k+k+k+2) → ℝ
  row_law : ∀ᶠ j in atTop,
    IdentDistrib (fun ω (t : ℝ≥0) => row j ω t) (fun ω (t : ℝ≥0) => Z (s (r j)) ω t) Q P
  row_cadlag : ∀ j ω i, IsCadlag (fun t => row j ω t i)
  limit_meas : ∀ t : ℝ≥0, Measurable (fun ω => limit ω t)
  limit_cont : ∀ ω, ContinuousOn (limit ω) (Ici (0:ℝ))
  convergence : ∀ᵐ ω ∂Q, ∀ T : ℝ, 0 ≤ T →
    Tendsto (fun n => supDist (row n ω) (limit ω) T) atTop (𝓝 0)

attribute [instance] QueueHJBPathSubseq.mΩ'

namespace QueueHJBPathSubseq

variable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    {P : Measure Ω} {Z : ℕ → Ω → ℝ → Fin (k+k+k+2) → ℝ} {s : ℕ → ℕ}

/-- Projection onto the limiting queue state. -/
def state (d : QueueHJBPathSubseq P Z s) (t : ℝ≥0) (ω : d.Ω') (i : Fin k) : ℝ :=
  d.limit ω t (Fin.castAdd 2 (Fin.castAdd k (Fin.castAdd k i)))

/-- Projection onto the limiting standardized noise. -/
def noise (d : QueueHJBPathSubseq P Z s) (t : ℝ≥0) (ω : d.Ω') (i : Fin k) : ℝ :=
  d.limit ω t (Fin.castAdd 2 (Fin.castAdd k (Fin.natAdd k i)))

/-- Projection onto the limiting accumulated drift. -/
def driftIntegral (d : QueueHJBPathSubseq P Z s) (t : ℝ≥0) (ω : d.Ω') (i : Fin k) : ℝ :=
  d.limit ω t (Fin.castAdd 2 (Fin.natAdd (k+k) i))

/-- Projection onto the limiting accumulated discounted running cost. -/
def runningCost (d : QueueHJBPathSubseq P Z s) (t : ℝ≥0) (ω : d.Ω') : ℝ :=
  d.limit ω t (Fin.natAdd (k+k+k) (0 : Fin 2))

/-- Projection onto the limiting accumulated discounted Hamiltonian gap. -/
def gap (d : QueueHJBPathSubseq P Z s) (t : ℝ≥0) (ω : d.Ω') : ℝ :=
  d.limit ω t (Fin.natAdd (k+k+k) (1 : Fin 2))

end QueueHJBPathSubseq
end ManyServerQED.Scheduling


