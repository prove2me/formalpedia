-- Prove2me | Definitions.Def_SampleDrivenOS_Structure_Supplement_Thresholds
-- name    : SampleDrivenOS_Structure_Supplement_Thresholds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:40:36.296693+00:00
-- url     : https://prove2.me/theorems/932e9e08-62a1-49f7-acff-b84d0c94c97c
-- title:
--   Threshold execution, SDRP objective and rank-limit integrals
-- statement:
--   Let 0≤p<1 and let t₀=p≤t₁≤t₂≤⋯≤1. The full threshold objective is
--   $$
--   v_p(t)=\inf_{k\ge1}\frac{F_k(\operatorname{thresholdQ}(t))}{1-p^k}.
--   $$
--   The published F_k and thresholdQ are reused. A threshold optimizer maximizes this objective over all such infinite sequences; no hypothesis about finite performance is part of being an optimizer.
--
--   Give each of the N globally ranked items an independent uniform clock in [0,1]. Items before p form the history. ALG_t accepts the first online item whose current relative rank ℓ satisfies t_ℓ≤τ at its arrival time τ. First-item selection is computed from the qualifying items and their earliest clock, with the fixed global rank breaking equal-clock ties. If no item qualifies, the reward is 0. The finite competitive ratio β_{N,p}(t) is the infimum of its actual expected reward divided by the actual expected offline maximum over every nonnegative decreasing weight vector with positive offline expectation.
--
--   For a fixed global rank j, define the limiting integral terms
--   $$
--   L_{j,i}(t)=\int_{t_i}^{t_{i+1}}\sum_{\ell=1}^{\min(j,i)}
--   \frac{T_i}{\tau^i}\binom{j-1}{\ell-1}(1-\tau)^{j-\ell}\tau^{\ell-1}\,d\tau,
--   \qquad T_i=\prod_{r=1}^{i}t_r.
--   $$
--   The event of selecting global rank j is distinct from numerical equality to Y_j when weights tie. Lemma 11 supplies integrability, summability and its probability limit.
--
--   These objects connect the continuous threshold representation to finite algorithmic rewards. The arrival law is a product measure, not a prescribed limiting selection distribution.
--
--   **Formalization Note** The interval [p,1] can replace (p,1] in the clock execution because endpoints have probability zero. The algorithms and their rewards are Borel functions obtained by finitely many comparisons and choices. Their bounded finite ranges imply integrability. The real objective infimum is over a nonempty set of nonnegative values for feasible thresholds. The full infinite rank range is retained.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 11, §3.4; p. 15, SDRP_p; p. 18, §4.4 and Lemma 11

import Mathlib
import Definitions.Def_SampleDrivenOS_Structure_Supplement_Experiments
import Definitions.Def_SampleDrivenOS_Limit_Setting

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace SampleDrivenOS.Structure.Supplement

noncomputable section
open Classical

/-- The unused index 0 is set to p, following the book-wide convention. -/
def IsThresholds (p : ℝ) (t : ℕ → ℝ) : Prop :=
  t 0 = p ∧ Monotone t ∧ ∀ i, p ≤ t i ∧ t i ≤ 1

def thresholdObjective (p : ℝ) (t : ℕ → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ k : ℕ, 1 ≤ k ∧
    r = SampleDrivenOS.Structure.Fk p (SampleDrivenOS.Limit.thresholdQ t) k / (1 - p ^ k)}

/-- An optimizer premise refers only to the full SDRP objective, not to finite algorithm
performance or to the equality between sampling models. -/
def IsOptimalThresholds (p : ℝ) (t : ℕ → ℝ) : Prop :=
  IsThresholds p t ∧ ∀ s : ℕ → ℝ, IsThresholds p s →
    thresholdObjective p s ≤ thresholdObjective p t

/-- Independent uniform [0,1] clocks, one for every globally ranked item. -/
def arrivalLaw (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi (fun _ : Fin N => volume.restrict (Icc (0 : ℝ) 1))

/-- First eligible item in time. Equal clocks are resolved by the fixed global rank order;
this zero-probability convention does not use numerical equality of weights. -/
def firstItem {N : ℕ} (A : Finset (Fin N)) (u : Fin N → ℝ) : Option (Fin N) :=
  let B := A.filter (fun a => ∀ b ∈ A, u a ≤ u b)
  if h : B.Nonempty then some (B.min' h) else none

/-- Current relative rank includes sampled items (their clocks are before p). -/
def clockRank {N : ℕ} (u : Fin N → ℝ) (a : Fin N) : ℕ :=
  1 + (Finset.univ.filter (fun b : Fin N => b < a ∧ u b ≤ u a)).card

/-- Executable ALG_t: the first online item whose current rank threshold is reached.
An empty candidate set means no stop and zero adversarial reward. -/
def thresholdChoice (N : ℕ) (p : ℝ) (t : ℕ → ℝ) (u : Fin N → ℝ) : Option (Fin N) :=
  firstItem (Finset.univ.filter (fun a => p ≤ u a ∧ t (clockRank u a) ≤ u a)) u

def thresholdReward (N : ℕ) (p : ℝ) (t : ℕ → ℝ) (w : Fin N → ℝ) : ℝ :=
  ∫ u, (thresholdChoice N p t u).elim 0 w ∂arrivalLaw N

def clockOffline {N : ℕ} (p : ℝ) (w : Fin N → ℝ) (u : Fin N → ℝ) : ℝ :=
  (insert 0 ((Finset.univ.filter (fun a => p ≤ u a)).image w)).max' (by simp)

def clockOfflineMean {N : ℕ} (p : ℝ) (w : Fin N → ℝ) : ℝ :=
  ∫ u, clockOffline p w u ∂arrivalLaw N

def thresholdRatio (N : ℕ) (p : ℝ) (t : ℕ → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ w : Fin N → ℝ, IsWeights w ∧ 0 < clockOfflineMean p w ∧
    r = thresholdReward N p t w / clockOfflineMean p w}

/-- j is a 1-based fixed global rank; it is not the event that the selected numerical value
coincides with the j-th value. The event is empty for N<j. -/
def selectionProbability (N : ℕ) (p : ℝ) (t : ℕ → ℝ) (j : ℕ) : ℝ :=
  (∫⁻ u, (if ∃ a : Fin N, a.val + 1 = j ∧ thresholdChoice N p t u = some a
    then (1 : ENNReal) else 0) ∂arrivalLaw N).toReal

/-- The i-th integral of Lemma 11, i≥1; the published threshold product is reused. -/
def rankLimitIntegrand (t : ℕ → ℝ) (j i : ℕ) (τ : ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc 1 (min j i), SampleDrivenOS.Structure.thresholdProd t i / τ ^ i *
    ((j - 1).choose (ℓ - 1) : ℝ) * (1 - τ) ^ (j - ℓ) * τ ^ (ℓ - 1)

def rankLimitTerm (t : ℕ → ℝ) (j i : ℕ) : ℝ :=
  ∫ τ in t i..t (i + 1), rankLimitIntegrand t j i τ

end
end SampleDrivenOS.Structure.Supplement


