-- Prove2me | Definitions.Def_SampleDrivenOS_Structure_Supplement_Partitions
-- name    : SampleDrivenOS_Structure_Supplement_Partitions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:43:31.990799+00:00
-- url     : https://prove2.me/theorems/d4df09c6-f063-469e-82d3-d44a78f43600
-- title:
--   Sampled offline optimum and the full sample partition property
-- statement:
--   Let the ground set have N elements, including possibly N=0. Its independent family I contains the empty set and is hereditary; the published general independence-system predicate is reused. For nonnegative weights Y, write
--   $$
--   \operatorname{OPT}(I,q,Y)=\mathbb E_{S[q]}\max_{X\subseteq S[q],\ X\in I}\sum_{e\in X}Y(e),
--   $$
--   where each element belongs to S[q] independently with probability q. The expectation is an explicit finite sum over subsets, with their Bernoulli probabilities.
--
--   A unit partition is a coloring of the ground set. Color 0 is forbidden, and at most one element can be chosen in each nonzero color class. Its independent family specializes the published general partition-matroid feasibility predicate to capacities 0 and 1. Only nonempty nonzero fibers are called allowed parts; unused labels are not additional empty parts.
--
--   One partition distribution L is chosen independently of weights, sampling and arrival times. It has the γ sample partition property when every independent set in every partition of positive mass belongs to I and, for every q∈[0,1] and every nonnegative weight assignment,
--   $$
--   \mathbb E_{P\sim L}\operatorname{OPT}(P,q,Y)\ge\gamma\operatorname{OPT}(I,q,Y).
--   $$
--   The universal quantification over q is essential. These objects allow arbitrary independence systems, not just matroids, and arbitrary random partition laws on a finite ground set.
--
--   **Formalization Note** Partitions are encoded by colors in `Fin (N+1)`; positive labels outside the image are ignored. Every unit partition of N elements has such a labeling. Finite probability mass functions make independence from clocks and weights explicit through the separate product expectation. The empty ground set has a unique coloring, empty output and zero sampled optimum.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, pp. 19–21, footnote 20, OPT(I,q,Y), §5.2 sample partition property

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsIndepSystem
import Definitions.Def_SeqPostedPricing_PartitionSPM_partitionFeasible
import Definitions.Def_SampleDrivenOS_Structure_Supplement_Thresholds

open MeasureTheory Set
open scoped BigOperators

namespace SampleDrivenOS.Structure.Supplement

noncomputable section
open Classical

/-- Zero labels the forbidden part. Positive labels in the image are exactly the nonempty
allowed parts; unused labels do not designate parts. Every finite unit partition is represented. -/
abbrev UnitPartition (N : ℕ) := Fin N → Fin (N + 1)

/-- Specialize the published general partition matroid to capacity 0 on part 0 and 1 elsewhere. -/
def PartitionIndependent {N : ℕ} (c : UnitPartition N) (X : Finset (Fin N)) : Prop :=
  SeqPostedPricing.PartitionSPM.partitionFeasible c (fun b => if b = 0 then 0 else 1) X

def setWeight {N : ℕ} (w : Fin N → ℝ) (X : Finset (Fin N)) : ℝ := ∑ a ∈ X, w a

/-- Actual maximum over the finite independent subsets of the sampled set. -/
def offlineSet {N : ℕ} (I : Finset (Fin N) → Prop) (w : Fin N → ℝ)
    (S : Finset (Fin N)) : ℝ :=
  (insert 0 ((S.powerset.filter I).image (setWeight w))).max' (by simp)

/-- Offline sampled optimum OPT(I,q,Y), including the Bernoulli sampling probabilities. -/
def sampledOpt {N : ℕ} (I : Finset (Fin N) → Prop) (q : ℝ) (w : Fin N → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
    q ^ S.card * (1 - q) ^ (N - S.card) * offlineSet I w S

/-- An arbitrary distribution on the finite collection of labelled unit partitions. It is
chosen once, independently of weights, history and all arrival clocks. -/
structure PartitionLaw (N : ℕ) where
  mass : UnitPartition N → ℝ
  nonneg : ∀ c, 0 ≤ mass c
  total : ∑ c : UnitPartition N, mass c = 1

/-- The full sample partition property, for every sampling rate q and every nonnegative
weight assignment. The original independence system need not be a matroid. -/
def HasSamplePartition {N : ℕ} (I : Finset (Fin N) → Prop) (γ : ℝ)
    (L : PartitionLaw N) : Prop :=
  (∀ c, 0 < L.mass c → ∀ X, PartitionIndependent c X → I X) ∧
  ∀ q ∈ Icc (0 : ℝ) 1, ∀ w : Fin N → ℝ, (∀ a, 0 ≤ w a) →
    γ * sampledOpt I q w ≤
      ∑ c : UnitPartition N, L.mass c * sampledOpt (PartitionIndependent c) q w

end
end SampleDrivenOS.Structure.Supplement


