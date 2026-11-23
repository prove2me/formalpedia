-- Prove2me | Definitions.Def_SampleDrivenOS_Structure_Supplement_Parallel
-- name    : SampleDrivenOS_Structure_Supplement_Parallel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:44:34.590709+00:00
-- url     : https://prove2.me/theorems/48d268eb-c87d-4622-b7ad-1cb9ff572af0
-- title:
--   The parallel threshold algorithm on a sampled partition
-- statement:
--   Fix a partition P, a sample rate p, and a threshold sequence t. Give all ground-set elements the same family of independent uniform arrival clocks. Within each allowed part, rank the observed elements by weight using a fixed index tie-break, include the part's sample items when computing ranks, and run ALG_t. The parallel output is the union of the first qualifying online items selected in each allowed part. The forbidden part contributes no item.
--
--   For a partition law L, its expected realized reward is
--   $$
--   \mathbb E_{P\sim L}\mathbb E_U\sum_{e\in\operatorname{ALG}(P,U,Y)}Y(e).
--   $$
--   The partition, the sample and the shared arrival order are averaged, not replaced by arbitrary reward parameters. The same law and thresholds are used for every weight assignment. `ParallelCompetitive` asserts the expected-reward inequality for this specific algorithm for all nonnegative weights.
--
--   This is precisely the algorithm whose guarantee is asserted in Theorem 15. It makes no assumption on the sizes of allowed parts.
--
--   **Formalization Note** Weight comparisons determine relative ranks only. Clock ties use the existing first-item convention; they have probability zero. Each part's first acceptable item is an adapted irrevocable decision, although the finite output is expressed as a first-element function on the full clock vector. The bounded output weight is integrable.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 22, algorithm preceding Theorem 15

import Definitions.Def_SampleDrivenOS_Structure_Supplement_Partitions

open MeasureTheory
open scoped BigOperators

namespace SampleDrivenOS.Structure.Supplement
noncomputable section
open Classical

/-- Global weight order with one fixed index tie-break, used only through relative ranks. -/
def Better {N : ℕ} (w : Fin N → ℝ) (b a : Fin N) : Prop :=
  w a < w b ∨ (w b = w a ∧ b < a)

/-- Relative rank within this part among the elements already observed, including its sample. -/
def partRank {N : ℕ} (c : UnitPartition N) (w : Fin N → ℝ)
    (u : Fin N → ℝ) (a : Fin N) : ℕ :=
  1 + (Finset.univ.filter (fun b : Fin N => c b = c a ∧ Better w b a ∧ u b ≤ u a)).card

/-- Parallel execution of ALG_t on the nonzero parts, sharing the global clocks and sample.
The first eligible item in each part is selected, irrevocably, when it arrives. -/
def parallelOutput {N : ℕ} (p : ℝ) (t : ℕ → ℝ) (c : UnitPartition N)
    (w : Fin N → ℝ) (u : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun a => c a ≠ 0 ∧
    firstItem (Finset.univ.filter (fun b => c b = c a ∧ p ≤ u b ∧
      t (partRank c w u b) ≤ u b)) u = some a)

def parallelMean {N : ℕ} (p : ℝ) (t : ℕ → ℝ) (L : PartitionLaw N)
    (w : Fin N → ℝ) : ℝ :=
  ∑ c : UnitPartition N, L.mass c *
    ∫ u, setWeight w (parallelOutput p t c w u) ∂arrivalLaw N

/-- Expected-reward competitiveness of this particular parallel algorithm for all weights. -/
def ParallelCompetitive {N : ℕ} (I : Finset (Fin N) → Prop) (p : ℝ)
    (t : ℕ → ℝ) (L : PartitionLaw N) (ρ : ℝ) : Prop :=
  ∀ w : Fin N → ℝ, (∀ a, 0 ≤ w a) →
    ρ * sampledOpt I (1 - p) w ≤ parallelMean p t L w

end
end SampleDrivenOS.Structure.Supplement


