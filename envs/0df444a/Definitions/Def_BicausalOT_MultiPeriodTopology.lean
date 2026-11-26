-- Prove2me | Definitions.Def_BicausalOT_MultiPeriodTopology
-- name    : BicausalOT_MultiPeriodTopology
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:09:38.932918+00:00
-- url     : https://prove2.me/theorems/7bdc1d45-991c-50b9-8c53-b35240ed96b1
-- title:
--   Multi Period Topology
-- statement:
--   Definitions and structural lemmas for Multi Period Topology, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MultiPeriodTopology.lean

import Definitions.Def_BicausalOT_MultiPeriod
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace MultiPeriod
variable (X Y : ℕ → Type*)
section Topology
variable [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
instance instTopologicalSpacePairHist : ∀ t, TopologicalSpace (PairHist X Y t)
  | 0 => inferInstanceAs (TopologicalSpace (X 0 × Y 0))
  | t + 1 =>
    letI := instTopologicalSpacePairHist t
    inferInstanceAs
      (TopologicalSpace (PairHist X Y t × (X (t + 1) × Y (t + 1))))
instance instTopologicalSpaceXHist : ∀ t, TopologicalSpace (XHist X t)
  | 0 => inferInstanceAs (TopologicalSpace (X 0))
  | t + 1 =>
    letI := instTopologicalSpaceXHist t
    inferInstanceAs (TopologicalSpace (XHist X t × X (t + 1)))
instance instTopologicalSpaceYHist : ∀ t, TopologicalSpace (YHist Y t)
  | 0 => inferInstanceAs (TopologicalSpace (Y 0))
  | t + 1 =>
    letI := instTopologicalSpaceYHist t
    inferInstanceAs (TopologicalSpace (YHist Y t × Y (t + 1)))
variable {X Y}
end Topology
section Polish
variable [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
variable [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
instance instPolishSpacePairHist : ∀ t, PolishSpace (PairHist X Y t)
  | 0 => inferInstanceAs (PolishSpace (X 0 × Y 0))
  | t + 1 =>
    letI := instPolishSpacePairHist t
    inferInstanceAs (PolishSpace (PairHist X Y t × (X (t + 1) × Y (t + 1))))
instance instPolishSpaceXHist : ∀ t, PolishSpace (XHist X t)
  | 0 => inferInstanceAs (PolishSpace (X 0))
  | t + 1 =>
    letI := instPolishSpaceXHist t
    inferInstanceAs (PolishSpace (XHist X t × X (t + 1)))
instance instPolishSpaceYHist : ∀ t, PolishSpace (YHist Y t)
  | 0 => inferInstanceAs (PolishSpace (Y 0))
  | t + 1 =>
    letI := instPolishSpaceYHist t
    inferInstanceAs (PolishSpace (YHist Y t × Y (t + 1)))
end Polish
section Measurable
variable [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
instance instMeasurableSpacePairHist : ∀ t, MeasurableSpace (PairHist X Y t)
  | 0 => inferInstanceAs (MeasurableSpace (X 0 × Y 0))
  | t + 1 =>
    letI := instMeasurableSpacePairHist t
    inferInstanceAs
      (MeasurableSpace (PairHist X Y t × (X (t + 1) × Y (t + 1))))
instance instMeasurableSpaceXHist : ∀ t, MeasurableSpace (XHist X t)
  | 0 => inferInstanceAs (MeasurableSpace (X 0))
  | t + 1 =>
    letI := instMeasurableSpaceXHist t
    inferInstanceAs (MeasurableSpace (XHist X t × X (t + 1)))
instance instMeasurableSpaceYHist : ∀ t, MeasurableSpace (YHist Y t)
  | 0 => inferInstanceAs (MeasurableSpace (Y 0))
  | t + 1 =>
    letI := instMeasurableSpaceYHist t
    inferInstanceAs (MeasurableSpace (YHist Y t × Y (t + 1)))
variable {X Y}
end Measurable
section Borel
variable [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
variable [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
variable [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
variable [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
instance instBorelSpacePairHist : ∀ t, BorelSpace (PairHist X Y t)
  | 0 => inferInstanceAs (BorelSpace (X 0 × Y 0))
  | t + 1 =>
    letI := instBorelSpacePairHist t
    inferInstanceAs (BorelSpace (PairHist X Y t × (X (t + 1) × Y (t + 1))))
instance instBorelSpaceXHist : ∀ t, BorelSpace (XHist X t)
  | 0 => inferInstanceAs (BorelSpace (X 0))
  | t + 1 =>
    letI := instBorelSpaceXHist t
    inferInstanceAs (BorelSpace (XHist X t × X (t + 1)))
instance instBorelSpaceYHist : ∀ t, BorelSpace (YHist Y t)
  | 0 => inferInstanceAs (BorelSpace (Y 0))
  | t + 1 =>
    letI := instBorelSpaceYHist t
    inferInstanceAs (BorelSpace (YHist Y t × Y (t + 1)))
end Borel
end MultiPeriod
end


