-- Prove2me | Definitions.Def_BrownianMotion_Auxiliary_Topology_F000
-- name    : BrownianMotion_Auxiliary_Topology_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:06:44.967887+00:00
-- url     : https://prove2.me/theorems/ef6a946e-3896-4c5e-9c3a-c05452609ea4
-- title:
--   Source declarations: BrownianMotion.Auxiliary.Topology
-- statement:
--   Source-preserving Lean declaration bundle from BrownianMotion.Auxiliary.Topology, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Topology.MetricSpace.HolderNorm


@[expose] public section

open Bornology Filter

open scoped NNReal ENNReal Topology

lemma eventually_nhdsGT {α : Type*} [TopologicalSpace α] [LinearOrder α] [ClosedIciTopology α]
    {a b : α} (hab : a < b) {p : α → Prop} (h : ∀ x ∈ Set.Ioc a b, p x) :
    ∀ᶠ x in 𝓝[>] a, p x :=
  sets_of_superset (x := Set.Ioo a b) _ (Ioo_mem_nhdsGT hab) (by grind)
variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [CompleteSpace Y]
    {C r : ℝ≥0} {s : Set X} {f : s → Y}

lemma neBot_comap_nhds (hs : Dense s) (x : X) : ((𝓝 x).comap ((↑) : s → X)).NeBot :=
  hs.isDenseInducing_val.comap_nhds_neBot _


