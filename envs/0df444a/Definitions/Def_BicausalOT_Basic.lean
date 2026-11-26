-- Prove2me | Definitions.Def_BicausalOT_Basic
-- name    : BicausalOT_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:32:39.156328+00:00
-- url     : https://prove2.me/theorems/0c018de1-1910-423f-affb-6d442b6e5d4b
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/Basic.lean

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_Proposition1
import Definitions.Def_BicausalOT_LowerBound
import Definitions.Def_BicausalOT_UpperBound
import Definitions.Def_BicausalOT_ValueRepresentation
import Definitions.Def_BicausalOT_Existence
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LowerSemianalytic
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Definitions.Def_BicausalOT_DescriptiveSetTheory_JankovVonNeumann
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Capacitability
import Definitions.Def_BicausalOT_DescriptiveSetTheory_KernelIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_ProbabilityMeasurePolish
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LsaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsCompact
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LintegralLsc
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_DescriptiveSetTheory_EpsOptimalSelection
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_MultiPeriod
import Definitions.Def_BicausalOT_MultiPeriodTopology
import Definitions.Def_BicausalOT_FeasNonempty
import Definitions.Def_BicausalOT_SemianalyticValue
import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_LscBellman
import Definitions.Def_BicausalOT_MeasurableFeasibleStrategy
set_option autoImplicit false


