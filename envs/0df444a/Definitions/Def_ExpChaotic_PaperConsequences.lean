-- Prove2me | Definitions.Def_ExpChaotic_PaperConsequences
-- name    : ExpChaotic_PaperConsequences
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:00:55.829407+00:00
-- url     : https://prove2.me/theorems/93f1fbed-286a-43ea-ab43-dd7018c0c1ee
-- title:
--   Paper Consequences
-- statement:
--   Definitions and structural lemmas for Paper Consequences, from Lasse Rempe (LR-UK/exp-chaotic; initial proof architecture adapted under HOL Light BSD-style licence from John Harrison Examples/misiurewicz.ml per THIRD_PARTY_NOTICES.md; original Lean code Apache-2.0)'s pinned The complex exponential map is chaotic and Misiurewicz's theorem (Julia set equals C) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/PaperConsequences.lean

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Interval.Set.Infinite
import Definitions.Def_ExpChaotic_Dynamics
set_option autoImplicit true
open Function Filter Set Metric
namespace ExponentialJuliaSetMisiurewicz
noncomputable section
end
end ExponentialJuliaSetMisiurewicz


