-- Prove2me | Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
-- name    : LeanPool_NemytskiiLebesgue_Caratheodory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:33:06.74832+00:00
-- url     : https://prove2.me/theorems/6d23bd41-7187-4c0a-bf81-ed73c81994b6
-- title:
--   Caratheodory
-- statement:
--   Definitions and structural lemmas for Caratheodory, from Petr Girg; Petr Nečesal; Martin Dvořák; Jakub Psutka; LeanPool contributors's pinned Nemytskii operators on Lebesgue spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Caratheodory.lean

module
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Basic
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory TopologicalSpace Filter
open scoped Topology
structure IsCaratheodory {Ω D F : Type*}
    [MeasurableSpace Ω] [TopologicalSpace D] [TopologicalSpace F]
    (f : Ω → D → F) (μ : Measure Ω) :
    Prop where
  isStronglyMeasurable : ∀ x : D, StronglyMeasurable (f · x)
  ae_continuous : ∀ᵐ ω : Ω ∂μ, Continuous (f ω)
end NemytskiiLebesgue


