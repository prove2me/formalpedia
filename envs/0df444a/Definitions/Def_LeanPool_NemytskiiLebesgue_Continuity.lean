-- Prove2me | Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
-- name    : LeanPool_NemytskiiLebesgue_Continuity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:33:31.119324+00:00
-- url     : https://prove2.me/theorems/e6d6827d-c36f-410a-beb3-d7024ab0a5bd
-- title:
--   Continuity
-- statement:
--   Definitions and structural lemmas for Continuity, from Petr Girg; Petr Nečesal; Martin Dvořák; Jakub Psutka; LeanPool contributors's pinned Nemytskii operators on Lebesgue spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Continuity.lean

module
public import Mathlib.MeasureTheory.Function.UnifTight
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal Topology
@[expose] def _root_.Function.NemytskiiConvergesTo
    {Ω : Type*} [MeasurableSpace Ω]
    {D : Type*} [NormedAddCommGroup D]
    (f : ℕ → Ω → D) (g : Ω → D) (p : ℝ≥0∞) (μ : Measure Ω) :
    Prop :=
  Tendsto (fun n : ℕ => eLpNorm (f n - g) p μ) atTop (𝓝 0)
end NemytskiiLebesgue


