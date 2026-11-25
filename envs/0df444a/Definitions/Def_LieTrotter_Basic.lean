-- Prove2me | Definitions.Def_LieTrotter_Basic
-- name    : LieTrotter_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T15:27:32.666776+00:00
-- url     : https://prove2.me/theorems/736d30fe-4b9e-4864-b53f-858a87be9966
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Zayn Blore (zblore/lie-trotter-lean; see pinned Apache-2.0 LICENSE and source headers)'s pinned Lie-Trotter product formula with commutator-scaling error bound in Banach algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Basic.lean

module
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.NoncommRing
set_option autoImplicit false
@[expose] public section
@[expose] public section
open NormedSpace
namespace LieTrotter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
variable [NormOneClass 𝔸]
end LieTrotter


