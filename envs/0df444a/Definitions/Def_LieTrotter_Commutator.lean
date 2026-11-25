-- Prove2me | Definitions.Def_LieTrotter_Commutator
-- name    : LieTrotter_Commutator
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T15:36:57.416802+00:00
-- url     : https://prove2.me/theorems/ccaa5ac0-b7e5-4d90-b1bc-0655a1af78cb
-- title:
--   Commutator
-- statement:
--   Definitions and structural lemmas for Commutator, from Zayn Blore (zblore/lie-trotter-lean; see pinned Apache-2.0 LICENSE and source headers)'s pinned Lie-Trotter product formula with commutator-scaling error bound in Banach algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/lie-trotter-lean/blob/24e7c036dbef3b6cfd33cff4ed05be7339519fde/LieTrotter/Commutator.lean

module
public import Definitions.Def_LieTrotter_Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
set_option autoImplicit false
@[expose] public section
@[expose] public section
open NormedSpace Set
namespace LieTrotter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
end LieTrotter


