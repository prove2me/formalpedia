-- Prove2me | Definitions.Def_MazurTransfer_OriginalContinuousCharacterFiniteFieldLevelData20261019
-- name    : MazurTransfer_OriginalContinuousCharacterFiniteFieldLevelData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-20T21:07:26.490899+00:00
-- url     : https://prove2.me/theorems/bafffd4c-2826-40dc-ae85-c88e8b2e6ed2
-- title:
--   Original continuous-character kernel and fixed field
-- statement:
--   Retain the original character kernel as the image of the same genuine continuous character kernel and its original fixed field. Both complete constructor types and whole values are independently compared with the original checked module. Openness and finite dimension are separate theorem statements. Named downstream consumer: the original actual reflected-character finite field level.
-- source:
--   MazurTheorem ContinuousCharacterFiniteFieldLevel by Vas and contributors; original constructor interface with complete original type and whole-value audits, preserving per-file Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a genuine continuous character on a GIVEN open Galois
subgroup, with discrete coefficients, vanishes on the fixing subgroup of
an ACTUAL finite intermediate field. Use its literal open kernel.
Constructor interface; finite-dimensionality is proved separately.
Named downstream consumer: the finite-level input of the checked official
uniform-character theorem for the actual degree-six reflected field.
-/
import Mathlib

noncomputable section
namespace MazurTransfer.ContinuousCharacterFiniteFieldLevel
variable (K M : Type) [Field K] [CharZero K] [IsGalois ℚ K]
  [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [DiscreteTopology M]
local notation "Γ" => K ≃ₐ[ℚ] K

def characterKernel (S : Subgroup Γ) (f : S →ₜ* M) : Subgroup Γ :=
  Subgroup.map S.subtype (MonoidHom.ker f.toMonoidHom)



def characterField (S : Subgroup Γ) (f : S →ₜ* M) : IntermediateField ℚ K :=
  IntermediateField.fixedField (characterKernel K M S f)







end MazurTransfer.ContinuousCharacterFiniteFieldLevel
#print axioms MazurTransfer.ContinuousCharacterFiniteFieldLevel.characterKernel
#print axioms MazurTransfer.ContinuousCharacterFiniteFieldLevel.characterField


