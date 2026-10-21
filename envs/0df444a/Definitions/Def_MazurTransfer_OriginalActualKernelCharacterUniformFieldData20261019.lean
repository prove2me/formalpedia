-- Prove2me | Definitions.Def_MazurTransfer_OriginalActualKernelCharacterUniformFieldData20261019
-- name    : MazurTransfer_OriginalActualKernelCharacterUniformFieldData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-20T22:38:48.724987+00:00
-- url     : https://prove2.me/theorems/c90d6ef5-f17f-45b8-9b98-fb5bb2b70ecd
-- title:
--   Original chosen uniform arithmetic character field
-- statement:
--   Choose the original common field from the separately accepted exact original uniform existence theorem. Independently check its complete constructor type and whole choice value, all three original scoped provider types and their one whole value, 518 context types and 219 whole values, and the complete original existence proof type used for choice. Named downstream consumer: unconditional finiteness of the original arithmetic character conditions.
-- source:
--   MazurTheorem Order13ActualKernelCharacterUniformLevel by Vas and contributors; original constructor interface with complete original type and whole-value audits, preserving per-file Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: choose the original common finite field from the separately accepted exact original uniform existence theorem. Preserve the same arithmetic character family and classical choice construction.
Named downstream consumer: unconditional finiteness of the original arithmetic kernel-character conditions and unramified reflected-character classes.
-/
import Definitions.Def_MazurTransfer_OriginalActualKernelCharacterFiniteLevelData20261019
import Theorems.Thm_MazurTransfer_original_actual_kernel_character_uniform_field_exists
noncomputable section
namespace MazurTransfer.Order13ActualKernelCharacterUniformLevel
open CategoryTheory RepresentationDiscreteCoefficients
open Order13ActualCyclotomicThirteenKernelCharacter Order13ActualSelectedCharacterKummerKernel
open Order13ActualUnramifiedKernelCharacterEmbedding Order13ActualReflectedCharacterField Order13ActualKernelCharacterFiniteLevel
local notation "F" => AlgebraicClosure ℚ
local notation "Γ" => F ≃ₐ[ℚ] F
local instance instIsGaloisRatAlgebraicClosure_order13ActualKernelCharacterUniformLevel : IsGalois ℚ F := Order13ActualPicardNormAlgebraicKummerInjection.canonicalClosureGalois
local instance instFactPrimeOfNatNat_order13ActualKernelCharacterUniformLevel : Fact (Nat.Prime 19) := ⟨by decide⟩
variable (z : F) (hz : IsPrimitiveRoot z 13)
local notation "χ" => piConjugateReflectedCharacter F z hz
local instance instModuleZModOfNatNatKernelCharactersAlgebraicClosureRat_order13ActualKernelCharacterUniformLevel : Module (ZMod 19) (KernelCharacters F z hz) := kernelCharactersZModModule F z hz
def uniformField : IntermediateField ℚ F := Classical.choose (MazurTransfer.original_actual_kernel_character_uniform_field_exists z hz)
end MazurTransfer.Order13ActualKernelCharacterUniformLevel
#print axioms MazurTransfer.Order13ActualKernelCharacterUniformLevel.uniformField
#print axioms MazurTransfer.Order13ActualKernelCharacterUniformLevel.instIsGaloisRatAlgebraicClosure_order13ActualKernelCharacterUniformLevel
#print axioms MazurTransfer.Order13ActualKernelCharacterUniformLevel.instFactPrimeOfNatNat_order13ActualKernelCharacterUniformLevel
#print axioms MazurTransfer.Order13ActualKernelCharacterUniformLevel.instModuleZModOfNatNatKernelCharactersAlgebraicClosureRat_order13ActualKernelCharacterUniformLevel


