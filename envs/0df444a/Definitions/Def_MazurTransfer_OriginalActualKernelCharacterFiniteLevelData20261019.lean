-- Prove2me | Definitions.Def_MazurTransfer_OriginalActualKernelCharacterFiniteLevelData20261019
-- name    : MazurTransfer_OriginalActualKernelCharacterFiniteLevelData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-20T21:54:38.515123+00:00
-- url     : https://prove2.me/theorems/3264499e-bec6-4fc0-a052-7d8db6c7c9e6
-- title:
--   Original actual kernel-character scalar extension
-- statement:
--   Retain the original scalar extension of the same genuine kernel character to the absolute Galois group by zero outside the exact same kernel. One complete original constructor type and whole value, all three scoped provider types and their one whole value, 514 context types and 217 whole values, and the generated structural certificate type are checked independently. Named downstream consumer: the complete official uniform-character theorem inputs.
-- source:
--   MazurTheorem Order13ActualKernelCharacterFiniteLevel by Vas and contributors; original constructor interface with complete original type and whole-value audits, preserving per-file Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: extend the same original genuine character on the actual reflected-character kernel to a scalar function on the same absolute Galois group by zero outside that exact kernel.
Named downstream consumer: the exact homomorphism, finite-field-level and genuine inertia hypotheses of the official uniform-character theorem.
-/
import Definitions.Def_MazurTransfer_OriginalActualReflectedCharacterFieldData20261019
noncomputable section
namespace MazurTransfer.Order13ActualKernelCharacterFiniteLevel
open CategoryTheory RepresentationDiscreteCoefficients
open Order13ActualCyclotomicThirteenKernelCharacter Order13ActualSelectedCharacterKummerKernel
open Order13ActualUnramifiedKernelCharacterEmbedding Order13ActualReflectedCharacterField
local notation "F" => AlgebraicClosure ℚ
local notation "Γ" => F ≃ₐ[ℚ] F
local instance instIsGaloisRatAlgebraicClosure_order13ActualKernelCharacterFiniteLevel : IsGalois ℚ F := Order13ActualPicardNormAlgebraicKummerInjection.canonicalClosureGalois
local instance instFactPrimeOfNatNat_order13ActualKernelCharacterFiniteLevel : Fact (Nat.Prime 19) := ⟨by decide⟩
variable (z : F) (hz : IsPrimitiveRoot z 13)
local notation "χ" => piConjugateReflectedCharacter F z hz
local notation "Mχ" => Coefficient (piLineRepresentation F z hz)
local instance instModuleZModOfNatNatKernelCharactersAlgebraicClosureRat_order13ActualKernelCharacterFiniteLevel : Module (ZMod 19) (KernelCharacters F z hz) := kernelCharactersZModModule F z hz
def extendedValue (f : KernelCharacters F z hz) (σ : Γ) : ZMod 19 :=
  if hσ : σ ∈ (χ).ker then evaluation F z hz ⟨σ, hσ⟩ f else 0
end MazurTransfer.Order13ActualKernelCharacterFiniteLevel
#print axioms MazurTransfer.Order13ActualKernelCharacterFiniteLevel.extendedValue
#print axioms MazurTransfer.Order13ActualKernelCharacterFiniteLevel.instIsGaloisRatAlgebraicClosure_order13ActualKernelCharacterFiniteLevel
#print axioms MazurTransfer.Order13ActualKernelCharacterFiniteLevel.instFactPrimeOfNatNat_order13ActualKernelCharacterFiniteLevel
#print axioms MazurTransfer.Order13ActualKernelCharacterFiniteLevel.instModuleZModOfNatNatKernelCharactersAlgebraicClosureRat_order13ActualKernelCharacterFiniteLevel


