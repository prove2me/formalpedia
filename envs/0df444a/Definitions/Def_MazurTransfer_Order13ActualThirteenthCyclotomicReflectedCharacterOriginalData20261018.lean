-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualThirteenthCyclotomicReflectedCharacterOriginalData20261018
-- name    : MazurTransfer_Order13ActualThirteenthCyclotomicReflectedCharacterOriginalData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T23:34:57.592104+00:00
-- url     : https://prove2.me/theorems/364e7d23-1260-44aa-9562-117a5fcfa2e7
-- title:
--   Original actual reflected thirteenth-cyclotomic Galois characters
-- statement:
--   The two original reflected characters compose the explicit inverse F19-valued unit characters with the primitive-thirteenth-root Galois power map. Both full declaration types and both whole values agree with the original source. Named downstream consumer: the arithmetic-character action on the actual norm quotient kernels and its exact order-six image. Character actions and image orders remain separate theorem contracts.
-- source:
--   MazurTheorem Order13ActualCyclotomicThirteenKernelCharacter, the original two character definitions; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the SAME actual cyclotomic quotient kernel has an explicit
arithmetic13 character of exact order six, with both factor orderings kept.
The Galois power map is for the literal primitive thirteenth root.
Named downstream consumer: complete norm representation exact sequences
and the exceptional-prime local Kummer and Selmer arguments.
-/
import Mathlib
import Definitions.Def_MazurTransfer_ThirteenToNineteenOriginalCharacterDataAndConstructorCertificates20261018
noncomputable section
namespace MazurTransfer.Order13ActualCyclotomicThirteenKernelCharacter
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
open MazurTransfer.ThirteenToNineteenCharacters
def piReflectedCharacter (z : K) (hz : IsPrimitiveRoot z 13) : (K ≃ₐ[ℚ] K) →* (ZMod 19)ˣ :=
  character.comp (hz.autToPow ℚ)

def piConjugateReflectedCharacter (z : K) (hz : IsPrimitiveRoot z 13) : (K ≃ₐ[ℚ] K) →* (ZMod 19)ˣ :=
  conjugateCharacter.comp (hz.autToPow ℚ)

end MazurTransfer.Order13ActualCyclotomicThirteenKernelCharacter
#print axioms MazurTransfer.Order13ActualCyclotomicThirteenKernelCharacter.piReflectedCharacter
#print axioms MazurTransfer.Order13ActualCyclotomicThirteenKernelCharacter.piConjugateReflectedCharacter


