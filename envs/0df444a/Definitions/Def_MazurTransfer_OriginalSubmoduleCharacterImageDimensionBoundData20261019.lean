-- Prove2me | Definitions.Def_MazurTransfer_OriginalSubmoduleCharacterImageDimensionBoundData20261019
-- name    : MazurTransfer_OriginalSubmoduleCharacterImageDimensionBoundData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T13:27:12.86712+00:00
-- url     : https://prove2.me/theorems/d2ecbc28-ff03-483a-893e-9e74b9028627
-- title:
--   Original restricted quotient and character-kernel linear maps
-- statement:
--   For linear maps f from V to W and i from A to V, retain the original restriction of f to a subspace E and the original map of its restricted kernel into i(C), with kernel coverage explicitly supplied. Both whole linear-map constructor values and every generated structural helper are checked against the original module. Named downstream consumer: the character-image dimension bound and the actual pi norm Kummer image estimate.
-- source:
--   MazurTheorem SubmoduleCharacterImageDimensionBound by Vas and contributors; original linear-map constructor bodies and per-file Apache-2.0 attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: original restriction of a given linear quotient map to a source subspace and original kernel map into a character subspace, with kernel coverage as an explicit input.
Named downstream consumer: the original character-image finite-dimension theorem and actual pi norm Kummer image bound.
-/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: bound a given source subspace using a given quotient
image and a given character subspace covering its kernel. Finite-
dimensionality of those two bounding spaces is an explicit input.
Named downstream consumer: the ORIGINAL pi norm Kummer quotient estimate
from its checked selected character image and unramified kernel lifts.
-/
import Mathlib

noncomputable section
namespace MazurTransfer.SubmoduleCharacterImageDimensionBound
variable {k A V W : Type} [Field k]
  [AddCommGroup A] [Module k A] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

def restrictedQuotient (E : Submodule k V) (f : V →ₗ[k] W) : E →ₗ[k] W := f.comp E.subtype

def characterKernelMap (E : Submodule k V) (f : V →ₗ[k] W) (i : A →ₗ[k] V) (C : Submodule k A)
    (hker : ∀ x : E, f x.val = 0 → x.val ∈ C.map i) :
    LinearMap.ker (restrictedQuotient E f) →ₗ[k] C.map i :=
  ((E.subtype).comp (LinearMap.ker (restrictedQuotient E f)).subtype).codRestrict (C.map i)
    (fun x => hker x.val x.property)





end MazurTransfer.SubmoduleCharacterImageDimensionBound
#print axioms MazurTransfer.SubmoduleCharacterImageDimensionBound.restrictedQuotient
#print axioms MazurTransfer.SubmoduleCharacterImageDimensionBound.characterKernelMap


