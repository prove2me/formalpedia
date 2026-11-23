-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyTrivialUnitCocycleFaithfullyFlat
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyTrivialUnitCocycleFaithfullyFlat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:47.976477+00:00
-- url     : https://prove2.me/theorems/04740c98-a663-4fd9-8f9a-f8ea76e171b6
-- title:
--   Locally Trivial Unit Cocycle Faithfully Flat
-- statement:
--   Definitions and structural lemmas for Locally Trivial Unit Cocycle Faithfully Flat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocallyTrivialUnitCocycleFaithfullyFlat.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct
namespace GlobalTheory
namespace UnitCocycle
section Tensor
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
variable (R B) in

noncomputable def m₁₂ : B ⊗[R] B →ₐ[R] B ⊗[R] (B ⊗[R] B) :=
  Algebra.TensorProduct.map (AlgHom.id R B) Algebra.TensorProduct.includeLeft
variable (R B) in

noncomputable def m₁₃ : B ⊗[R] B →ₐ[R] B ⊗[R] (B ⊗[R] B) :=
  Algebra.TensorProduct.map (AlgHom.id R B) Algebra.TensorProduct.includeRight
variable (R B) in

noncomputable def m₂₃ : B ⊗[R] B →ₐ[R] B ⊗[R] (B ⊗[R] B) :=
  Algebra.TensorProduct.includeRight
noncomputable def datum (c : B ⊗[R] B) : B →ₗ[B] B ⊗[R] B :=
  LinearMap.toSpanSingleton B _ c
end Tensor
end UnitCocycle
end GlobalTheory


