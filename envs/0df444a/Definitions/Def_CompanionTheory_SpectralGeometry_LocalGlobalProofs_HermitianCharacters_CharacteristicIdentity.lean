-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_CharacteristicIdentity
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_CharacteristicIdentity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:49:08.224191+00:00
-- url     : https://prove2.me/theorems/ca8356a9-cedf-4873-aab3-de39b7f9904e
-- title:
--   Characteristic Identity
-- statement:
--   Definitions and structural lemmas for Characteristic Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/HermitianCharacters/CharacteristicIdentity.lean

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset TensorProduct Formalism.HermitianLatticeCounting.S8
noncomputable section
namespace GlobalTheory.CompanionTheory.Inh.CharId
open Polynomial Formalism.REAL
def IsPolyFun {B : Type*} [Ring B] [Algebra ℂ B] (f : ℂ → B) : Prop :=
  ∃ P : B[X], ∀ u, f u = P.eval (algebraMap ℂ B u)
section
variable {B : Type*} [Ring B] [Algebra ℂ B]
theorem IsPolyFun.map {B' : Type*} [Ring B'] [Algebra ℂ B'] (g : B →ₐ[ℂ] B') {f : ℂ → B}
    (hf : IsPolyFun f) : IsPolyFun (fun u => g (f u)) := by
  obtain ⟨P, hP⟩ := hf
  refine ⟨P.map (g : B →+* B'), fun u => ?_⟩
  show g (f u) = _
  rw [hP, ← g.commutes u]
  exact (Polynomial.eval_map_apply (g : B →+* B') _).symm
end
section
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
def op (M : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (V ⊗[ℂ] (Fin n → ℂ)) :=
  ∑ a, ∑ b, TensorProduct.map (M a b) (stdRep n a b)
end
end GlobalTheory.CompanionTheory.Inh.CharId
namespace GlobalTheory.CompanionTheory.Inh
open CharId
end GlobalTheory.CompanionTheory.Inh


