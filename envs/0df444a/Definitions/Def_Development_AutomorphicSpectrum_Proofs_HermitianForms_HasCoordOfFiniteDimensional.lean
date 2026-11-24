-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
-- name    : Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:23:13.310406+00:00
-- url     : https://prove2.me/theorems/8791f35b-0c5d-4057-a99b-34b483c0c0b5
-- title:
--   Has Coord Of Finite Dimensional
-- statement:
--   Definitions and structural lemmas for Has Coord Of Finite Dimensional, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/HasCoordOfFiniteDimensional.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk


set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CompanionTheory.SelfDualInf
def HasCoord (V : Type) [AddCommGroup V] [TopologicalSpace V] : Prop :=
  ∃ (N : ℕ) (e : V ≃+ (Fin N → ℝ)), Continuous e ∧ Continuous e.symm
section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
theorem sigR_tmul (r : R) (x : E) : sigR R σ (r ⊗ₜ[F] x) = r ⊗ₜ[F] σ x := rfl
theorem sigR_invol (hσ : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z with
  | zero => simp
  | tmul r x => rw [sigR_tmul, sigR_tmul, hσ]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
theorem sigR_smul (r : R) (z : R ⊗[F] E) : sigR R σ (r • z) = r • sigR R σ z := by
  induction z with
  | zero => simp
  | tmul s x => simp [TensorProduct.smul_tmul', sigR_tmul]
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]
def sigLin : R ⊗[F] E →ₗ[R] R ⊗[F] E where
  toFun := sigR R σ
  map_add' := map_add _
  map_smul' := sigR_smul R σ
end Alg
section Form
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
def hermUnit (hσ : ∀ x, σ (σ x) = x) (n : ℕ) (a b : Fin n) (u : R ⊗[F] E) : HermR R σ n :=
  ⟨fun i j => (if i = b ∧ j = a then u else 0) + (if i = a ∧ j = b then sigR R σ u else 0), by
    intro i j
    have e1 : (j = b ∧ i = a) ↔ (i = a ∧ j = b) := and_comm
    have e2 : (j = a ∧ i = b) ↔ (i = b ∧ j = a) := and_comm
    simp only [map_add, apply_ite (sigR R σ), map_zero, sigR_invol R σ hσ, e1, e2]
    rw [add_comm]⟩
end Form
section Top
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  (σ : E →ₐ[F] E)
end Top
section Arch
variable {F : Type} [Field F] [NumberField F]
end Arch
end GlobalTheory.CompanionTheory.SelfDualInf


