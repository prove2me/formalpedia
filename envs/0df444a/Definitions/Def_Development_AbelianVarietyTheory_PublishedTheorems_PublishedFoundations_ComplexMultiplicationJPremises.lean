-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:36:29.600526+00:00
-- url     : https://prove2.me/theorems/ecd20df5-a903-4a73-9dad-af779f7dde39
-- title:
--   Complex Multiplication JPremises
-- statement:
--   Definitions and structural lemmas for Complex Multiplication JPremises, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/ComplexMultiplicationJPremises.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors IntermediateField
namespace GlobalTheory.Published
instance galSMulCommClassIntegers {K L : Type*} [Field K] [Field L] [Algebra K L] :
    SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) where
  smul_comm s a x := by
    apply RingOfIntegers.ext
    rw [Algebra.smul_def, Algebra.smul_def]
    change s (algebraMap K L a * x) = algebraMap K L a * s x
    rw [map_mul, AlgEquiv.commutes]
section Defs
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
def IsUnramifiedAbelian (M : IntermediateField K ℂ) : Prop :=
  FiniteDimensional K M ∧ IsAbelianGalois K M ∧
    ∀ (P : Ideal (𝓞 M)) [P.IsPrime], P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 K) P
def IsHilbertClassField (H : IntermediateField K ℂ) : Prop :=
  IsUnramifiedAbelian H ∧ ∀ M : IntermediateField K ℂ, IsUnramifiedAbelian M → M ≤ H
def IsArtinMap {H : IntermediateField K ℂ} (art : ClassGroup (𝓞 K) →* (H ≃ₐ[K] H)) : Prop :=
  ∀ (𝔭 : (Ideal (𝓞 K))⁰) (𝔓 : Ideal (𝓞 H)), 𝔓.IsPrime → 𝔓.LiesOver (𝔭 : Ideal (𝓞 K)) →
    IsArithFrobAt (𝓞 K) (art (ClassGroup.mk0 𝔭)) 𝔓
def IsIdealLattice (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : PeriodPair) : Prop :=
  (L.lattice : Set ℂ) = algebraMap K ℂ '' 𝔞.1
end Defs
def ComplexMultiplicationJSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K ℂ],
    Module.finrank ℚ K = 2 →
    ∃ (H : IntermediateField K ℂ) (art : ClassGroup (𝓞 K) ≃* (H ≃ₐ[K] H)),
      IsHilbertClassField H ∧ IsArtinMap art.toMonoidHom ∧
      (∀ (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : PeriodPair), IsIdealLattice 𝔞 L →
        K⟮(latticeCurve L).j⟯ = H) ∧
      ∀ (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L L' : PeriodPair),
        IsIdealLattice 𝔞 L → IsIdealLattice (𝔟⁻¹ * 𝔞) L' →
        ∀ x : H, (x : ℂ) = (latticeCurve L).j →
          (art (ClassGroup.mk K 𝔟) x : ℂ) = (latticeCurve L').j
section Lemmas
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
end Lemmas
end GlobalTheory.Published


