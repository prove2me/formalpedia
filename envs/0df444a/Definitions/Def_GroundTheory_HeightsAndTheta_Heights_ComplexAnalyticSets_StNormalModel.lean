-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:14.056839+00:00
-- url     : https://prove2.me/theorems/f87b2042-f02c-4922-8200-4a1b9fecfee5
-- title:
--   St Normal Model
-- statement:
--   Definitions and structural lemmas for St Normal Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalModel.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial
noncomputable section
def zeroSetIn {σ : Type*} (I : Ideal (MvPolynomial σ ℂ)) : Set (σ → ℂ) :=
  {z | ∀ q ∈ I, eval z q = 0}
def firstCoords {n m : ℕ} (w : Fin n ⊕ Fin m → ℂ) : Fin n → ℂ :=
  fun i => w (Sum.inl i)
structure NormalModel {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) where

  m : ℕ

  ideal : Ideal (MvPolynomial (Fin n ⊕ Fin m) ℂ)
  isPrime : ideal.IsPrime
  isIntegrallyClosed : IsIntegrallyClosed (MvPolynomial (Fin n ⊕ Fin m) ℂ ⧸ ideal)
  comap_eq : ideal.comap
    (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ) = J
  integral : ∀ i : Fin m, ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P.Monic ∧
    P.eval₂ (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ).toRingHom
      (X (Sum.inr i)) ∈ ideal
  birational : ∀ i : Fin m, ∃ a b : MvPolynomial (Fin n) ℂ, b ∉ J ∧
    rename Sum.inl b * X (Sum.inr i) - rename Sum.inl a ∈ ideal
def lineDiagonalMap : MvPolynomial (Fin 1 ⊕ Fin 1) ℂ →ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  aeval (Sum.elim X fun _ => X 0)
theorem lineDiagonalMap_rename (q : MvPolynomial (Fin 1) ℂ) : lineDiagonalMap (rename Sum.inl q) = q := by
  rw [lineDiagonalMap, aeval_rename]
  exact aeval_X_left_apply q
theorem lineDiagonalMap_surjective : Function.Surjective lineDiagonalMap :=
  fun q => ⟨rename Sum.inl q, lineDiagonalMap_rename q⟩
def lineDiagonalIdeal : Ideal (MvPolynomial (Fin 1 ⊕ Fin 1) ℂ) :=
  RingHom.ker lineDiagonalMap.toRingHom
theorem lineDiagonalIdeal_isPrime : lineDiagonalIdeal.IsPrime :=
  RingHom.ker_isPrime _
theorem lineDiagonalIdeal_isIntegrallyClosed :
    IsIntegrallyClosed (MvPolynomial (Fin 1 ⊕ Fin 1) ℂ ⧸ lineDiagonalIdeal) :=
  IsIntegrallyClosed.of_equiv (RingHom.quotientKerEquivOfSurjective
    (f := lineDiagonalMap.toRingHom) lineDiagonalMap_surjective).symm
def lineDiagonalModel : NormalModel (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) where
  m := 1
  ideal := lineDiagonalIdeal
  isPrime := lineDiagonalIdeal_isPrime
  isIntegrallyClosed := lineDiagonalIdeal_isIntegrallyClosed
  comap_eq := by
    ext q
    rw [Ideal.mem_comap, Ideal.mem_bot]
    show lineDiagonalMap (rename Sum.inl q) = 0 ↔ q = 0
    rw [lineDiagonalMap_rename]
  integral := fun i => ⟨Polynomial.X - Polynomial.C (X 0), Polynomial.monic_X_sub_C _, by
    show lineDiagonalMap _ = 0
    simp [lineDiagonalMap, Polynomial.eval₂_sub]⟩
  birational := fun i => ⟨X 0, 1, by simp, by
    show lineDiagonalMap _ = 0
    simp [lineDiagonalMap]⟩
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


