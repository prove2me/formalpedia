-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightSemilocalQuotCard
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightSemilocalQuotCard
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:01.882351+00:00
-- url     : https://prove2.me/theorems/3950bbcf-9708-4e9f-ac6c-a9d9168e26c8
-- title:
--   Height Semilocal Quot Card
-- statement:
--   Definitions and structural lemmas for Height Semilocal Quot Card, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightSemilocalQuotCard.lean

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
namespace GroundTheory.Heights₂.Heights
open NumberField
def integralAtPlaces {L : Type*} [Field L] [NumberField L] (S : Set (FinitePlace L)) :
    Subalgebra ℤ L where
  carrier := {x | ∀ w ∈ S, w x ≤ 1}
  mul_mem' {a b} ha hb w hw := by
    rw [map_mul]
    exact mul_le_one₀ (ha w hw) (apply_nonneg w b) (hb w hw)
  add_mem' {a b} ha hb w hw := (FinitePlace.add_le w a b).trans (max_le (ha w hw) (hb w hw))
  algebraMap_mem' z w _ := by
    rw [eq_intCast, ← FinitePlace.mk_maximalIdeal w, FinitePlace.mk_apply,
      FinitePlace.norm_embedding]
    exact NumberField.HeightOneSpectrum.adicAbv_intCast_le_one (K := L) (v := w.maximalIdeal) z
def SemilocalQuotCard.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (S : Set (FinitePlace L)), S.Finite →
    ∀ t : integralAtPlaces S, t ≠ 0 →
      (Nat.card (integralAtPlaces S ⧸ Ideal.span {t}) : ℝ) = ∏ᶠ w ∈ S, (w (t : L))⁻¹
example : ∃ (S : Set (FinitePlace ℚ)) (t : integralAtPlaces S), S.Finite ∧ S.Nonempty ∧ t ≠ 0 := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 ℚ)
  have hne : P ≠ ⊥ := fun h ↦
    RingOfIntegers.not_isField ℚ (Ring.isField_iff_maximal_bot.mpr (h ▸ hP))
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) := ⟨P, hP.isPrime, hne⟩
  refine ⟨{FinitePlace.mk v}, 2, Set.finite_singleton _, Set.singleton_nonempty _, ?_⟩
  intro h
  have := congrArg (fun y : integralAtPlaces ({FinitePlace.mk v} : Set (FinitePlace ℚ)) ↦ (y : ℚ)) h
  norm_num at this
end GroundTheory.Heights₂.Heights


