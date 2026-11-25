-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:12:12.452166+00:00
-- url     : https://prove2.me/theorems/9cdd7a68-43f5-5798-9e0f-0e77d3258d9b
-- title:
--   PHilbert Point
-- statement:
--   Definitions and structural lemmas for PHilbert Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_mem_primeOf_077b7ab281b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
namespace HilbertPoint
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
def aff (y : Fin (N + 1) → Ω) (j : Fin (N + 1)) : Fin (N + 1) → Ω := fun l => y l / y j
theorem aff_def (y : Fin (N + 1) → Ω) (j : Fin (N + 1)) : aff y j = fun l => y l / y j := rfl
variable (k) in

def affRing (y : Fin (N + 1) → Ω) (j : Fin (N + 1)) : Subalgebra k Ω :=
  (aeval (aff y j) : Poly k N →ₐ[k] Ω).range
variable (k) in

def affPiece (y : Fin (N + 1) → Ω) (j : Fin (N + 1)) (n : ℕ) : Submodule k Ω :=
  Submodule.span k {z | ∃ f : Poly k N, f.IsHomogeneous n ∧ z = aeval (aff y j) f}
variable {y : Fin (N + 1) → Ω} {j : Fin (N + 1)}
theorem aeval_aff_of_mem_primeOf {f : Poly k N} (hf : f ∈ primeOf (S := k) y) :
    aeval (aff y j) f = 0 := by
  rw [← sum_homogeneousComponent f, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [aff_def, aeval_div_of_isHomogeneous (homogeneousComponent_isHomogeneous d f),
    (mem_primeOf_of_isHomogeneous y (homogeneousComponent_isHomogeneous d f)).mp
      (homogeneousComponent_mem_primeOf y hf d), zero_div]
theorem le_zero_of_add_one_le_one {d : WithBot ℕ∞} (h : d + 1 ≤ 1) : d ≤ 0 := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    have h' : e + 1 ≤ 1 := by exact_mod_cast h
    induction e using ENat.recTopCoe with
    | top => simp at h'
    | coe m =>
      have : m + 1 ≤ 1 := by exact_mod_cast h'
      have hm : m = 0 := by omega
      subst hm
      simp
theorem isField_affRing (hy : IsSubvar y (primeOf (S := k) y) 0) (hj : y j ≠ 0) :
    IsField (affRing k y j) := by
  let φ : Poly k N →ₐ[k] affRing k y j := (aeval (aff y j)).rangeRestrict
  have hφ : Function.Surjective φ := AlgHom.rangeRestrict_surjective _
  have hker : ∀ f ∈ primeOf (S := k) y, φ.toRingHom f = 0 := fun f hf =>
    Subtype.ext (aeval_aff_of_mem_primeOf hf)
  let ψ : Poly k N ⧸ primeOf (S := k) y →+* affRing k y j :=
    Ideal.Quotient.lift (primeOf (S := k) y) φ.toRingHom hker
  have hψ : Function.Surjective ψ := Ideal.Quotient.lift_surjective_of_surjective _ hker hφ
  let r : Poly k N ⧸ primeOf (S := k) y := Ideal.Quotient.mk _ (X j - 1)
  have hr : r ≠ 0 := by
    intro h
    have hmem : (X j - 1 : Poly k N) ∈ primeOf (S := k) y := Ideal.Quotient.eq_zero_iff_mem.mp h
    have h0 := homogeneousComponent_mem_primeOf y hmem 0
    rw [homogeneousComponent_zero] at h0
    have := (mem_primeOf_of_isHomogeneous y (isHomogeneous_C _ _)).mp h0
    simp at this
  have hr' : r ∈ nonZeroDivisors (Poly k N ⧸ primeOf (S := k) y) := mem_nonZeroDivisors_of_ne_zero hr
  have hψr : ψ r = 0 := by
    apply Subtype.ext
    change aeval (aff y j) (X j - 1 : Poly k N) = 0
    simp [aff, hj]
  have hrψ : ∀ a ∈ Ideal.span {r}, ψ a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hψr, mul_zero]
  have hχ : Function.Surjective (Ideal.Quotient.lift (Ideal.span {r}) ψ hrψ) :=
    Ideal.Quotient.lift_surjective_of_surjective _ hrψ hψ
  have h1 : ringKrullDim (affRing k y j) ≤
      ringKrullDim ((Poly k N ⧸ primeOf (S := k) y) ⧸ Ideal.span {r}) := by
    exact ringKrullDim_le_of_surjective _ hχ
  have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr'
  rw [hy.dim] at h2
  have h3 : ringKrullDim (affRing k y j) ≤ 0 :=
    le_zero_of_add_one_le_one ((add_le_add h1 (le_refl (1 : WithBot ℕ∞))).trans (by simpa using h2))
  have : Ring.KrullDimLE 0 (affRing k y j) := Ring.krullDimLE_iff.mpr (by simpa using h3)
  exact Ring.KrullDimLE.isField_of_isDomain
end HilbertPoint
end
end GroundTheory.Heights₂.Heights.Kleiman


