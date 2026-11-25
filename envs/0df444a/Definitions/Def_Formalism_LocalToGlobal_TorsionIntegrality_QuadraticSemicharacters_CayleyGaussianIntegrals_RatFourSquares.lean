-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RatFourSquares
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RatFourSquares
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:11:24.975192+00:00
-- url     : https://prove2.me/theorems/83ef2260-566f-488b-ad45-2a3db48c982d
-- title:
--   Rat Four Squares
-- statement:
--   Definitions and structural lemmas for Rat Four Squares, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/RatFourSquares.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_InterIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
theorem sqrtNeg_sq (d : ℕ) :
    (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) = -(d : ℂ) := by
  have h : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
    simp
  linear_combination (Complex.I * Complex.I) * h + (d : ℂ) * Complex.I_mul_I
theorem sqrtNeg_conj (d : ℕ) :
    conj (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) = -(Complex.I * ((Real.sqrt d : ℝ) : ℂ)) := by
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
theorem InK.conj {d : ℕ} {z : ℂ} (hz : InK d z) : InK d (conj z) := by
  obtain ⟨p, q, rfl⟩ := hz
  refine ⟨p, -q, ?_⟩
  rw [map_add, map_mul, sqrtNeg_conj, map_ratCast, map_ratCast]
  push_cast
  ring
def fieldK (d : ℕ) : Subfield ℂ where
  carrier := {z | InK d z}
  mul_mem' := by
    rintro _ _ ⟨p, q, rfl⟩ ⟨p', q', rfl⟩
    refine ⟨p * p' - d * q * q', p * q' + q * p', ?_⟩
    push_cast
    linear_combination ((q : ℂ) * (q' : ℂ)) * sqrtNeg_sq d
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨p, q, rfl⟩ ⟨p', q', rfl⟩
    exact ⟨p + p', q + q', by push_cast; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨p, q, rfl⟩
    exact ⟨-p, -q, by push_cast; ring⟩
  inv_mem' := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      exact ⟨0, 0, by simp⟩
    have hc0 : conj z ≠ 0 := by simpa using hz0
    obtain ⟨p, q, rfl⟩ := hz
    have hc : conj ((p : ℂ) + (q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)))
        = (p : ℂ) - (q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) := by
      rw [map_add, map_mul, sqrtNeg_conj, map_ratCast, map_ratCast]
      ring
    rw [hc] at hc0
    have hN : ((p : ℂ) + (q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)))
        * ((p : ℂ) - (q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ))) = ((p * p + d * q * q : ℚ) : ℂ) := by
      push_cast
      linear_combination (-(q : ℂ) * (q : ℂ)) * sqrtNeg_sq d
    have hN0 : ((p * p + d * q * q : ℚ) : ℂ) ≠ 0 := by
      rw [← hN]
      exact mul_ne_zero hz0 hc0
    refine ⟨p / (p * p + d * q * q), -q / (p * p + d * q * q), ?_⟩
    apply inv_eq_of_mul_eq_one_right
    have : ((p : ℂ) + (q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)))
        * (((p / (p * p + d * q * q) : ℚ) : ℂ) + ((-q / (p * p + d * q * q) : ℚ) : ℂ)
          * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)))
        = (((p : ℂ) + (q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)))
        * ((p : ℂ) - (q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)))) / ((p * p + d * q * q : ℚ) : ℂ) := by
      rw [Rat.cast_div, Rat.cast_div, Rat.cast_neg]
      ring
    rw [this, hN, div_self hN0]
def PD {n : Type*} [Fintype n] (h : Matrix n n ℂ) : Prop :=
  ∀ x : n → ℂ, x ≠ 0 → 0 < (∑ i, ∑ j, x i * h i j * conj (x j)).re
end Formalism.L2.Th1.H


