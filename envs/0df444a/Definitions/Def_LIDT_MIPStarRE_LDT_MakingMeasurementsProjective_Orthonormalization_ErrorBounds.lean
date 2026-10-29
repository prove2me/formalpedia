-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_ErrorBounds
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_ErrorBounds
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:53:27.803417+00:00
-- url     : https://prove2.me/theorems/041165dc-c129-45f8-a29f-ce0ecae76393
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / Orthonormalization / ErrorBounds
-- statement:
--   This bundle compares the error convention used by the submeasurement orthonormalization lemma with the error convention used by its completed-measurement route. It provides the constant-factor bookkeeping needed when projectivizing and completing approximate measurements.
--
--   Principal definitions:
--   - `orthonormalizationMainLemmaError_two_mul_le_orthonormalizationError`: The submeasurement error, multiplied by two, is bounded by the named orthonormalization error envelope.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization/ErrorBounds.lean#L24-L75

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization/ErrorBounds.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib

namespace LIDT

/-!
# Error Bounds for Orthonormalization

This file records the scalar estimates which compare the intermediate error
terms in the proof of the orthonormalization theorem with the paper's final
`100 * ζ ^ (1/4)` envelope.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

/-! ### Scalar estimates -/

namespace Orthonormalization
namespace ErrorBounds

/-- Bookkeeping for the submeasurement version of the orthonormalization theorem:
after completing `A` by a fresh outcome, the local measurement lemma returns the
error `84·(2ζ)^{1/4}`, which is bounded by the paper's `100·ζ^{1/4}`. -/
lemma orthonormalizationMainLemmaError_two_mul_le_orthonormalizationError
    (ζ : Error) (hζ : 0 ≤ ζ) :
    orthonormalizationMainLemmaError (2 * ζ) ≤ orthonormalizationError ζ := by
  dsimp [orthonormalizationMainLemmaError, orthonormalizationError]
  rw [Real.mul_rpow (by positivity) hζ]
  have hconst :
      84 * Real.rpow (2 : Error) (1 / (4 : Error)) ≤ 100 := by
    have hquarter : Real.rpow (2 : Error) (1 / (4 : Error)) ≤ 25 / 21 := by
      let x : Error := Real.rpow (2 : Error) (1 / (4 : Error))
      have hx_nonneg : 0 ≤ x := by
        dsimp [x]
        exact Real.rpow_nonneg (by norm_num) _
      have hx4 : x ^ (4 : ℕ) = 2 := by
        change (Real.rpow (2 : Error) (1 / (4 : Error))) ^ (4 : ℕ) = 2
        calc
          (Real.rpow (2 : Error) (1 / (4 : Error))) ^ (4 : ℕ)
              = (Real.rpow (2 : Error) (1 / (4 : Error))) ^ (4 : Error) := by
                  symm
                  exact Real.rpow_natCast _ 4
          _ = Real.rpow (2 : Error) ((1 / (4 : Error)) * 4) := by
                  simpa using
                    (Real.rpow_mul (x := (2 : Error)) (by positivity)
                      (1 / (4 : Error)) 4).symm
          _ = Real.rpow (2 : Error) 1 := by norm_num
          _ = 2 := by norm_num [Real.rpow_natCast]
      by_contra hx_gt
      have hx_lt : (25 / 21 : Error) < x := lt_of_not_ge hx_gt
      have hpow_lt : (25 / 21 : Error) ^ (4 : ℕ) < x ^ (4 : ℕ) := by
        exact pow_lt_pow_left₀ hx_lt (by positivity) (by decide)
      have hq : (2 : Error) < (25 / 21 : Error) ^ (4 : ℕ) := by
        norm_num
      have : (25 / 21 : Error) ^ (4 : ℕ) < 2 := by
        simpa [hx4] using hpow_lt
      linarith
    calc
      84 * Real.rpow (2 : Error) (1 / (4 : Error))
        ≤ 84 * (25 / 21 : Error) := by
            refine mul_le_mul_of_nonneg_left hquarter ?_
            norm_num
      _ = 100 := by norm_num
  have hquart_nonneg : 0 ≤ Real.rpow ζ (1 / (4 : Error)) := Real.rpow_nonneg hζ _
  calc
    84 *
        (Real.rpow (2 : Error) (1 / (4 : Error)) *
          Real.rpow ζ (1 / (4 : Error))) =
      (84 * Real.rpow (2 : Error) (1 / (4 : Error))) *
        Real.rpow ζ (1 / (4 : Error)) := by ring
    _ ≤ 100 * Real.rpow ζ (1 / (4 : Error)) := by
          exact mul_le_mul_of_nonneg_right hconst hquart_nonneg





end ErrorBounds
end Orthonormalization

end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


