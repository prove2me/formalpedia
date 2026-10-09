-- Prove2me | solution 1 for ArtinPrimitiveRoots.vaughan_identity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T16:44:32.85161+00:00
-- url     : https://prove2.me/submissions/26dfb879-6daf-4544-9b8a-45ac977c3e8b

import Mathlib
import Definitions.Def_ArtinBV

section

end

section
/-!
# Elementary divisor-sum estimates
-/

namespace ArtinPrimitiveRoots.BV

open Finset

end ArtinPrimitiveRoots.BV
end

section
/-!
# Vaughan's identity and the resulting decomposition of `ψ(X, χ)`
-/

namespace ArtinPrimitiveRoots.BV

open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- **Vaughan's identity.** -/
theorem vaughan_identity (U V : ℕ) :
    (Λ : ArithmeticFunction ℝ) =
      trunc Λ V + trunc (μ : ArithmeticFunction ℝ) U * ArithmeticFunction.log
        - trunc (μ : ArithmeticFunction ℝ) U * trunc Λ V * (ζ : ArithmeticFunction ℝ)
        + (Λ - trunc Λ V) * (1 - trunc (μ : ArithmeticFunction ℝ) U * (ζ : ArithmeticFunction ℝ)) := by
  have key : trunc (μ : ArithmeticFunction ℝ) U * ArithmeticFunction.log =
      trunc (μ : ArithmeticFunction ℝ) U * Λ * (ζ : ArithmeticFunction ℝ) := by
    rw [mul_assoc, ArithmeticFunction.vonMangoldt_mul_zeta]
  rw [key]
  ring

end ArtinPrimitiveRoots.BV
end

open ArtinPrimitiveRoots in
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius ArithmeticFunction.zeta in
theorem solution (U V : ℕ) :
    (Λ : ArithmeticFunction ℝ) =
      trunc Λ V + trunc (μ : ArithmeticFunction ℝ) U * ArithmeticFunction.log
        - trunc (μ : ArithmeticFunction ℝ) U * trunc Λ V * (ζ : ArithmeticFunction ℝ)
        + (Λ - trunc Λ V) * (1 - trunc (μ : ArithmeticFunction ℝ) U * (ζ : ArithmeticFunction ℝ)) :=
  ArtinPrimitiveRoots.BV.vaughan_identity U V
