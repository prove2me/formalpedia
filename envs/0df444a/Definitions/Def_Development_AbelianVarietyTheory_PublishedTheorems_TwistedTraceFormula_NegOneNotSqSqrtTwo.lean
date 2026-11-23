-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_NegOneNotSqSqrtTwo
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_NegOneNotSqSqrtTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:08.015468+00:00
-- url     : https://prove2.me/theorems/8b78f51e-219c-4f09-9b58-ed86f7493c3f
-- title:
--   Neg One Not Sq Sqrt Two
-- statement:
--   Definitions and structural lemmas for Neg One Not Sq Sqrt Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NegOneNotSqSqrtTwo.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory.QuadSymbol
namespace GlobalTheory.QuadSymbol.Model
section Quad
variable {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)]
end Quad
section Real
variable {K : Type} [Field K] [Fact (∀ r : K, r ^ 2 ≠ -1 + 0 * r)]
end Real
section Tower
variable {F K : Type} [Field F] [Field K] [Algebra F K] (d : F)
def sqrtMap : QuadraticAlgebra F d 0 →ₐ[F] QuadraticAlgebra K (algebraMap F K d) 0 :=
  QuadraticAlgebra.lift ⟨QuadraticAlgebra.omega, by
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, Algebra.algebraMap_eq_smul_one]⟩
end Tower
instance two_not_sq_rat : Fact (∀ r : ℚ, r ^ 2 ≠ 2 + 0 * r) := ⟨fun r h => by
  rw [zero_mul, add_zero] at h
  have h1 := congrArg (padicValRat 2) h
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by exact_mod_cast padicValRat.self (p := 2) (by norm_num)
  rw [padicValRat.pow, h2] at h1
  omega⟩
instance neg_one_not_sq_rat : Fact (∀ r : ℚ, r ^ 2 ≠ -1 + 0 * r) := ⟨fun r h => by
  nlinarith [sq_nonneg r]⟩
end GlobalTheory.QuadSymbol.Model
end


