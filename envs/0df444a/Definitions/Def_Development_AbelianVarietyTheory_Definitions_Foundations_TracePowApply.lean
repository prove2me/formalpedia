-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TracePowApply
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_TracePowApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:53.352283+00:00
-- url     : https://prove2.me/theorems/13ee6224-d5af-44b6-92d5-a7036ca380cb
-- title:
--   Trace Pow Apply
-- statement:
--   Definitions and structural lemmas for Trace Pow Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TracePowApply.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_GelfA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Mem.GelfCheck
open MvPolynomial GlobalTheory.Mem.Gelf
section
variable {A : Type} [Ring A] {N : ℕ} {E : Matrix (Fin N) (Fin N) A}
end
section
variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] {N : ℕ}
  {E : Matrix (Fin N) (Fin N) (Module.End R V)} {μ : Fin N → R} {v : V}
end
example : gelfC (![1, 0] : Fin 2 → ℤ) 2 = 2 := by
  simp [gelfC, gelfA, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
example : gelfC (![0, 1] : Fin 2 → ℤ) 2 = 0 := by
  simp [gelfC, gelfA, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
end GlobalTheory.Mem.GelfCheck


