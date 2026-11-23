-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_MemIntOEOfIsIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:57:47.388429+00:00
-- url     : https://prove2.me/theorems/603e677d-4e90-43a3-9106-5e8478cf36d1
-- title:
--   Mem Int OEOf Is Integral
-- statement:
--   Definitions and structural lemmas for Mem Int OEOf Is Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/MemIntOEOfIsIntegral.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace PI.UnitaryApproxFinWork
section General
variable {n : Type} [Fintype n] [DecidableEq n]
def scU {A : Type} [CommRing A] (a b : A) (h : a * b = 1) : GL n A :=
  ⟨a • 1, b • 1, by rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, h, one_smul],
    by rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_comm, h, one_smul]⟩
end General
section Tensor
variable {F E : Type} [Field F] [CommRing E] [Algebra F E]
end Tensor
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end PI.UnitaryApproxFinWork
end


