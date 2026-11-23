-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:36.443368+00:00
-- url     : https://prove2.me/theorems/ba1abe4a-4f28-4834-a3bf-7f350b0124f0
-- title:
--   ESMul ESOf Ne Zero
-- statement:
--   Definitions and structural lemmas for ESMul ESOf Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/ESMulESOfNeZero.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.Tr
open PI.Dv
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
abbrev cf (T : GoodSet K G) (s : T.S) : K :=
  ((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K)
def phiS (T : GoodSet K G) (s : T.S) : Module.End K (T.W s) →ₗ[K] MonoidAlgebra K G where
  toFun X := ∑ x : G, (cf T s * LinearMap.trace K (T.W s) (T.tau s x⁻¹ * X)) • MonoidAlgebra.of K G x
  map_add' X Y := by
    simp only [mul_add, map_add, add_smul, Finset.sum_add_distrib]
  map_smul' r X := by
    simp only [mul_smul_comm, map_smul, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring_nf
end PI.Dv.Tr


