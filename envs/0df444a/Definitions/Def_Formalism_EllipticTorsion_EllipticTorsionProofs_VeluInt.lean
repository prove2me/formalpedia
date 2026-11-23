-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_VeluInt
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_VeluInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:52.665799+00:00
-- url     : https://prove2.me/theorems/607b7b91-7a7c-4350-ba32-d5d58edf5983
-- title:
--   Velu Int
-- statement:
--   Definitions and structural lemmas for Velu Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/VeluInt.lean

import Definitions.Def_Formalism_EllipticTorsion_VeluIntegralModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
namespace Formalism.ELL
namespace VeluIntegrality
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
def ball : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    rwa [norm_neg]
end VeluIntegrality
end Formalism.ELL


