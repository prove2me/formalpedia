-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA
-- name    : ReciprocityTheory_SemistableReduction_SemiDegAA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:59.137704+00:00
-- url     : https://prove2.me/theorems/53edfecc-bb68-4c01-b69a-8dc03ad2915c
-- title:
--   Semi Deg AA
-- statement:
--   Definitions and structural lemmas for Semi Deg AA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegAA.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open Module
def waR {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (x : Fin r → K) :
    (Fin r → K) →ₗ[K] K where
  toFun y := S.h x y
  map_add' y z := by
    simp only [HermForm.h, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a y := by
    simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end ReciprocityTheory.MultiplicativeHeights


