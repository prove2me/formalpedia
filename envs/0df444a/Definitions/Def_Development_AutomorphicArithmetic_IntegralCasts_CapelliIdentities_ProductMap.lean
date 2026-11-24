-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ProductMap
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ProductMap
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T20:46:09.080003+00:00
-- url     : https://prove2.me/theorems/89d035f1-65b5-4398-bcb2-915bf4d80429
-- title:
--   Product Map
-- statement:
--   Definitions and structural lemmas for Product Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ProductMap.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.IdempotentMatrixMonoidHom.prM :
    {R A : Type} →
      [inst : CommRing R] →
        [inst_1 : CommRing A] →
          [Algebra R A] →
            (e : R) → e * e = e → (ι : Type) → [inst : Fintype ι] → [inst_3 : DecidableEq ι] → Matrix ι ι A →* Matrix ι ι A :=
  fun {R A} _ _ _ e he ι _ _ =>
    { toFun := fun M => e • M + (1 - e) • (1 : Matrix ι ι A)
      map_one' := by rw [← add_smul, add_sub_cancel, one_smul]
      map_mul' := fun M N => by
        have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
        have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
        have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, mul_one, h2, sub_zero]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
          smul_smul, he, h1, h2, h3, zero_smul, add_zero, zero_add, Matrix.mul_one] }


