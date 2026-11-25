-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_TotalDegreePderivLt
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_TotalDegreePderivLt
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:17:23.128714+00:00
-- url     : https://prove2.me/theorems/f09d5975-2cef-4a41-86e8-f7e660ff22cf
-- title:
--   Total Degree Pderiv Lt
-- statement:
--   Definitions and structural lemmas for Total Degree Pderiv Lt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/TotalDegreePderivLt.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DerAeval
import Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_IsDer_der_one
import Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_IsDer_der_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.GenericSectionMinimum
open IsLocalRing Cardinal
section Fld
variable {F : Type} [Field F]
def constField (K : Type) [Field K] [Algebra K F] {δ : F → F} (h : IsDer δ)
    (hK : ∀ c, δ (algebraMap K F c) = 0) : IntermediateField K F where
  carrier := {x | δ x = 0}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [h.mul, ha, hb, mul_zero, mul_zero, add_zero]
  one_mem' := h.der_one
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [h.add, ha, hb, add_zero]
  zero_mem' := h.der_zero
  algebraMap_mem' c := hK c
  inv_mem' x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    by_cases hx0 : x = 0
    · rw [hx0, inv_zero]; exact h.der_zero
    · have e := h.mul x x⁻¹
      rw [mul_inv_cancel₀ hx0, h.der_one, hx, mul_zero, add_zero] at e
      exact (mul_eq_zero.mp e.symm).resolve_left hx0
end Fld
end Formalism.L2.Pj.GenericSectionMinimum


