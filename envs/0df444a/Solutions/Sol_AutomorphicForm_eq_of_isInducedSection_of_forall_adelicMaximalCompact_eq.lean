-- Prove2me | solution 1 for AutomorphicForm.eq_of_isInducedSection_of_forall_adelicMaximalCompact_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/54e96c91-d11a-5b22-bc6f-8332f015e005

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_eq_of_isInducedSection_of_forall_adelicMaximalCompact_eq
p2m_attr_erase "instance" "HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val"

set_option autoImplicit false

open NumberField AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K]
    (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (φ₁ φ₂ : AdelicGL2 (𝓞 K) K → ℂ)
    (h₁ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ₁) (h₂ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ₂)
    (h : ∀ k : adelicMaximalCompact K, φ₁ (k : AdelicGL2 (𝓞 K) K) = φ₂ (k : AdelicGL2 (𝓞 K) K)) :
    φ₁ = φ₂ := by
  funext g
  obtain ⟨b, k, hb, hkf, hka, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq K g
  have hk : k ∈ adelicMaximalCompact K := ⟨hkf, hka⟩
  rw [h₁ b hb k, h₂ b hb k, h ⟨k, hk⟩]

end S_AutomorphicForm_eq_of_isInducedSection_of_forall_adelicMaximalCompact_eq
end P2MW
export P2MW.S_AutomorphicForm_eq_of_isInducedSection_of_forall_adelicMaximalCompact_eq (solution)
