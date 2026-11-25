-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocD
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_NDLocD
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T16:09:20.999866+00:00
-- url     : https://prove2.me/theorems/157e43c8-8c23-4a50-94fe-9dec5b319b83
-- title:
--   NDLoc D
-- statement:
--   Definitions and structural lemmas for NDLoc D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocD.lean

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocC
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CovariantDegrees
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_KwF_le_clE_70450b557674
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_jE_mem_86ded92f8610
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_j_rHom_06cfa976bc62
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_rHom_injective_77ec01eca437
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_rHom_surjective_d261655e68d1
import Theorems.Thm_UpperTheory_Reformulated_B_CovariantDegrees_continuous_rHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l}
  {A : ValuationSubring Ω} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
theorem continuous_rHom : Continuous (rHom (E := E) hj) :=
  by apply _root_.UpperTheory.Reformulated.B.CovariantDegrees.continuous_rHom <;> assumption
instance compact_GK (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    CompactSpace ↥K.fixingSubgroup :=
  isCompact_iff_compactSpace.mp (IntermediateField.fixingSubgroup_isClosed K).isCompact
def eDec : ↥(Dec (F := E) A) ≃* ↥(KwF (E := E) j).fixingSubgroup :=
  (MulEquiv.ofBijective (rHom hj) ⟨rHom_injective hj, rHom_surjective hj⟩).symm
theorem eDec_comm (g : ↥(Dec (F := E) A)) (x : Ω) :
    ((eDec hj g : ↥(KwF (E := E) j).fixingSubgroup) : GQ l) (j x) = j ((g : G E Ω) x) := by
  rw [← j_rHom hj]
  congr 2
  exact congrArg Subtype.val ((MulEquiv.ofBijective (rHom hj) ⟨rHom_injective hj, rHom_surjective hj⟩).apply_symm_apply g)
theorem continuous_eDec_symm : Continuous (eDec (E := E) hj).symm := continuous_rHom hj
theorem continuous_eDec : Continuous (eDec (E := E) hj) :=
  Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := (MulEquiv.ofBijective (rHom hj) ⟨rHom_injective hj, rHom_surjective hj⟩).toEquiv)
    (continuous_rHom hj)
def bridgeOf (LL : FinExt l)
    (hLL : ∀ (τ : ↥(KwF (E := E) j) →ₐ[ℚ_[l]] Om l) (x : ↥(KwF (E := E) j)), τ x ∈ LL.1) :
    LocBridge l E Ω (Dec (F := E) A) ↥(OL LL) where
  Kw := ⟨KwF (E := E) j, KwF_fin j⟩
  j := j
  j_E := jE_mem j
  j_dense := KwF_le_clE j
  e := eDec hj
  e_cont := continuous_eDec hj
  e_symm_cont := continuous_eDec_symm hj
  e_comm := eDec_comm hj
  LL := LL
  LL_split := hLL
  eO := RingEquiv.refl _
  eO_alg := fun _ => rfl
  eO_cont := continuous_id
  eO_symm_cont := continuous_id
def nclo (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] : FinExt l :=
  ⟨IntermediateField.normalClosure ℚ_[l] K (PadicAlgCl l), inferInstance⟩
end Formalism.BasicNotions.Examples₂.LB
namespace Formalism.BasicNotions.Examples₂
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc LB
end Formalism.BasicNotions.Examples₂


