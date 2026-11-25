-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_RationalCyclotomic
-- name    : GroundTheory_GlobalFields_NormResidueSymbol_RationalCyclotomic
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:48:38.673071+00:00
-- url     : https://prove2.me/theorems/c7e91f36-f231-495a-86f7-e64a575f8dbe
-- title:
--   Rational Cyclotomic
-- statement:
--   Definitions and structural lemmas for Rational Cyclotomic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/NormResidueSymbol/RationalCyclotomic.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Rational
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Theorems.Thm_GroundTheory_Global_Cyclotomic_character_surjective
import Theorems.Thm_GroundTheory_Global_Cyclotomic_ker_character

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open IsDedekindDomain NumberField IdeleGroup IntermediateField
open scoped GroundTheory.LocalField.Abstract
noncomputable section
namespace RationalSymbol
open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
instance isGalois_maxCyclotomic : IsGalois ℚ maxCyclotomic := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  have h : @IsGalois ℚ _ maxCyclotomic _ (IntermediateField.algebra' maxCyclotomic) := by
    rw [← InfiniteGalois.normal_iff_isGalois, ← ker_character]
    infer_instance
  convert h
  exact Subsingleton.elim _ _
abbrev cycRestrict : Gal(ℚ̄/ℚ) →* Gal(maxCyclotomic/ℚ) :=
  AlgEquiv.restrictNormalHom maxCyclotomic
theorem cycRestrict_surjective : Function.Surjective cycRestrict := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  exact AlgEquiv.restrictNormalHom_surjective ℚ̄
theorem coe_cycRestrict_apply (σ : Gal(ℚ̄/ℚ)) (x : maxCyclotomic) :
    ((cycRestrict σ x : maxCyclotomic) : ℚ̄) = σ x :=
  AlgEquiv.restrictNormal_commutes σ maxCyclotomic x
theorem ker_cycRestrict : cycRestrict.ker = character.ker := by
  rw [ker_character]
  ext σ
  rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have := coe_cycRestrict_apply σ ⟨x, hx⟩
    rw [h, AlgEquiv.one_apply] at this
    exact this.symm
  · intro h
    ext x
    rw [coe_cycRestrict_apply, AlgEquiv.one_apply]
    exact h x x.2
def cycCharacter : Gal(maxCyclotomic/ℚ) ≃* ℤ̂ˣ :=
  (QuotientGroup.quotientKerEquivOfSurjective cycRestrict cycRestrict_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq ker_cycRestrict).trans
      (QuotientGroup.quotientKerEquivOfSurjective character character_surjective))
def unitPart : IdeleClassGroup ℚ →* ℤ̂ˣ :=
  (Units.map padicEquiv.symm.toRingHom.toMonoidHom).comp
    ((MonoidHom.snd _ _).comp RationalIdeles.ideleClassGroupEquiv.toMulEquiv.toMonoidHom)
def reciprocityMap : IdeleClassGroup ℚ →* Gal(maxCyclotomic/ℚ) :=
  cycCharacter.symm.toMonoidHom.comp unitPart⁻¹
end RationalSymbol
end
end GroundTheory.Global


