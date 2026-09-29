-- Prove2me | solution 1 for AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_exchange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c35b7dcf-8c06-5f4f-903a-7ea4ace8207a

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_Correspondence
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.SeparableClosure
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber
import Theorems.Thm_AlgebraicCurve_Place_exists_restrict_eq
import Theorems.Thm_AlgebraicCurve_Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_comp
import Theorems.Thm_AlgebraicCurve_Place_inertiaDegAlong_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.AlgebraicCurve"

namespace BifibreW2

section AlongBridge

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem inertiaDegAlong_congr {φ φ' : F →ₐ[K] F'} (h : φ = φ') (hφ : φ.toRingHom.IsIntegral)
    (hφ' : φ'.toRingHom.IsIntegral) (w : Place K F') :
    w.inertiaDegAlong φ hφ = w.inertiaDegAlong φ' hφ' := by
  subst h; rfl

variable [Algebra F F'] [IsScalarTower K F F']

theorem isIntegral_toAlgHom [Algebra.IsIntegral F F'] :
    (IsScalarTower.toAlgHom K F F').toRingHom.IsIntegral :=
  fun x => Algebra.IsIntegral.isIntegral (R := F) x

end AlongBridge

section Tower

variable {K F E M : Type*} [Field K] [Field F] [Field E] [Field M]
    [Algebra K F] [Algebra K E] [Algebra K M] [Algebra F E] [Algebra E M] [Algebra F M]
    [IsScalarTower F E M] [IsScalarTower K F E] [IsScalarTower K E M] [IsScalarTower K F M]

theorem toAlgHom_comp_toAlgHom :
    (IsScalarTower.toAlgHom K E M).comp (IsScalarTower.toAlgHom K F E) =
      IsScalarTower.toAlgHom K F M :=
  AlgHom.ext fun x => (IsScalarTower.algebraMap_apply F E M x).symm

theorem restrict_restrict [Algebra.IsIntegral F E] [Algebra.IsIntegral E M]
    [Algebra.IsIntegral F M] (W : Place K M) : (W.restrict E).restrict F = W.restrict F :=
  Place.ext (by
    simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])

end Tower

end BifibreW2

section TowerRows

variable {K F E M : Type*} [Field K] [Field F] [Field E] [Field M]
    [Algebra K F] [Algebra K E] [Algebra K M] [Algebra F E] [Algebra E M] [Algebra F M]
    [IsScalarTower F E M] [IsScalarTower K F E] [IsScalarTower K E M] [IsScalarTower K F M]

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place.ramificationIndex_pos Place.restrict_toValuationSubring Place Place.ext Place.sum_ramificationIndex_mul_inertiaDeg_bifiber Place.exists_restrict_eq Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg Place.ramificationIndexAlong_comp Place.inertiaDegAlong_comp" namespace Place p2m_export "AlgebraicCurve.Place" "ramificationIndex ramificationIndex_pos restrict restrict_toValuationSubring inertiaDeg ext inertiaDegAlong sum_ramificationIndex_mul_inertiaDeg_bifiber exists_restrict_eq card_fiberOver_mul_ramificationIndex_mul_inertiaDeg ramificationIndexAlong_comp inertiaDegAlong_comp" end AlgebraicCurve.Place
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in

theorem AlgebraicCurve.Place.ramificationIndex_eq_mul_ramificationIndex_restrict
    [Algebra.IsIntegral F E] [Algebra.IsIntegral E M] (W : Place K M) :
    W.ramificationIndex F = W.ramificationIndex E * (W.restrict E).ramificationIndex F := by
  have h := Place.ramificationIndexAlong_comp (IsScalarTower.toAlgHom K F E)
    (IsScalarTower.toAlgHom K E M) BifibreW2.isIntegral_toAlgHom BifibreW2.isIntegral_toAlgHom
    (by rw [BifibreW2.toAlgHom_comp_toAlgHom]
        haveI : Algebra.IsIntegral F M := Algebra.IsIntegral.trans E
        exact BifibreW2.isIntegral_toAlgHom) W
  rw [BifibreW2.toAlgHom_comp_toAlgHom] at h
  exact h

p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in

theorem AlgebraicCurve.Place.inertiaDeg_eq_mul_inertiaDeg_restrict
    [Algebra.IsIntegral F E] [Algebra.IsIntegral E M] [Algebra.IsIntegral F M] (W : Place K M) :
    W.inertiaDeg F = W.inertiaDeg E * (W.restrict E).inertiaDeg F := by
  have h := Place.inertiaDegAlong_comp (IsScalarTower.toAlgHom K F E)
    (IsScalarTower.toAlgHom K E M) BifibreW2.isIntegral_toAlgHom BifibreW2.isIntegral_toAlgHom
    (by rw [BifibreW2.toAlgHom_comp_toAlgHom]; exact BifibreW2.isIntegral_toAlgHom) W
  rw [BifibreW2.inertiaDegAlong_congr BifibreW2.toAlgHom_comp_toAlgHom _
    BifibreW2.isIntegral_toAlgHom] at h
  exact h

end TowerRows

namespace BifibreW2

section Envelope

variable (F E : Type*) [Field F] [Field E] [Algebra F E]

abbrev Env : Type _ := ↥(IntermediateField.normalClosure F E (AlgebraicClosure E))

theorem isGalois_env [FiniteDimensional F E] [Algebra.IsSeparable F E] : IsGalois F (Env F E) := by
  haveI : Normal F (AlgebraicClosure E) := IsAlgClosure.normal F _
  haveI : ∀ f : E →ₐ[F] AlgebraicClosure E, Algebra.IsSeparable F f.fieldRange := fun f =>
    AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)
  haveI : Algebra.IsSeparable F (Env F E) :=
    IntermediateField.isSeparable_iSup (F := F) (E := AlgebraicClosure E)
      (t := fun f : E →ₐ[F] AlgebraicClosure E => f.fieldRange)
  exact ⟨⟩

variable (R : Type*) [Field R] [Algebra R E]

@[reducible] noncomputable def algebraEnv : Algebra R (Env F E) :=
  ((algebraMap E (Env F E)).comp (algebraMap R E)).toAlgebra

theorem isScalarTower_env_mid : letI := algebraEnv F E R; IsScalarTower R E (Env F E) :=
  letI := algebraEnv F E R
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem isScalarTower_env_base [Algebra F R] [IsScalarTower F R E] :
    letI := algebraEnv F E R; IsScalarTower F R (Env F E) :=
  letI := algebraEnv F E R
  IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (by
    show algebraMap F (AlgebraicClosure E) x =
      algebraMap E (AlgebraicClosure E) (algebraMap R E (algebraMap F R x))
    rw [← IsScalarTower.algebraMap_apply F R E x,
      ← IsScalarTower.algebraMap_apply F E (AlgebraicClosure E) x])

variable (K : Type*) [Field K] [Algebra K F] [Algebra K E] [IsScalarTower K F E]

theorem isScalarTower_env_bot [Algebra K R] [IsScalarTower K R E] :
    letI := algebraEnv F E R; IsScalarTower K R (Env F E) :=
  letI := algebraEnv F E R
  IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (by
    show algebraMap K (AlgebraicClosure E) x =
      algebraMap E (AlgebraicClosure E) (algebraMap R E (algebraMap K R x))
    rw [← IsScalarTower.algebraMap_apply K R E x,
      ← IsScalarTower.algebraMap_apply K E (AlgebraicClosure E) x])

omit [Algebra R E] in
theorem isScalarTower_env_const : IsScalarTower K E (Env F E) :=
  IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (by
    show algebraMap K (AlgebraicClosure E) x =
      algebraMap E (AlgebraicClosure E) (algebraMap K E x)
    rw [← IsScalarTower.algebraMap_apply K E (AlgebraicClosure E) x])

end Envelope

theorem exchange_of_isGalois {K F F₁ F₂ E : Type*} (M : Type*)
    [Field K] [Field F] [Field F₁] [Field F₂] [Field E] [Field M]
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E] [Algebra K M]
    [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F M]
    [Algebra F₁ E] [Algebra F₂ E] [Algebra F₁ M] [Algebra F₂ M] [Algebra E M]
    [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F E] [IsScalarTower K F M]
    [IsScalarTower K F₁ E] [IsScalarTower K F₂ E] [IsScalarTower K F₁ M] [IsScalarTower K F₂ M]
    [IsScalarTower K E M]
    [IsScalarTower F F₁ E] [IsScalarTower F F₂ E] [IsScalarTower F F₁ M] [IsScalarTower F F₂ M]
    [IsScalarTower F E M] [IsScalarTower F₁ E M] [IsScalarTower F₂ E M]
    [FiniteDimensional F F₁] [FiniteDimensional F F₂] [FiniteDimensional F E]
    [FiniteDimensional F₁ E] [FiniteDimensional F₂ E]
    [FiniteDimensional F M] [IsGalois F M]
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤)
    (hLD : Module.finrank F E = Module.finrank F F₁ * Module.finrank F F₂)
    (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂)
    (hw₁ : w₁.restrict F = v) (hw₂ : w₂.restrict F = v)
    (T : Finset (Place K E)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂ =
      w₁.inertiaDeg F * w₂.ramificationIndex F := by
  have hB := AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_bifiber M hgen hLD v w₁ w₂
    hw₁ hw₂ T hT

  have hsum : ∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F =
      (∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂) *
        (w₁.ramificationIndex F * w₂.inertiaDeg F) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun W hW => ?_
    obtain ⟨h₁, h₂⟩ := (hT W).mp hW
    rw [Place.ramificationIndex_eq_mul_ramificationIndex_restrict (F := F) (E := F₁) W, h₁,
      Place.inertiaDeg_eq_mul_inertiaDeg_restrict (F := F) (E := F₂) W, h₂]
    ring

  have he₁ : 0 < w₁.ramificationIndex F := Place.ramificationIndex_pos (F := F) w₁
  have hf₂ : 0 < w₂.inertiaDeg F := by
    haveI : FiniteDimensional F₂ M := Module.Finite.of_restrictScalars_finite F F₂ M
    haveI : IsGalois F₂ M := IsGalois.tower_top_of_isGalois F F₂ M
    obtain ⟨P, hP⟩ := Place.exists_restrict_eq (M := M) w₂
    have hPF : P.restrict F = v := by rw [← restrict_restrict (E := F₂) P, hP, hw₂]
    have hTC := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg v P hPF
    have hf := Place.inertiaDeg_eq_mul_inertiaDeg_restrict (F := F) (E := F₂) P
    rw [hP] at hf
    have hne : Module.finrank F M ≠ 0 := Module.finrank_pos.ne'
    rw [← hTC, hf] at hne
    exact Nat.pos_of_ne_zero fun h0 => hne (by simp [h0])
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos he₁ hf₂)
  rw [← hsum, hB]
  ring

end BifibreW2

p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in
open BifibreW2 in
theorem AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_bifiber_of_isSeparable
    {K F F₁ F₂ E : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field E]
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E]
    [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F₁ E] [Algebra F₂ E]
    [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F E]
    [IsScalarTower K F₁ E] [IsScalarTower K F₂ E] [IsScalarTower F F₁ E] [IsScalarTower F F₂ E]
    [FiniteDimensional F F₁] [FiniteDimensional F F₂] [FiniteDimensional F E]
    [FiniteDimensional F₁ E] [FiniteDimensional F₂ E] [Algebra.IsSeparable F E]
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤)
    (hLD : Module.finrank F E = Module.finrank F F₁ * Module.finrank F F₂)
    (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂)
    (hw₁ : w₁.restrict F = v) (hw₂ : w₂.restrict F = v)
    (T : Finset (Place K E)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F =
      (w₁.ramificationIndex F * w₁.inertiaDeg F) * (w₂.ramificationIndex F * w₂.inertiaDeg F) := by
  letI : Algebra F₁ (Env F E) := algebraEnv F E F₁
  letI : Algebra F₂ (Env F E) := algebraEnv F E F₂
  haveI : IsScalarTower F₁ E (Env F E) := isScalarTower_env_mid F E F₁
  haveI : IsScalarTower F₂ E (Env F E) := isScalarTower_env_mid F E F₂
  haveI : IsScalarTower F F₁ (Env F E) := isScalarTower_env_base F E F₁
  haveI : IsScalarTower F F₂ (Env F E) := isScalarTower_env_base F E F₂
  haveI : IsScalarTower K F₁ (Env F E) := isScalarTower_env_bot F E F₁ K
  haveI : IsScalarTower K F₂ (Env F E) := isScalarTower_env_bot F E F₂ K
  haveI : IsScalarTower K E (Env F E) := isScalarTower_env_const F E K
  haveI : IsGalois F (Env F E) := isGalois_env F E
  exact AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_bifiber (Env F E) hgen hLD v w₁ w₂
    hw₁ hw₂ T hT

open BifibreW2 in
theorem solution
    {K F F₁ F₂ E : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field E]
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E]
    [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F₁ E] [Algebra F₂ E]
    [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F E]
    [IsScalarTower K F₁ E] [IsScalarTower K F₂ E] [IsScalarTower F F₁ E] [IsScalarTower F F₂ E]
    [FiniteDimensional F F₁] [FiniteDimensional F F₂] [FiniteDimensional F E]
    [FiniteDimensional F₁ E] [FiniteDimensional F₂ E] [Algebra.IsSeparable F E]
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤)
    (hLD : Module.finrank F E = Module.finrank F F₁ * Module.finrank F F₂)
    (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂)
    (hw₁ : w₁.restrict F = v) (hw₂ : w₂.restrict F = v)
    (T : Finset (Place K E)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂ =
      w₁.inertiaDeg F * w₂.ramificationIndex F := by
  letI : Algebra F₁ (Env F E) := algebraEnv F E F₁
  letI : Algebra F₂ (Env F E) := algebraEnv F E F₂
  haveI : IsScalarTower F₁ E (Env F E) := isScalarTower_env_mid F E F₁
  haveI : IsScalarTower F₂ E (Env F E) := isScalarTower_env_mid F E F₂
  haveI : IsScalarTower F F₁ (Env F E) := isScalarTower_env_base F E F₁
  haveI : IsScalarTower F F₂ (Env F E) := isScalarTower_env_base F E F₂
  haveI : IsScalarTower K F₁ (Env F E) := isScalarTower_env_bot F E F₁ K
  haveI : IsScalarTower K F₂ (Env F E) := isScalarTower_env_bot F E F₂ K
  haveI : IsScalarTower K E (Env F E) := isScalarTower_env_const F E K
  haveI : IsGalois F (Env F E) := isGalois_env F E
  exact exchange_of_isGalois (Env F E) hgen hLD v w₁ w₂ hw₁ hw₂ T hT

end S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange
end P2MW
export P2MW.S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange (solution)
