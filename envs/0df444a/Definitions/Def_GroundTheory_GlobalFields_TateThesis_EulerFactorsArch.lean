-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsArch
-- name    : GroundTheory_GlobalFields_TateThesis_EulerFactorsArch
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T08:00:40.479083+00:00
-- url     : https://prove2.me/theorems/28c919a1-e40c-509f-85c5-e5f371a66fe9
-- title:
--   Euler Factors Arch
-- statement:
--   Definitions and structural lemmas for Euler Factors Arch, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsArch.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_toIdele_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteComponent
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_standardOpenSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteComponent_finiteUnitsSingle
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toFinite_ofFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toInfinite_ofFinite
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_coe_circleToUnits
import Theorems.Thm_GroundTheory_Global_existsUnique_complexUnits_circle
import Theorems.Thm_GroundTheory_Global_existsUnique_realUnits_circle
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.HeckeCharacter.toIdele_diagonal
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteComponent
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_standardOpenSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteComponent_finiteUnitsSingle
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.toFinite_ofFinite
attribute [local simp] GroundTheory.Global.IdeleGroup.toInfinite_ofFinite
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.coe_circleToUnits
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf


set_option autoImplicit false
open NumberField InfinitePlace InfinitePlace.Completion MeasureTheory Complex ComplexConjugate
open scoped Real
namespace GroundTheory.Global
noncomputable section
section Units
variable {F : Type*} [NormedField F] [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F]
end Units
theorem ofReal_pow_cpow {r : ℝ} (hr : 0 < r) (n : ℕ) (c : ℂ) :
    ((r ^ n : ℝ) : ℂ) ^ c = (r : ℂ) ^ ((n : ℂ) * c) := by
  have h1 : ((r ^ n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hr n).ne'
  have h2 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [cpow_def_of_ne_zero h1, cpow_def_of_ne_zero h2, ← ofReal_log (pow_pos hr n).le,
    ← ofReal_log hr.le, Real.log_pow]
  push_cast
  ring_nf
theorem ofReal_div_abs_eq_sign {x : ℝ} (hx : x ≠ 0) :
    (x : ℂ) / ((|x| : ℝ) : ℂ) = (Real.sign x : ℂ) := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [abs_of_neg h, Real.sign_of_neg h]
    have : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    push_cast
    field_simp
  · rw [abs_of_pos h, Real.sign_of_pos h]
    have : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    push_cast
    field_simp
section Place
variable {K : Type*} [Field K] [NumberField K]
end Place
def unitsContinuousHom {A B : Type*} [Ring A] [Ring B] [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃+* B) (he : Continuous e) : Aˣ →ₜ* Bˣ where
  toMonoidHom := Units.map (e : A →* B)
  continuous_toFun := Units.continuous_iff.2
    ⟨he.comp Units.continuous_val, he.comp Units.continuous_coe_inv⟩
namespace HeckeCharacter
variable {K : Type*} [Field K] [NumberField K] (χ : HeckeCharacter K)
theorem exists_infiniteParams (w : InfinitePlace K) :
    ∃ p : ℤ × ℝ, (w.IsReal → 0 ≤ p.1 ∧ p.1 < 2) ∧ ∀ a : (w.Completion)ˣ,
      (χ.infiniteComponent w a : ℂ) =
        (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ p.1 *
          ((‖(a : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ ((p.2 : ℂ) * I) := by
  by_cases hw : w.IsReal
  · set e := ringEquivRealOfIsReal hw
    have hec : Continuous e.symm := (isometryEquivRealOfIsReal hw).symm.continuous
    set ψ : ℝˣ →ₜ* Circle := (χ.infiniteComponent w).comp (unitsContinuousHom e.symm hec)
    obtain ⟨⟨a', τ⟩, hp, -⟩ := existsUnique_realUnits_circle ψ
    refine ⟨(((a' : ℕ) : ℤ), τ), fun _ ↦ ⟨by positivity, by have := a'.2; omega⟩, fun a ↦ ?_⟩
    have hx := hp (Units.map (e : w.Completion →* ℝ) a)
    have hψ : ψ (Units.map (e : w.Completion →* ℝ) a) = χ.infiniteComponent w a := by
      change χ.infiniteComponent w (Units.map (e.symm : ℝ →* w.Completion)
        (Units.map (e : w.Completion →* ℝ) a)) = _
      congr 1
      ext
      simp
    rw [hψ] at hx
    rw [hx]
    set x : ℝ := e a
    have hι : extensionEmbedding w (a : w.Completion) = (x : ℂ) :=
      (extensionEmbeddingOfIsReal_apply hw _).symm
    have hn : ‖(a : w.Completion)‖ = |x| := by
      rw [← Real.norm_eq_abs]
      exact ((isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _).symm
    have hx0 : x ≠ 0 := (map_ne_zero_iff _ e.injective).2 a.ne_zero
    simp only [Units.coe_map, MonoidHom.coe_coe]
    rw [hι, hn, mult, if_pos hw, pow_one, zpow_natCast, ofReal_div_abs_eq_sign hx0]
  · have hc := not_isReal_iff_isComplex.1 hw
    set e := ringEquivComplexOfIsComplex hc
    have hec : Continuous e.symm := (isometryEquivComplexOfIsComplex hc).symm.continuous
    set ψ : ℂˣ →ₜ* Circle := (χ.infiniteComponent w).comp (unitsContinuousHom e.symm hec)
    obtain ⟨⟨m, τ⟩, hp, -⟩ := existsUnique_complexUnits_circle ψ
    refine ⟨(m, τ / 2), fun h ↦ absurd h hw, fun a ↦ ?_⟩
    have hx := hp (Units.map (e : w.Completion →* ℂ) a)
    have hψ : ψ (Units.map (e : w.Completion →* ℂ) a) = χ.infiniteComponent w a := by
      change χ.infiniteComponent w (Units.map (e.symm : ℂ →* w.Completion)
        (Units.map (e : w.Completion →* ℂ) a)) = _
      congr 1
      ext
      simp
    rw [hψ] at hx
    rw [hx]
    have hι : (e a : ℂ) = extensionEmbedding w (a : w.Completion) := rfl
    have hn : ‖e a‖ = ‖(a : w.Completion)‖ :=
      (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _
    have hpos : 0 < ‖(a : w.Completion)‖ := norm_pos_iff.2 a.ne_zero
    simp only [Units.coe_map, MonoidHom.coe_coe]
    rw [hn, hι, mult, if_neg hw, ofReal_pow_cpow hpos]
    congr 2
    push_cast
    ring
def infiniteParams (w : InfinitePlace K) : ℤ × ℝ := (χ.exists_infiniteParams w).choose
def infiniteWeight (w : InfinitePlace K) : ℤ := (χ.infiniteParams w).1
def infiniteTau (w : InfinitePlace K) : ℝ := (χ.infiniteParams w).2
end HeckeCharacter
namespace HeckeCharacter
variable {K : Type*} [Field K] [NumberField K] (χ : HeckeCharacter K)
def infiniteTest (w : InfinitePlace K) (a : w.Completion) : ℂ :=
  (if 0 < χ.infiniteWeight w then conj (extensionEmbedding w a) else extensionEmbedding w a) ^
      (χ.infiniteWeight w).natAbs * ((Real.exp (-(π * w.mult * ‖a‖ ^ 2)) : ℝ) : ℂ)
open Classical in

def infiniteGamma (w : InfinitePlace K) (s : ℂ) : ℂ :=
  if w.IsReal then Gammaℝ (s + χ.infiniteTau w * I + χ.infiniteWeight w)
  else Gammaℂ (s + χ.infiniteTau w * I + ((χ.infiniteWeight w).natAbs : ℂ) / 2)
omit [NumberField K] in
open Classical in

def infiniteConst (w : InfinitePlace K) : ℂ := if w.IsReal then 1 else π
end HeckeCharacter
end
end GroundTheory.Global


