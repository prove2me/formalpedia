-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
-- name    : QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T11:14:28.380763+00:00
-- url     : https://prove2.me/theorems/c8631a97-b853-4137-a852-f370f230c84b
-- title:
--   LPSCusp Petersson Positive
-- statement:
--   Definitions and structural lemmas for LPSCusp Petersson Positive, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspPeterssonPositive.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.InnerProductSpace.Defs
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_continuous
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_individual_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_integrable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_invariant
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_nonneg
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_add_left
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_conj
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_self_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_self_nonneg
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_smul_left
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_smul_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal ComplexConjugate
noncomputable section
lemma lpsPetersson_volume_isOpenPosMeasure : (volume : Measure ℍ).IsOpenPosMeasure := by
  let μ : Measure ℍ := volume.comap UpperHalfPlane.coe
  let w : ℍ → ℝ≥0∞ := fun z => ↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0)^2)
  have hm : Measurable w := by
    dsimp [w]
    fun_prop
  have hw : ∀z,w z≠0 := by
    intro z
    have hz : NNReal.mk z.im z.im_pos.le≠0 := by
      intro h
      have hr := congrArg (fun x:ℝ≥0 => (x:ℝ)) h
      exact z.im_ne_zero hr
    exact ENNReal.coe_ne_zero.mpr (pow_ne_zero 2 (by simpa only [one_div] using inv_ne_zero hz))
  have hac : μ ≪ (volume : Measure ℍ) :=
    withDensity_absolutelyContinuous' hm.aemeasurable (Eventually.of_forall hw)
  let : μ.IsOpenPosMeasure := Measure.IsOpenPosMeasure.comap _ UpperHalfPlane.isOpenEmbedding_coe
  exact ⟨fun U hU hne hzero => hU.measure_ne_zero μ hne (hac hzero)⟩
lemma lpsCuspPeterssonDensity_eq_zero_of_integral_eq_zero (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : ∫τ in ModularGroup.fd,lpsCuspPeterssonDensity N f τ=0) :
    lpsCuspPeterssonDensity N f=0 := by
  let : (volume : Measure ℍ).IsOpenPosMeasure := lpsPetersson_volume_isOpenPosMeasure
  have hae : lpsCuspPeterssonDensity N f =ᵐ[volume.restrict ModularGroup.fd] 0 :=
    (integral_eq_zero_iff_of_nonneg (lpsCuspPeterssonDensity_nonneg N f)
      (lpsCuspPeterssonDensity_integrable N f)).mp h
  have hfd : EqOn (lpsCuspPeterssonDensity N f) 0 ModularGroup.fd := by
    apply Measure.eqOn_of_ae_eq hae (lpsCuspPeterssonDensity_continuous N f).continuousOn
      continuous_const.continuousOn
    rw [←ModularGroup.fdo_eq_interior_fd,←ModularGroup.fd_eq_closure_fdo]
  funext τ
  obtain ⟨g,hg⟩ := ModularGroup.exists_smul_mem_fd τ
  rw [←lpsCuspPeterssonDensity_invariant N f g τ]
  exact hfd hg
lemma lpsWeightTwoCusp_eq_zero_of_peterssonMass_eq_zero (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : ∫τ in ModularGroup.fd,lpsCuspPeterssonDensity N f τ=0) : f=0 := by
  have hz := lpsCuspPeterssonDensity_eq_zero_of_integral_eq_zero N f h
  ext τ
  have hi := lpsCuspPeterssonDensity_individual_le N f τ
  rw [hz] at hi
  change ‖f τ‖^2*τ.im^2≤0 at hi
  have hn : ‖f τ‖=0 := by
    by_contra hn
    have hp : 0<‖f τ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    exact (not_lt_of_ge hi) (mul_pos (sq_pos_of_pos hp) (sq_pos_of_pos τ.im_pos))
  exact norm_eq_zero.mp hn
lemma lpsCuspPeterssonPairing_self_eq_zero_iff (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N f f=0 ↔ f=0 := by
  constructor
  · intro h
    apply lpsWeightTwoCusp_eq_zero_of_peterssonMass_eq_zero N f
    rw [lpsCuspPeterssonPairing_self_eq] at h
    exact Complex.ofReal_eq_zero.mp h
  · rintro rfl
    have h := lpsCuspPeterssonPairing_smul_right N 0 0 (0:ℂ)
    simpa using h
@[instance_reducible] def lpsCuspPeterssonCore (N : ℕ) [NeZero N] :
    InnerProductSpace.Core ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) where
  inner := lpsCuspPeterssonPairing N
  conj_inner_symm f g := by rw [lpsCuspPeterssonPairing_conj,conj_conj]
  re_inner_nonneg := lpsCuspPeterssonPairing_self_nonneg N
  add_left := lpsCuspPeterssonPairing_add_left N
  smul_left f g c := lpsCuspPeterssonPairing_smul_left N f g c
  definite f := (lpsCuspPeterssonPairing_self_eq_zero_iff N f).mp
end
end QEC.Coding.TannerLiftedProduct


