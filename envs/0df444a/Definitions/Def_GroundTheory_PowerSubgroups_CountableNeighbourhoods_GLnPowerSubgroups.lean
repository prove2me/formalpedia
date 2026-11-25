-- Prove2me | Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_GLnPowerSubgroups
-- name    : GroundTheory_PowerSubgroups_CountableNeighbourhoods_GLnPowerSubgroups
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:15:48.4455+00:00
-- url     : https://prove2.me/theorems/36b23988-fe3b-4373-998e-23ebda8019b6
-- title:
--   GLn Power Subgroups
-- statement:
--   Definitions and structural lemmas for GLn Power Subgroups, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/GLnPowerSubgroups.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_continuous_det
import Theorems.Thm_GroundTheory_Automorphic_AdelicGLn_diagonal_apply
import Theorems.Thm_GroundTheory_Automorphic_RestrictedProduct_matrixUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_continuous_ideleModule
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_ideleModule
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_ideleModule_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.AdelicGLn.diagonal_apply
attribute [local simp] GroundTheory.Automorphic.RestrictedProduct.matrixUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
namespace GroundTheory.Variant₂.N1
open NumberField
noncomputable def normOneGL (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Subgroup (GroundTheory.Automorphic.AdelicGLn.AdelicGL K n) :=
  Subgroup.comap (GroundTheory.Automorphic.AdelicGLn.det K n) (GroundTheory.Global.IdeleGroup.normOneSubgroup K)
section Splitting
variable {G P : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup P] [TopologicalSpace P]
def centralSplitting (φ : G →* P) (hφ : Continuous φ) (s : P →* G) (hs : Continuous s)
    (hsφ : ∀ p, φ (s p) = p) (hc : ∀ p g, s p * g = g * s p) (H : Subgroup G)
    (hH : ∀ g, g ∈ H ↔ φ g = 1) : G ≃ₜ* H × P where
  toFun g := (⟨g * (s (φ g))⁻¹, (hH _).2 (by rw [map_mul, map_inv, hsφ, mul_inv_cancel])⟩, φ g)
  invFun x := (x.1 : G) * s x.2
  left_inv g := by simp
  right_inv x := by
    obtain ⟨⟨h, hh⟩, p⟩ := x
    have h1 : φ h = 1 := (hH h).1 hh
    have h2 : φ (h * s p) = p := by rw [map_mul, h1, hsφ, one_mul]
    refine Prod.ext (Subtype.ext ?_) h2
    simp [h2]
  map_mul' g g' := by
    have hci : ∀ p g, (s p)⁻¹ * g = g * (s p)⁻¹ := fun p g => by
      rw [← map_inv]; exact hc p⁻¹ g
    refine Prod.ext (Subtype.ext ?_) (map_mul φ g g')
    simp only [map_mul, mul_inv_rev]
    rw [hci (φ g') (s (φ g))⁻¹]
    calc g * g' * ((s (φ g))⁻¹ * (s (φ g'))⁻¹)
        = g * (g' * (s (φ g))⁻¹) * (s (φ g'))⁻¹ := by simp only [mul_assoc]
      _ = g * ((s (φ g))⁻¹ * g') * (s (φ g'))⁻¹ := by rw [hci]
      _ = g * (s (φ g))⁻¹ * (g' * (s (φ g'))⁻¹) := by simp only [mul_assoc]
  continuous_toFun :=
    (Continuous.subtype_mk (continuous_id.mul ((hs.comp hφ).inv)) _).prodMk hφ
  continuous_invFun := (continuous_subtype_val.comp continuous_fst).mul (hs.comp continuous_snd)
end Splitting
section Section
variable {K : Type*} [Field K]
open Classical in

noncomputable def realToCompletion (w : InfinitePlace K) : ℝ →+* w.Completion :=
  if h : w.IsReal then (InfinitePlace.Completion.ringEquivRealOfIsReal h).symm.toRingHom
  else (InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (InfinitePlace.not_isReal_iff_isComplex.mp h)).symm.toRingHom.comp Complex.ofRealHom
theorem norm_realToCompletion (w : InfinitePlace K) (t : ℝ) :
    ‖realToCompletion w t‖ = |t| := by
  unfold realToCompletion
  split_ifs with h
  · set y := (InfinitePlace.Completion.ringEquivRealOfIsReal h).symm t
    have hy : InfinitePlace.Completion.extensionEmbeddingOfIsReal h y = t :=
      (InfinitePlace.Completion.ringEquivRealOfIsReal h).apply_symm_apply t
    have := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h).norm_map_of_map_zero
      (map_zero _) y
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← this, hy, Real.norm_eq_abs]
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp h
    set y := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm (t : ℂ)
    have hy : InfinitePlace.Completion.extensionEmbedding w y = t :=
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).apply_symm_apply t
    have := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) y
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, Complex.ofRealHom_eq_coe]
    rw [← this, hy, Complex.norm_real, Real.norm_eq_abs]
theorem continuous_realToCompletion (w : InfinitePlace K) : Continuous (realToCompletion w) := by
  unfold realToCompletion
  split_ifs with h
  · refine (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h).isEmbedding.isInducing.continuous_iff.2 ?_
    have : (⇑(InfinitePlace.Completion.extensionEmbeddingOfIsReal h) ∘
        ⇑((InfinitePlace.Completion.ringEquivRealOfIsReal h).symm.toRingHom)) = id := by
      funext t; exact (InfinitePlace.Completion.ringEquivRealOfIsReal h).apply_symm_apply t
    rw [this]; exact continuous_id
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp h
    refine (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.isInducing.continuous_iff.2 ?_
    have : (⇑(InfinitePlace.Completion.extensionEmbedding w) ∘
        ⇑(((InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm.toRingHom).comp Complex.ofRealHom))
        = fun t : ℝ => (t : ℂ) := by
      funext t; exact (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).apply_symm_apply t
    rw [this]; exact Complex.continuous_ofReal
noncomputable def posUnit (w : InfinitePlace K) (c : ℝ) : {r : ℝ // 0 < r} →* w.Completionˣ where
  toFun r := Units.mk0 (realToCompletion w ((r : ℝ) ^ c))
    ((map_ne_zero _).2 (Real.rpow_pos_of_pos r.2 c).ne')
  map_one' := by ext; simp
  map_mul' r r' := by
    ext
    simp [Positive.val_mul, Real.mul_rpow r.2.le r'.2.le]
theorem norm_posUnit (w : InfinitePlace K) (c : ℝ) (r : {r : ℝ // 0 < r}) :
    ‖((posUnit w c r : w.Completionˣ) : w.Completion)‖ = (r : ℝ) ^ c := by
  show ‖realToCompletion w ((r : ℝ) ^ c)‖ = _
  rw [norm_realToCompletion, abs_of_pos (Real.rpow_pos_of_pos r.2 c)]
theorem continuous_posUnit (w : InfinitePlace K) (c : ℝ) : Continuous (posUnit w c) := by
  have hv : Continuous fun r : {r : ℝ // 0 < r} => realToCompletion w ((r : ℝ) ^ c) :=
    (continuous_realToCompletion w).comp
      (continuous_subtype_val.rpow_const fun r => Or.inl r.2.ne')
  refine Units.continuous_iff.2 ⟨hv, ?_⟩
  have : (fun r => (((posUnit w c r)⁻¹ : w.Completionˣ) : w.Completion)) =
      fun r : {r : ℝ // 0 < r} => (realToCompletion w ((r : ℝ) ^ c))⁻¹ := by
    funext r; simp [posUnit]
  rw [this]
  exact hv.inv₀ fun r => (map_ne_zero _).2 (Real.rpow_pos_of_pos r.2 c).ne'
variable [NumberField K]
variable (K) in

noncomputable def basePlace : InfinitePlace K := Classical.arbitrary _
variable (K) in

noncomputable def idelePos (n : ℕ) : {r : ℝ // 0 < r} →* GroundTheory.Global.IdeleGroup K :=
  (GroundTheory.Global.IdeleGroup.infiniteEmbedding (basePlace K)).comp
    (posUnit (basePlace K) (1 / ((n : ℝ) * (basePlace K).mult)))
variable (K) in

noncomputable def scalarSection (n : ℕ) :
    {r : ℝ // 0 < r} →* GroundTheory.Automorphic.AdelicGLn.AdelicGL K n :=
  (Matrix.GeneralLinearGroup.scalar (Fin n)).comp (idelePos K n)
variable (K) in

noncomputable def detNorm (n : ℕ) : GroundTheory.Automorphic.AdelicGLn.AdelicGL K n →* {r : ℝ // 0 < r} :=
  (GroundTheory.Global.IdeleGroup.ideleModule K).comp (GroundTheory.Automorphic.AdelicGLn.det K n)
theorem continuous_detNorm (n : ℕ) : Continuous (detNorm K n) :=
  GroundTheory.Global.IdeleGroup.continuous_ideleModule.comp (GroundTheory.Automorphic.AdelicGLn.continuous_det K n)
theorem continuous_idelePos (n : ℕ) : Continuous (idelePos K n) :=
  (GroundTheory.Global.IdeleGroup.continuous_infiniteEmbedding (basePlace K)).comp
    (continuous_posUnit (basePlace K) (1 / ((n : ℝ) * (basePlace K).mult)))
theorem continuous_scalarSection (n : ℕ) : Continuous (scalarSection K n) := by
  obtain ⟨ha1, ha2⟩ := Units.continuous_iff.1 (continuous_idelePos (K := K) n)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have e : (Units.val ∘ scalarSection K n) =
        fun r => Matrix.diagonal fun _ : Fin n => ((idelePos K n r : GroundTheory.Global.IdeleGroup K) :
          NumberField.AdeleRing (NumberField.RingOfIntegers K) K) := by
      funext r
      rw [Function.comp_apply, scalarSection, MonoidHom.comp_apply,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    rw [e]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => ha1)
  · have e : (fun r => (((scalarSection K n r)⁻¹ : GroundTheory.Automorphic.AdelicGLn.AdelicGL K n) :
          Matrix (Fin n) (Fin n) (NumberField.AdeleRing (NumberField.RingOfIntegers K) K))) =
        fun r => Matrix.diagonal fun _ : Fin n => (((idelePos K n r)⁻¹ : GroundTheory.Global.IdeleGroup K) :
          NumberField.AdeleRing (NumberField.RingOfIntegers K) K) := by
      funext r
      rw [scalarSection, MonoidHom.comp_apply, ← map_inv,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    rw [e]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => ha2)
theorem detNorm_scalarSection {n : ℕ} (hn : 0 < n) (r : {r : ℝ // 0 < r}) :
    detNorm K n (scalarSection K n r) = r := by
  apply Subtype.ext
  have hm : (0 : ℝ) < (basePlace K).mult := by exact_mod_cast InfinitePlace.mult_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hdet : GroundTheory.Automorphic.AdelicGLn.det K n (scalarSection K n r) = idelePos K n r ^ n := by
    show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) _) = _
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
  have hpos : idelePos K n r = GroundTheory.Global.IdeleGroup.infiniteEmbedding (basePlace K)
      (posUnit (basePlace K) (1 / ((n : ℝ) * (basePlace K).mult)) r) := rfl
  rw [detNorm, MonoidHom.comp_apply, hdet, map_pow, Positive.val_pow, hpos,
    GroundTheory.Global.IdeleGroup.ideleModule_infiniteEmbedding, norm_posUnit,
    ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul r.2.le, ← Real.rpow_mul r.2.le]
  have : 1 / ((n : ℝ) * (basePlace K).mult) * ((basePlace K).mult : ℕ) * (n : ℕ) = 1 := by
    field_simp
  rw [this, Real.rpow_one]
end Section
noncomputable def adelicGLEquivNormOneProd {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (hn : 0 < n) :
    GroundTheory.Automorphic.AdelicGLn.AdelicGL K n ≃ₜ* ↥(normOneGL K n) × { r : ℝ // 0 < r } :=
  centralSplitting (detNorm K n) (continuous_detNorm n) (scalarSection K n)
    (continuous_scalarSection n) (detNorm_scalarSection hn)
    (fun _ g => Matrix.GeneralLinearGroup.scalar_commute _ g) (normOneGL K n) (fun _ => Iff.rfl)
end GroundTheory.Variant₂.N1


