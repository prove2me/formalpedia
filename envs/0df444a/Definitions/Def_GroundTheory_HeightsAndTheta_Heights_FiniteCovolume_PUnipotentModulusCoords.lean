-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusCoords
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusCoords
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T07:44:16.235233+00:00
-- url     : https://prove2.me/theorems/06796ebb-90ff-4d9c-9e0c-84fbda96d42c
-- title:
--   PUnipotent Modulus Coords
-- statement:
--   Definitions and structural lemmas for PUnipotent Modulus Coords, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusCoords.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramAtData
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramAtData_proof_6f69e474274d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HermAtPlace_proof_4b36a3148377
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_heisMat_ad6efea24ef6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_heisS_036f0895ef05
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_add_left_21ed53f20908
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_add_right_73a7d76a7d0e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_conj_a26db4eadf30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_neg_left_ff70cfa4a8ef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_neg_right_013bd065af05
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_self_im_82678c31a9eb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_smul_right_b5b6ef42f985
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_zero_left_b51af4b2c968
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_zero_right_6b8edb0e313a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mulVec_debb3da7c3fb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mulVec_self_ae871acdba7c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mul_0b194300fa17
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_unitary_b973147ebfea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_zero_6a323343603e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisS_spec_d0b72175b660
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_archUnitary_0eab686fdef0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
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
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι] in
theorem real_smul_vec (c : ℝ) (z : ι → ℂ) : c • z = (c : ℂ) • z := by
  ext i
  simp [Complex.real_smul]
omit [Fintype ι] [DecidableEq ι] in
theorem map_conj_transpose (M : Matrix ι ι ℂ) : (M.map (starRingEnd ℂ))ᵀ = Mᴴ := rfl
theorem hyperbolic_at_place (h : HermitianForm F E W) (v : Basis ι E W) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (w : InfinitePlace E) :
    (gramAt h v w).IsHermitian ∧ IsUnit (gramAt h v w).det ∧
      hForm (gramAt h v w) (vecAt v x₀ w) (vecAt v x₀ w) = 0 ∧
      hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v w₀ w) = 0 ∧
      hForm (gramAt h v w) (vecAt v x₀ w) (vecAt v w₀ w) = 1 := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨(GramAtData.proof h v w).1, (GramAtData.proof h v w).2, ?_, ?_, ?_⟩
  · rw [hForm, ← HermAtPlace.proof h v w, h1, map_zero]
  · rw [hForm, ← HermAtPlace.proof h v w, h2, map_zero]
  · rw [hForm, ← HermAtPlace.proof h v w, h3, map_one]
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in

theorem archUnitary_at_place {h : HermitianForm F E W} {v : Basis ι E W} (g : archUnitary h v)
    (w : InfinitePlace E) :
    (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ))ᴴ * gramAt h v w *
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = gramAt h v w := by
  rw [← map_conj_transpose]
  exact mem_archUnitary.1 g.2 w
def heisY (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :
    Submodule ℝ (InfinitePlace E → ι → ℂ) where
  carrier := {y | ∀ w, hForm (gramAt h v w) (vecAt v x₀ w) (y w) = 0 ∧
    hForm (gramAt h v w) (vecAt v w₀ w) (y w) = 0}
  add_mem' {y z} hy hz w := by
    simp only [Pi.add_apply, hForm_add_right, (hy w).1, (hz w).1, (hy w).2, (hz w).2, add_zero,
      and_self]
  zero_mem' w := ⟨hForm_zero_right _ _, hForm_zero_right _ _⟩
  smul_mem' c y hy w := by
    simp only [Pi.smul_apply, real_smul_vec, hForm_smul_right, (hy w).1, (hy w).2, mul_zero,
      and_self]
abbrev HeisCoord (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :=
  heisY h v x₀ w₀ × (InfinitePlace E → ℝ)
def heisMatAt (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W)
    (y : InfinitePlace E → ι → ℂ) (t : InfinitePlace E → ℝ) (w : InfinitePlace E) :
    Matrix ι ι ℂ :=
  heisMat (gramAt h v w) (vecAt v x₀ w) (y w) (heisS (gramAt h v w) (y w) (t w))
omit [DecidableEq ι] in
theorem heisS_add {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (y₁ y₂ : ι → ℂ) (t₁ t₂ : ℝ) :
    heisS H y₁ t₁ + heisS H y₂ t₂ - hForm H y₁ y₂ =
      heisS H (y₁ + y₂) (t₁ + t₂ - (hForm H y₁ y₂).im) := by
  have hs : (heisS H y₁ t₁ + heisS H y₂ t₂ - hForm H y₁ y₂) +
      starRingEnd ℂ (heisS H y₁ t₁ + heisS H y₂ t₂ - hForm H y₁ y₂) +
      hForm H (y₁ + y₂) (y₁ + y₂) = 0 := by
    have e1 := heisS_spec hH y₁ t₁
    have e2 := heisS_spec hH y₂ t₂
    have e3 := hForm_conj hH y₁ y₂
    simp only [map_add, map_sub, hForm_add_left, hForm_add_right]
    linear_combination e1 + e2 - e3
  rw [eq_heisS hs]
  congr 1
section Coords
variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}
theorem heisMatAt_mul (hp : IsHyperbolicPair h x₀ w₀) {y₁ y₂ : InfinitePlace E → ι → ℂ}
    (hy₁ : y₁ ∈ heisY h v x₀ w₀) (hy₂ : y₂ ∈ heisY h v x₀ w₀) (t₁ t₂ : InfinitePlace E → ℝ)
    (w : InfinitePlace E) :
    heisMatAt h v x₀ y₁ t₁ w * heisMatAt h v x₀ y₂ t₂ w = heisMatAt h v x₀ (y₁ + y₂)
      (t₁ + t₂ - fun w => (hForm (gramAt h v w) (y₁ w) (y₂ w)).im) w := by
  obtain ⟨hH, -, ha, -, -⟩ := hyperbolic_at_place h v hp w
  rw [heisMatAt, heisMatAt, heisMat_mul hH ha (hy₁ w).1 (hy₂ w).1, heisS_add hH, heisMatAt]
  rfl
def heisUnit (hp : IsHyperbolicPair h x₀ w₀) (y : heisY h v x₀ w₀) (t : InfinitePlace E → ℝ)
    (w : InfinitePlace E) : GL ι ℂ where
  val := heisMatAt h v x₀ y t w
  inv := heisMatAt h v x₀ (-(y : InfinitePlace E → ι → ℂ)) (-t) w
  val_inv := by
    obtain ⟨hH, -, -, -, -⟩ := hyperbolic_at_place h v hp w
    rw [heisMatAt_mul hp y.2 (neg_mem y.2), heisMatAt]
    simp only [add_neg_cancel, Pi.zero_apply, Pi.sub_apply, Pi.add_apply, Pi.neg_apply,
      hForm_neg_right, Complex.neg_im, hForm_self_im hH]
    simp only [heisS, hForm_zero_left, Complex.zero_re, neg_zero, zero_div, sub_self]
    exact heisMat_zero
  inv_val := by
    obtain ⟨hH, -, -, -, -⟩ := hyperbolic_at_place h v hp w
    rw [heisMatAt_mul hp (neg_mem y.2) y.2, heisMatAt]
    simp only [neg_add_cancel, Pi.zero_apply, Pi.sub_apply, Pi.add_apply, Pi.neg_apply,
      hForm_neg_left, Complex.neg_im, hForm_self_im hH]
    simp only [heisS, hForm_zero_left, Complex.zero_re, neg_zero, zero_div, sub_self]
    exact heisMat_zero
def heisPoint (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀) : unipRadical h v x₀ :=
  ⟨⟨fun w => heisUnit hp p.1 p.2 w, mem_archUnitary.2 fun w => by
      obtain ⟨hH, -, ha, -, -⟩ := hyperbolic_at_place h v hp w
      rw [map_conj_transpose]
      exact heisMat_unitary hH ha (p.1.2 w).1 (heisS_spec hH _ _)⟩,
    mem_unipRadical.2 fun w => by
      obtain ⟨hH, -, ha, -, -⟩ := hyperbolic_at_place h v hp w
      refine ⟨heisMat_mulVec_self hH ha (p.1.2 w).1 _, fun z hz => ⟨-hForm (gramAt h v w)
        ((p.1 : InfinitePlace E → ι → ℂ) w) z, ?_⟩⟩
      change heisMat _ _ _ _ *ᵥ z = _
      rw [heisMat_mulVec, show hForm (gramAt h v w) (vecAt v x₀ w) z = 0 from hz]
      simp only [zero_smul, add_zero, neg_smul, sub_eq_add_neg]⟩
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in

theorem unipRadical_at_place (n : unipRadical h v x₀) (w : InfinitePlace E) :
    (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)ᴴ * gramAt h v w *
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = gramAt h v w ∧
    (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      vecAt v x₀ w ∧
    ∀ z, hForm (gramAt h v w) (vecAt v x₀ w) z = 0 → ∃ c : ℂ,
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z =
        z + c • vecAt v x₀ w :=
  ⟨archUnitary_at_place _ w, (mem_unipRadical.1 n.2 w).1, (mem_unipRadical.1 n.2 w).2⟩
def heisU (n : unipRadical h v x₀) (w : InfinitePlace E) : ι → ℂ :=
  (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v w₀ w -
    vecAt v w₀ w
def heisYOf (n : unipRadical h v x₀) : InfinitePlace E → ι → ℂ := fun w =>
  heisU (w₀ := w₀) n w - hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w) • vecAt v x₀ w
theorem heisYOf_spec (hp : IsHyperbolicPair h x₀ w₀) (n : unipRadical h v x₀)
    (w : InfinitePlace E) :
    hForm (gramAt h v w) (vecAt v x₀ w) (heisYOf (w₀ := w₀) n w) = 0 ∧
    hForm (gramAt h v w) (vecAt v w₀ w) (heisYOf (w₀ := w₀) n w) = 0 ∧
    hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w) +
      starRingEnd ℂ (hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w)) +
      hForm (gramAt h v w) (heisYOf (w₀ := w₀) n w) (heisYOf (w₀ := w₀) n w) = 0 ∧
    (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      heisMat (gramAt h v w) (vecAt v x₀ w) (heisYOf (w₀ := w₀) n w)
        (hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w)) := by
  obtain ⟨hH, -, ha, hb, hab⟩ := hyperbolic_at_place h v hp w
  obtain ⟨hn, hna, hn'⟩ := unipRadical_at_place n w
  exact eq_heisMat hH ha hb hab hn hna hn'
def heisCoordOf (hp : IsHyperbolicPair h x₀ w₀) (n : unipRadical h v x₀) : HeisCoord h v x₀ w₀ :=
  (⟨heisYOf n, fun w => ⟨(heisYOf_spec hp n w).1, (heisYOf_spec hp n w).2.1⟩⟩,
    fun w => (hForm (gramAt h v w) (vecAt v w₀ w) (heisU (w₀ := w₀) n w)).im)
end Coords
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


