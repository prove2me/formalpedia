-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PTorusEmbedding
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PTorusEmbedding
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T04:19:47.113082+00:00
-- url     : https://prove2.me/theorems/299f3b58-1021-453b-8ade-8536e6ba0aec
-- title:
--   PTorus Embedding
-- statement:
--   Definitions and structural lemmas for PTorus Embedding, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTorusEmbedding.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusEmbedding
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
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
namespace TorusEmbedding
section Linear
variable {ι : Type*} [Fintype ι]
def pair (H : Matrix ι ι ℂ) (u z : ι → ℂ) : ℂ := star u ⬝ᵥ (H *ᵥ z)
variable {H : Matrix ι ι ℂ} {X Y : ι → ℂ}
theorem pair_add (u z z' : ι → ℂ) : pair H u (z + z') = pair H u z + pair H u z' := by
  simp [pair, mulVec_add, dotProduct_add]
theorem pair_smul (u z : ι → ℂ) (c : ℂ) : pair H u (c • z) = c * pair H u z := by
  simp [pair, mulVec_smul, dotProduct_smul]
theorem add_pair (u u' z : ι → ℂ) : pair H (u + u') z = pair H u z + pair H u' z := by
  simp [pair, add_dotProduct]
theorem smul_pair (u z : ι → ℂ) (c : ℂ) : pair H (c • u) z = starRingEnd ℂ c * pair H u z := by
  simp [pair, star_smul, smul_dotProduct]
theorem pair_swap (hH : H.IsHermitian) (u z : ι → ℂ) :
    pair H u z = starRingEnd ℂ (pair H z u) := by
  rw [pair, pair, dotProduct_mulVec, ← RCLike.star_def, ← star_dotProduct_star, star_star,
    star_mulVec, hH.eq]
variable [DecidableEq ι]
def torusMat (H : Matrix ι ι ℂ) (X Y : ι → ℂ) (s t : ℂ) : Matrix ι ι ℂ :=
  1 + (s - 1) • vecMulVec X (star Y ᵥ* H) + (t - 1) • vecMulVec Y (star X ᵥ* H)
theorem torusMat_mulVec (s t : ℂ) (z : ι → ℂ) :
    torusMat H X Y s t *ᵥ z = z + ((s - 1) * pair H Y z) • X + ((t - 1) * pair H X z) • Y := by
  simp only [torusMat, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, pair,
    dotProduct_mulVec, op_smul_eq_smul, smul_smul]
theorem torusMat_one_one : torusMat H X Y 1 1 = 1 := by
  simp [torusMat]
theorem pair_Y_torusMat (hYY : pair H Y Y = 0) (hYX : pair H Y X = 1) (s t : ℂ) (z : ι → ℂ) :
    pair H Y (torusMat H X Y s t *ᵥ z) = s * pair H Y z := by
  rw [torusMat_mulVec, pair_add, pair_add, pair_smul, pair_smul, hYX, hYY]; ring
theorem pair_X_torusMat (hXX : pair H X X = 0) (hXY : pair H X Y = 1) (s t : ℂ) (z : ι → ℂ) :
    pair H X (torusMat H X Y s t *ᵥ z) = t * pair H X z := by
  rw [torusMat_mulVec, pair_add, pair_add, pair_smul, pair_smul, hXX, hXY]; ring
theorem torusMat_mul (hXX : pair H X X = 0) (hYY : pair H Y Y = 0) (hXY : pair H X Y = 1)
    (hYX : pair H Y X = 1) (s t s' t' : ℂ) :
    torusMat H X Y s t * torusMat H X Y s' t' = torusMat H X Y (s * s') (t * t') := by
  refine mulVec_injective (funext fun z => ?_)
  rw [← mulVec_mulVec, torusMat_mulVec s t, pair_Y_torusMat hYY hYX, pair_X_torusMat hXX hXY,
    torusMat_mulVec s' t', torusMat_mulVec]
  module
theorem torusMat_unitary (hH : H.IsHermitian) (hXX : pair H X X = 0) (hYY : pair H Y Y = 0)
    (hXY : pair H X Y = 1) (hYX : pair H Y X = 1) (s t : ℂ) (hst : starRingEnd ℂ s * t = 1) :
    (torusMat H X Y s t)ᴴ * H * torusMat H X Y s t = H := by
  have hts : starRingEnd ℂ t * s = 1 := by
    have := congrArg (starRingEnd ℂ) hst
    simpa [mul_comm] using this
  have key : ∀ u z : ι → ℂ, pair H (torusMat H X Y s t *ᵥ u) (torusMat H X Y s t *ᵥ z) =
      pair H u z := by
    intro u z
    conv_lhs => rw [torusMat_mulVec s t u]
    rw [add_pair, add_pair, smul_pair, smul_pair, pair_Y_torusMat hYY hYX,
      pair_X_torusMat hXX hXY, torusMat_mulVec, pair_add, pair_add, pair_smul, pair_smul,
      pair_swap hH u X, pair_swap hH u Y]
    simp only [map_mul, map_sub, map_one]
    linear_combination (pair H X z * starRingEnd ℂ (pair H Y u)) * hst +
      (pair H Y z * starRingEnd ℂ (pair H X u)) * hts
  refine mulVec_injective (funext fun z => ?_)
  refine dotProduct_eq _ _ fun u => ?_
  rw [dotProduct_comm, dotProduct_comm (H *ᵥ z)]
  have := key (star u) z
  simp only [pair, star_star] at this
  rw [← this, star_mulVec, star_star]
  simp only [dotProduct_mulVec, vecMul_vecMul]
def torusGL (H : Matrix ι ι ℂ) (X Y : ι → ℂ) (hXX : pair H X X = 0) (hYY : pair H Y Y = 0)
    (hXY : pair H X Y = 1) (hYX : pair H Y X = 1) (a : ℂˣ) : GL ι ℂ where
  val := torusMat H X Y a (starRingEnd ℂ ↑a⁻¹)
  inv := torusMat H X Y ↑a⁻¹ (starRingEnd ℂ a)
  val_inv := by
    rw [torusMat_mul hXX hYY hXY hYX, Units.mul_inv, ← map_mul, Units.inv_mul, map_one,
      torusMat_one_one]
  inv_val := by
    rw [torusMat_mul hXX hYY hXY hYX, Units.inv_mul, ← map_mul, Units.mul_inv, map_one,
      torusMat_one_one]
end Linear
section Places
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W}
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in

theorem place_pairs (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (w : InfinitePlace E) :
    pair (gramAt h v w) (vecAt v x₀ w) (vecAt v x₀ w) = 0 ∧
      pair (gramAt h v w) (vecAt v w₀ w) (vecAt v w₀ w) = 0 ∧
      pair (gramAt h v w) (vecAt v x₀ w) (vecAt v w₀ w) = 1 ∧
      pair (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
  obtain ⟨hxx, hww, hxw⟩ := hp
  have e : ∀ x y, pair (gramAt h v w) (vecAt v x w) (vecAt v y w) = w.embedding (h.toSesq x y) :=
    fun x y => (h1 w x y).symm
  refine ⟨by rw [e, hxx, map_zero], by rw [e, hww, map_zero], by rw [e, hxw, map_one], ?_⟩
  rw [pair_swap (h2 w).1, e, hxw, map_one, map_one]
variable (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v) {x₀ w₀ : W}
  (hp : IsHyperbolicPair h x₀ w₀)
def torusAt (w : InfinitePlace E) (a : ℂˣ) : GL ι ℂ :=
  torusGL (gramAt h v w) (vecAt v x₀ w) (vecAt v w₀ w) (place_pairs h1 h2 hp w).1
    (place_pairs h1 h2 hp w).2.1 (place_pairs h1 h2 hp w).2.2.1 (place_pairs h1 h2 hp w).2.2.2 a
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in
theorem torusAt_mem (a : InfinitePlace E → ℂˣ) :
    (fun w => torusAt h1 h2 hp w (a w)) ∈ archUnitary h v := by
  rw [mem_archUnitary]
  intro w
  obtain ⟨hXX, hYY, hXY, hYX⟩ := place_pairs h1 h2 hp w
  have hc : ∀ M : Matrix ι ι ℂ, (M.map (starRingEnd ℂ))ᵀ = Mᴴ := fun M => by
    ext i j; simp [conjTranspose_apply]
  rw [hc]
  refine torusMat_unitary (h2 w).1 hXX hYY hXY hYX _ _ ?_
  rw [← map_mul, Units.mul_inv, map_one]
def torusHom : (InfinitePlace E → ℂˣ) →* archUnitary h v where
  toFun a := ⟨fun w => torusAt h1 h2 hp w (a w), torusAt_mem h1 h2 hp a⟩
  map_one' := Subtype.ext (funext fun w => Units.ext (by
    simp [torusAt, torusGL, torusMat_one_one]))
  map_mul' a b := Subtype.ext (funext fun w => Units.ext (by
    obtain ⟨hXX, hYY, hXY, hYX⟩ := place_pairs h1 h2 hp w
    simp only [torusAt, torusGL, Subgroup.coe_mul, Pi.mul_apply, Units.val_mul]
    rw [torusMat_mul hXX hYY hXY hYX, ← map_mul, ← Units.val_mul, ← Units.val_mul,
      ← _root_.mul_inv_rev, mul_comm (b w)]))
end Places
section Main
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
end Main
end TorusEmbedding
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


