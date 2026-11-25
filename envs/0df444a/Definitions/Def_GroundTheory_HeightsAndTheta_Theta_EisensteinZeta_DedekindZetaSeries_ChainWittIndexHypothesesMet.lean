-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ChainWittIndexHypothesesMet
-- name    : GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ChainWittIndexHypothesesMet
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T09:00:41.484185+00:00
-- url     : https://prove2.me/theorems/6a589fe6-0216-5ad6-879d-1e2e93a4c49c
-- title:
--   Chain Witt Index Hypotheses Met
-- statement:
--   Definitions and structural lemmas for Chain Witt Index Hypotheses Met, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/ChainWittIndexHypothesesMet.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_HeightGeSecondCubicBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Signature
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Parabolic
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
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
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Theta
open Module NumberField GroundTheory.Automorphic
universe u
def ChainWittIndex.Statement (F E : Type u) [Field F] [NumberField F] [IsTotallyReal F]
    [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] : Prop :=
  ∀ P : ChainParams, ∀ j : ℕ, j ≤ P.m →
    ∀ (V : Type u) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (h : HermitianForm F E V) (b : Basis (Fin (P.rk j)) E V),
      (∀ v : InfinitePlace F, signature h v = (P.rk j - P.nu j, P.nu j)) →
      wittIndex F (gram h.toSesq b) = P.nu j
instance isTotallyComplex_gaussQ : IsTotallyComplex GaussQ where
  isComplex v := by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff]
    intro hv
    set φ := v.embedding
    have hsq : φ (QuadraticAlgebra.omega) * φ (QuadraticAlgebra.omega) = -1 := by
      rw [← map_mul, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
      simp
    have him : (φ (QuadraticAlgebra.omega)).im = 0 := by
      have := RingHom.congr_fun hv (QuadraticAlgebra.omega)
      rw [ComplexEmbedding.conjugate_coe_eq] at this
      exact Complex.conj_eq_iff_im.1 this
    have hre := congrArg Complex.re hsq
    simp only [Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re, Complex.one_re] at hre
    nlinarith [mul_self_nonneg (φ (QuadraticAlgebra.omega)).re]
def chainWittExampleSigns : Fin 3 → ℚˣ := ![1, 1, -1]
noncomputable def chainWittExampleForm : HermitianForm ℚ GaussQ (Fin 3 → GaussQ) :=
  diagForm chainWittExampleSigns
end GroundTheory.Heights₂.Theta


