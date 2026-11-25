-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Unimodular_IndefiniteUnitary
-- name    : GroundTheory_HeightsAndTheta_Theta_Unimodular_IndefiniteUnitary
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:55:40.796329+00:00
-- url     : https://prove2.me/theorems/ec73878b-ab4f-4ea3-a18e-5e11a4c93e1a
-- title:
--   Indefinite Unitary
-- statement:
--   Definitions and structural lemmas for Indefinite Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Unimodular/IndefiniteUnitary.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Cartan
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
import Theorems.Thm_GroundTheory_Automorphic_conjCME_one
import Theorems.Thm_GroundTheory_Automorphic_indefJ_conjTranspose
import Theorems.Thm_GroundTheory_Automorphic_mulEquivHaarChar_conjCME_eq_one
import Theorems.Thm_GroundTheory_Automorphic_mulEquivHaarChar_conjCME_inv
import Theorems.Thm_GroundTheory_Automorphic_mulEquivHaarChar_conjCME_mul
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.conjCME_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a


set_option autoImplicit false
namespace GroundTheory.Heights₂.Theta
open MeasureTheory Matrix GroundTheory.Automorphic
open scoped NNReal ComplexOrder MatrixOrder
noncomputable section
variable {p q : ℕ}
def indefJElem (p q : ℕ) : indefiniteUnitaryGroup p q :=
  upqOfMatrix (indefJ p q) (by rw [indefJ_conjTranspose, indefJ_mul_self, Matrix.one_mul])
theorem indefJElem_mul_self : indefJElem p q * indefJElem p q = 1 :=
  Subtype.ext (Units.ext (indefJ_mul_self p q))
theorem indefJElem_mul_mul_indefJElem (s : cartanPos p q) :
    indefJElem p q * upqOfMatrix s.1 s.2.2 * indefJElem p q = (upqOfMatrix s.1 s.2.2)⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  change indefJ p q * s.1 * indefJ p q = indefJ p q * s.1ᴴ * indefJ p q
  rw [s.2.1.isHermitian.eq]
variable [MeasurableSpace (indefiniteUnitaryGroup p q)] [BorelSpace (indefiniteUnitaryGroup p q)]
theorem mulEquivHaarChar_conjCME_indefiniteUnitary (g : indefiniteUnitaryGroup p q) :
    mulEquivHaarChar (conjCME g) = 1 := by
  set ks := cartanHomeomorph.symm g with hks
  set s : indefiniteUnitaryGroup p q := upqOfMatrix ks.2.1 ks.2.2.2 with hs
  have hg : g = (ks.1 : indefiniteUnitaryGroup p q) * s :=
    (cartanHomeomorph.apply_symm_apply g).symm
  rw [hg, mulEquivHaarChar_conjCME_mul,
    mulEquivHaarChar_conjCME_eq_one isCompact_maxCompact_indefiniteUnitary ks.1.2, one_mul]
  set J := indefJElem p q
  have hJ : mulEquivHaarChar (conjCME J) * mulEquivHaarChar (conjCME J) = 1 := by
    rw [← mulEquivHaarChar_conjCME_mul, indefJElem_mul_self, conjCME_one, mulEquivHaarChar_refl]
  have h1 : mulEquivHaarChar (conjCME s⁻¹) = mulEquivHaarChar (conjCME s) := by
    rw [← indefJElem_mul_mul_indefJElem ks.2, mulEquivHaarChar_conjCME_mul,
      mulEquivHaarChar_conjCME_mul]
    calc mulEquivHaarChar (conjCME J) * mulEquivHaarChar (conjCME s) *
          mulEquivHaarChar (conjCME J)
        = mulEquivHaarChar (conjCME s) *
            (mulEquivHaarChar (conjCME J) * mulEquivHaarChar (conjCME J)) := by ring
      _ = mulEquivHaarChar (conjCME s) := by rw [hJ, mul_one]
  have h2 := mulEquivHaarChar_conjCME_inv s
  rw [h1] at h2
  have h3 : ((mulEquivHaarChar (conjCME s) : ℝ≥0) : ℝ) * (mulEquivHaarChar (conjCME s) : ℝ) = 1 := by
    exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ (mulEquivHaarChar (conjCME s) : ℝ) := NNReal.coe_nonneg _
  have h5 : ((mulEquivHaarChar (conjCME s) : ℝ≥0) : ℝ) = 1 := by nlinarith
  exact_mod_cast h5
theorem isMulRightInvariant_indefiniteUnitary (μ : Measure (indefiniteUnitaryGroup p q))
    [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have hc : μ.map (conjCME g⁻¹) = μ := by
    have e := mulEquivHaarChar_smul_map μ (conjCME g⁻¹)
    rwa [mulEquivHaarChar_conjCME_indefiniteUnitary, one_smul] at e
  have hfun : (fun x => x * g) = (fun x => g * x) ∘ (conjCME g⁻¹) := by
    funext x
    simp [mul_assoc]
  have hm : Measurable (conjCME g⁻¹) := (map_continuous (conjCME g⁻¹)).measurable
  rw [hfun, ← Measure.map_map (measurable_const_mul g) hm, hc, map_mul_left_eq_self]
instance (μ : Measure (indefiniteUnitaryGroup p q)) [μ.IsHaarMeasure] : μ.IsMulRightInvariant :=
  isMulRightInvariant_indefiniteUnitary μ
example : (Measure.haar : Measure (indefiniteUnitaryGroup p q)).IsMulRightInvariant :=
  inferInstance
end
end GroundTheory.Heights₂.Theta


