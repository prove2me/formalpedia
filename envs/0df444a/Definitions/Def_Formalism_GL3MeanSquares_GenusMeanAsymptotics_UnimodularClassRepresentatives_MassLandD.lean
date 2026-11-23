-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandD
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:39.176797+00:00
-- url     : https://prove2.me/theorems/8c20f776-738c-4cf7-970d-8c56ef40011b
-- title:
--   Mass Land D
-- statement:
--   Definitions and structural lemmas for Mass Land D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandD.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandDA
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadAdj_rep_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Polynomial
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def skewSq (w : K) (hw : star w = -w) : cmF K :=
  ⟨w * w, (mem_cmF_iff K _).2 (by rw [star_mul', hw]; ring)⟩
abbrev polE (d : cmF K) : (cmF K)[X] := X ^ 2 - C d
abbrev Ed (d : cmF K) : Type := AdjoinRoot (polE d)
abbrev polKE (d δ : cmF K) : (Ed d)[X] := X ^ 2 - C (algebraMap (cmF K) (Ed d) δ)
abbrev KEd (d δ : cmF K) : Type := AdjoinRoot (polKE d δ)
section
variable (d δ : cmF K) [Fact (Irreducible (polE d))] [Fact (Irreducible (polKE d δ))]
instance numberField_Ed : NumberField (Ed d) :=
  NumberField.of_module_finite (cmF K) (Ed d)
instance numberField_KEd : NumberField (KEd d δ) :=
  NumberField.of_module_finite (Ed d) (KEd d δ)
instance finiteDimensional_KEd : FiniteDimensional (Ed d) (KEd d δ) :=
  QuadAdj.finite_adj _
instance isScalarTower_KEd : IsScalarTower (cmF K) (Ed d) (KEd d δ) :=
  inferInstance
instance isGalois_KEd : IsGalois (Ed d) (KEd d δ) :=
  QuadAdj.isGalois_adj _
end
def reF (x : K) : cmF K :=
  ⟨(x + star x) / 2, (mem_cmF_iff K _).2 (by rw [star_div₀, star_add, star_star, star_ofNat]; ring)⟩
def imF (w : K) (hw : star w = -w) (x : K) : cmF K :=
  ⟨(x - star x) / (2 * w), (mem_cmF_iff K _).2 (by
    rw [star_div₀, star_sub, star_star, star_mul', hw, star_ofNat]; ring)⟩
theorem reF_add (x y : K) : reF (x + y) = reF x + reF y := by
  apply Subtype.ext
  show (x + y + star (x + y)) / 2 = (x + star x) / 2 + (y + star y) / 2
  rw [star_add]; ring
theorem imF_add (w : K) (hw : star w = -w) (x y : K) :
    imF w hw (x + y) = imF w hw x + imF w hw y := by
  apply Subtype.ext
  show (x + y - star (x + y)) / (2 * w) = (x - star x) / (2 * w) + (y - star y) / (2 * w)
  rw [star_add]; ring
theorem reF_coe (a : cmF K) : reF (a : K) = a := by
  apply Subtype.ext
  show ((a : K) + star (a : K)) / 2 = a
  rw [star_coe_cmF]; ring
theorem imF_coe (w : K) (hw : star w = -w) (a : cmF K) : imF w hw (a : K) = 0 := by
  apply Subtype.ext
  show ((a : K) - star (a : K)) / (2 * w) = 0
  rw [star_coe_cmF, sub_self, zero_div]
theorem reF_mul (w : K) (hw0 : w ≠ 0) (hw : star w = -w) (x y : K) :
    reF (x * y) = reF x * reF y + skewSq w hw * (imF w hw x * imF w hw y) := by
  apply Subtype.ext
  show (x * y + star (x * y)) / 2 = (x + star x) / 2 * ((y + star y) / 2) +
    w * w * ((x - star x) / (2 * w) * ((y - star y) / (2 * w)))
  rw [star_mul']
  field_simp
  ring
theorem imF_mul (w : K) (hw0 : w ≠ 0) (hw : star w = -w) (x y : K) :
    imF w hw (x * y) = reF x * imF w hw y + imF w hw x * reF y := by
  apply Subtype.ext
  show (x * y - star (x * y)) / (2 * w) = (x + star x) / 2 * ((y - star y) / (2 * w)) +
    (x - star x) / (2 * w) * ((y + star y) / 2)
  rw [star_mul']
  field_simp
  ring
theorem skew_ne_zero_of_irreducible (w : K) (hw : star w = -w) (d : cmF K)
    [Fact (Irreducible (polE d))] [Fact (Irreducible (polKE d (skewSq w hw)))] : w ≠ 0 := by
  rintro rfl
  have hr := QuadAdj.root_mul_root (algebraMap (cmF K) (Ed d) (skewSq 0 hw))
  have h0 : skewSq (0 : K) hw = 0 := Subtype.ext (mul_zero _)
  have hz : algebraMap (cmF K) (Ed d) (skewSq 0 hw) = 0 := by rw [h0, map_zero]
  have hr0 := mul_self_eq_zero.1 (hr.trans ((congrArg (AdjoinRoot.of _) hz).trans (map_zero _)))
  have := QuadAdj.rep_eq_zero (algebraMap (cmF K) (Ed d) (skewSq 0 hw)) (a := 0) (b := 1) (by
    rw [map_zero, map_one, hr0]; ring)
  exact one_ne_zero this.2
section
variable (w : K) (hw0 : w ≠ 0) (hw : star w = -w) (d : cmF K) [Fact (Irreducible (polE d))]
  [Fact (Irreducible (polKE d (skewSq w hw)))]
def ιK : K →ₐ[cmF K] KEd d (skewSq w hw) where
  toFun x := algebraMap (cmF K) (KEd d (skewSq w hw))
      ⟨(x + star x) / 2, (mem_cmF_iff K _).2 (by rw [star_div₀, star_add, star_star, star_ofNat]; ring)⟩ +
    algebraMap (cmF K) (KEd d (skewSq w hw))
      ⟨(x - star x) / (2 * w), (mem_cmF_iff K _).2 (by
        rw [star_div₀, star_sub, star_star, star_mul', hw, star_ofNat]; ring)⟩ *
      AdjoinRoot.root (polKE d (skewSq w hw))
  map_one' := by
    show algebraMap (cmF K) (KEd d (skewSq w hw)) (reF 1) +
      algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw 1) * AdjoinRoot.root _ = 1
    have h1 : (1 : K) = ((1 : cmF K) : K) := rfl
    rw [h1, reF_coe, imF_coe, map_one, map_zero, zero_mul, add_zero]
  map_mul' x y := by
    show algebraMap (cmF K) (KEd d (skewSq w hw)) (reF (x * y)) +
      algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw (x * y)) * AdjoinRoot.root _ =
      (algebraMap (cmF K) (KEd d (skewSq w hw)) (reF x) +
        algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw x) * AdjoinRoot.root _) *
      (algebraMap (cmF K) (KEd d (skewSq w hw)) (reF y) +
        algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw y) * AdjoinRoot.root _)
    have hw0' := skew_ne_zero_of_irreducible w hw d
    have hr : AdjoinRoot.root (polKE d (skewSq w hw)) * AdjoinRoot.root (polKE d (skewSq w hw)) =
        algebraMap (cmF K) (KEd d (skewSq w hw)) (skewSq w hw) :=
      QuadAdj.root_mul_root (algebraMap (cmF K) (Ed d) (skewSq w hw))
    rw [reF_mul w hw0' hw, imF_mul w hw0' hw]
    simp only [map_add, map_mul]
    linear_combination (-(algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw x) *
      algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw y))) * hr
  map_zero' := by
    show algebraMap (cmF K) (KEd d (skewSq w hw)) (reF 0) +
      algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw 0) * AdjoinRoot.root _ = 0
    have h1 : (0 : K) = ((0 : cmF K) : K) := rfl
    rw [h1, reF_coe, imF_coe, map_zero, zero_mul, add_zero]
  map_add' x y := by
    show algebraMap (cmF K) (KEd d (skewSq w hw)) (reF (x + y)) +
      algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw (x + y)) * AdjoinRoot.root _ =
      (algebraMap (cmF K) (KEd d (skewSq w hw)) (reF x) +
        algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw x) * AdjoinRoot.root _) +
      (algebraMap (cmF K) (KEd d (skewSq w hw)) (reF y) +
        algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw y) * AdjoinRoot.root _)
    rw [reF_add, imF_add, map_add, map_add]
    ring
  commutes' r := by
    show algebraMap (cmF K) (KEd d (skewSq w hw)) (reF (r : K)) +
      algebraMap (cmF K) (KEd d (skewSq w hw)) (imF w hw (r : K)) * AdjoinRoot.root _ =
      algebraMap (cmF K) (KEd d (skewSq w hw)) r
    rw [reF_coe, imF_coe, map_zero, zero_mul, add_zero]
end
end Formalism.HermitianLattices.Ext.L3


