-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_SpecMapAwayFnEquivAwayChart
-- name    : Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_SpecMapAwayFnEquivAwayChart
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:16:27.0259+00:00
-- url     : https://prove2.me/theorems/54b16734-ac35-496c-b806-42bf4d7c6671
-- title:
--   Spec Map Away Fn Equiv Away Chart
-- statement:
--   Definitions and structural lemmas for Spec Map Away Fn Equiv Away Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/SpecMapAwayFnEquivAwayChart.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Theorems.Thm_GlobalTheory_ProjFrac_awayToSection_mk
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_appLinearBase_apply
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_baseRingHom_comp_SpecMap
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_baseRingHom_res
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_TangentOrigin_eq_spec_fromSpec
import Theorems.Thm_GlobalTheory_TangentOrigin_evalPt_res
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_isAffineOpen_coordOpen
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
import Theorems.Thm_ReciprocityTheory_AnForm_R_toSpecZero_appLE_basicOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.Qcqs.appLinearBase_apply
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap resG constFn)
open GlobalTheory.ProjFrac GlobalTheory.QCoh.Qcqs GlobalTheory.TangentOrigin
namespace GlobalTheory
namespace WeierstrassCurve
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
def constOn (U : (scheme W).Opens) : R →+* Γ(scheme W, U) := (baseRingHom (toSpec W) U).hom
def ratioOn (U : (scheme W).Opens) (i : Fin 3) (hU : U ≤ coordOpen W i) (j : Fin 3) :
    Γ(scheme W, U) :=
  frac (grading W) U (coord W j) (coord W i) (coord_mem W j) (coord_mem W i) hU
abbrev ratio (i j : Fin 3) : Γ(scheme W, coordOpen W i) := ratioOn W (coordOpen W i) i le_rfl j
section
variable {W} {U V : (scheme W).Opens} {i j k : Fin 3}
theorem resG_constOn (h : V ≤ U) (r : R) : resG _ h (constOn W U r) = constOn W V r :=
  baseRingHom_res (toSpec W) h r
@[simp] theorem ratioOn_self (hi : U ≤ coordOpen W i) : ratioOn W U i hi i = 1 := frac_self
end
def awayFnEquiv (i : Fin 3) : AwayRing W i ≃+* Γ(scheme W, coordOpen W i) :=
  (Proj.basicOpenIsoAway (grading W) (coord W i) (coord_mem W i) one_pos).commRingCatIsoToRingEquiv
@[simp] theorem awayFnEquiv_awayCoord (i j : Fin 3) :
    awayFnEquiv W i (awayCoord W i j) = ratio W i j :=
  (awayToSection_mk (coord_mem W i) 1 (coord_mem W j)).trans (frac_eq (by ring))
@[simp] theorem awayFnEquiv_awayConst (i : Fin 3) (r : R) :
    awayFnEquiv W i (awayConst W i r) = constOn W (coordOpen W i) r := by
  have h := baseRingHom_comp_SpecMap (Proj.toSpecZero (grading W))
    (CommRingCat.ofHom (algebraMap R (grading W 0))) (coordOpen W i)
  have h' := ReciprocityTheory.AnForm.R.toSpecZero_appLE_basicOpen (grading W) (coord_mem W i) one_pos
  exact (congrArg (fun φ => φ.hom r) (h.trans (congrArg (_ ≫ ·) h'))).symm
section
variable {W} {U : (scheme W).Opens} {i : Fin 3}
theorem equation_ratioOn (hi : U ≤ coordOpen W i) :
    (W.map (constOn W U)).toProjective.Equation (ratioOn W U i hi) := by
  have h := ((isUnimodularSol_awayCoord W i).map_comp
    ((resG _ hi).comp (awayFnEquiv W i : AwayRing W i →+* _))).equation
  have e₁ : ((resG _ hi).comp (awayFnEquiv W i : AwayRing W i →+* _)).comp (awayConst W i) =
      constOn W U := RingHom.ext fun r =>
    (congrArg (resG _ hi) (awayFnEquiv_awayConst W i r)).trans (resG_constOn hi r)
  have e₂ : ((resG _ hi).comp (awayFnEquiv W i : AwayRing W i →+* _)) ∘ awayCoord W i =
      ratioOn W U i hi := funext fun j => congrArg (resG _ hi) (awayFnEquiv_awayCoord W i j)
  rwa [e₁, e₂] at h
end
theorem SpecMap_awayFnEquiv_awayChart (i : Fin 3) :
    spMap (awayFnEquiv W i : AwayRing W i →+* Γ(scheme W, coordOpen W i)) ≫ awayChart W i =
      (isAffineOpen_coordOpen W i).fromSpec := by
  have h := Proj.basicOpenIsoSpec_hom (grading W) (coord W i) (coord_mem W i) one_pos
  have hU := Proj.isAffineOpen_basicOpen (grading W) (coord W i) (coord_mem W i) one_pos
  change Spec.map (Proj.awayToSection (grading W) (coord W i)) ≫
    Proj.awayι (grading W) (coord W i) (coord_mem W i) one_pos = hU.fromSpec
  rw [Proj.awayι, IsAffineOpen.fromSpec, ← Category.assoc]
  congr 1
  rw [Iso.comp_inv_eq, h, Iso.eq_inv_comp]
  rfl
section
variable {W} {A : Type} [CommRing A]
theorem evalPt_ptHom_ratioOn_mul (ρ : R →+* A) (P : Fin 3 → A) (hP : IsUnimodularSol (W.map ρ) P)
    {U : (scheme W).Opens} {i : Fin 3} (hi : U ≤ coordOpen W i) (h : ⊤ ≤ ptHom W ρ P hP ⁻¹ᵁ U)
    (j : Fin 3) : evalPt (ptHom W ρ P hP) U h (ratioOn W U i hi j) * P i = P j := by
  have h' : ⊤ ≤ ptHom W ρ P hP ⁻¹ᵁ coordOpen W i := h.trans ((ptHom W ρ P hP).preimage_mono hi)
  have hu : IsUnit (P i) := by
    rw [ptHom_preimage_coordOpen] at h'
    by_contra hu
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {P i})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    exact h' (Set.mem_univ (⟨m, hm.isPrime⟩ : PrimeSpectrum A))
      (hle (Ideal.mem_span_singleton_self _))
  have e₁ := eq_spec_fromSpec (isAffineOpen_coordOpen W i) _ h'
  have e₂ := ptHom_eq_awayChart W i ρ P hP hu
  rw [← SpecMap_awayFnEquiv_awayChart, ← Category.assoc, ← Spec.map_comp] at e₁
  have e₃ := congrArg (fun φ => φ.hom (awayCoord W i j))
    (Spec.map_injective ((cancel_mono _).1 (e₁.symm.trans e₂)))
  have e₄ : evalPt _ _ h' (awayFnEquiv W i (awayCoord W i j)) =
      awayEval W i ρ P hP.equation hu (awayCoord W i j) := e₃
  rw [awayFnEquiv_awayCoord] at e₄
  rw [← awayEval_awayCoord_mul W i ρ P hP.equation hu j, ← e₄, ← evalPt_res _ hi h' h]
  rfl
end
def affineFnEquiv : W.toAffine.CoordinateRing ≃+* Γ(scheme W, coordOpen W 2) :=
  (awayEquivAffine W).symm.trans (awayFnEquiv W 2)
def originFnEquiv : OriginRing W ≃+* Γ(scheme W, coordOpen W 1) :=
  (awayEquivOrigin W).symm.trans (awayFnEquiv W 1)
section BaseChange
variable {R' : Type} [CommRing R'] {W' : WeierstrassCurve R'} (f : R →+* R') (h : W.map f = W')
end BaseChange
example (hP : IsUnimodularSol ((⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℚ).map (RingHom.id ℚ)) ![2, -5, 8])
    (h : ⊤ ≤ ptHom _ _ _ hP ⁻¹ᵁ coordOpen _ 2) :
    evalPt (ptHom _ _ _ hP) _ h (ratio _ 2 0) = 1 / 4 := by
  have := evalPt_ptHom_ratioOn_mul _ _ hP le_rfl h 0
  simp only [Matrix.cons_val_zero, Matrix.cons_val] at this
  linarith
end WeierstrassCurve
end GlobalTheory


