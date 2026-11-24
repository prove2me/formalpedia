-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PDehomogOrd
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_PDehomogOrd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:56.869957+00:00
-- url     : https://prove2.me/theorems/d6cfd72e-5e51-4767-b989-307ec7bb7efc
-- title:
--   PDehomog Ord
-- statement:
--   Definitions and structural lemmas for PDehomog Ord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PDehomogOrd.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLocDomain_linForm_isHomogeneous_618f3987ba84

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace DehomogOrd
variable {F : Type} [Field F] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
theorem aeval_smul_hom {B : Type*} [CommSemiring B] [Algebra F B] (π : MvPolynomial (Fin n) F →ₐ[F] B) (c : B)
    {g : MvPolynomial (Fin n) F} {d : ℕ} (hg : g.IsHomogeneous d) :
    aeval (fun m => c * π (X m)) g = c ^ d * π g := by
  have key : aeval (fun m => c * π (X m)) g = c ^ d * aeval (fun m => π (X m)) g := by
    conv_lhs => rw [g.as_sum]
    conv_rhs => rw [g.as_sum]
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hd := hg (mem_support_iff.mp hs)
    simp only [aeval_monomial, mul_pow]
    rw [Finsupp.prod_mul, Finsupp.prod_pow, Finsupp.prod_pow, Finset.prod_pow_eq_pow_sum, ← hd,
      Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp only [smul_eq_mul, Pi.one_apply, mul_one]
    ring
  rw [key]
  congr 1
  rw [← comp_aeval_apply]
  simp
theorem map_eq_zero_of_components {B G : Type*} [CommRing B] [FunLike G (MvPolynomial (Fin n) F) B]
    [RingHomClass G (MvPolynomial (Fin n) F) B] (f : G)
    {K : Ideal (MvPolynomial (Fin n) F)}
    (hf : ∀ g ∈ K, ∀ k, f (homogeneousComponent k g) = 0) {g : MvPolynomial (Fin n) F} (hg : g ∈ K) :
    f g = 0 := by
  rw [← sum_homogeneousComponent g, map_sum]
  exact Finset.sum_eq_zero fun k _ => hf g hg k
abbrev chartIdealOf : Ideal (MvPolynomial (Fin n) F) := I ⊔ Ideal.span {linForm t - 1}
abbrev ChartRing := MvPolynomial (Fin n) F ⧸ chartIdealOf I t
abbrev linClass : MvPolynomial (Fin n) F ⧸ I := Ideal.Quotient.mk I (linForm t)
theorem mk_linForm_chart : Ideal.Quotient.mk (chartIdealOf I t) (linForm t) = 1 := by
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk (chartIdealOf I t)), ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
def toPoly : MvPolynomial (Fin n) F →ₐ[F] MvPolynomial Unit (ChartRing I t) :=
  aeval fun m => X () * (IsScalarTower.toAlgHom F (ChartRing I t) (MvPolynomial Unit (ChartRing I t))).comp
    (Ideal.Quotient.mkₐ F (chartIdealOf I t)) (X m)
theorem toPoly_hom {g : MvPolynomial (Fin n) F} {d : ℕ} (hg : g.IsHomogeneous d) :
    toPoly I t g = X () ^ d * C (Ideal.Quotient.mk (chartIdealOf I t) g) := by
  have h := aeval_smul_hom ((IsScalarTower.toAlgHom F (ChartRing I t) (MvPolynomial Unit (ChartRing I t))).comp
    (Ideal.Quotient.mkₐ F (chartIdealOf I t))) (X ()) hg
  refine h.trans ?_
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', Ideal.Quotient.mkₐ_eq_mk, MvPolynomial.algebraMap_eq]
theorem toPoly_eq_zero (hI : IsHomogIdeal I) {a : MvPolynomial (Fin n) F} (ha : a ∈ I) : toPoly I t a = 0 :=
  map_eq_zero_of_components (toPoly I t) (fun g hg k => by
    rw [toPoly_hom I t (homogeneousComponent_isHomogeneous k g),
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (hI g hg k)), map_zero, mul_zero]) ha
def toPolyR (hI : IsHomogIdeal I) : MvPolynomial (Fin n) F ⧸ I →+* MvPolynomial Unit (ChartRing I t) :=
  Ideal.Quotient.lift I (toPoly I t).toRingHom fun _ ha => toPoly_eq_zero I t hI ha
theorem toPolyR_mk (hI : IsHomogIdeal I) (a : MvPolynomial (Fin n) F) :
    toPolyR I t hI (Ideal.Quotient.mk I a) = toPoly I t a := rfl
theorem toPolyR_linClass (hI : IsHomogIdeal I) : toPolyR I t hI (linClass I t) = X () := by
  rw [toPolyR_mk, toPoly_hom I t (ChartLocDomain.linForm_isHomogeneous t), mk_linForm_chart, map_one,
    pow_one, mul_one]
def fromChart : MvPolynomial (Fin n) F →ₐ[F] Localization.Away (linClass I t) :=
  aeval fun m => IsLocalization.Away.invSelf (linClass I t) *
    (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ I) (Localization.Away (linClass I t))).comp
      (Ideal.Quotient.mkₐ F I) (X m)
theorem fromChart_hom {g : MvPolynomial (Fin n) F} {d : ℕ} (hg : g.IsHomogeneous d) :
    fromChart I t g = IsLocalization.Away.invSelf (linClass I t) ^ d *
      algebraMap _ (Localization.Away (linClass I t)) (Ideal.Quotient.mk I g) := by
  rw [fromChart, aeval_smul_hom _ _ hg]
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', Ideal.Quotient.mkₐ_eq_mk]
theorem fromChart_eq_zero (hI : IsHomogIdeal I) {a : MvPolynomial (Fin n) F} (ha : a ∈ chartIdealOf I t) :
    fromChart I t a = 0 := by
  have hle : chartIdealOf I t ≤ RingHom.ker (fromChart I t) := by
    refine sup_le (fun g hg => ?_) ?_
    · rw [RingHom.mem_ker]
      refine map_eq_zero_of_components (fromChart I t) (fun g hg k => ?_) hg
      rw [fromChart_hom I t (homogeneousComponent_isHomogeneous k g),
        Ideal.Quotient.eq_zero_iff_mem.mpr (hI g hg k), map_zero, mul_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      change fromChart I t (linForm t - 1) = 0
      rw [map_sub, map_one, fromChart_hom I t (ChartLocDomain.linForm_isHomogeneous t), pow_one, mul_comm,
        IsLocalization.Away.mul_invSelf, sub_self]
  exact hle ha
def fromChartQ (hI : IsHomogIdeal I) : ChartRing I t →+* Localization.Away (linClass I t) :=
  Ideal.Quotient.lift _ (fromChart I t).toRingHom fun _ ha => fromChart_eq_zero I t hI ha
def fromPoly (hI : IsHomogIdeal I) : MvPolynomial Unit (ChartRing I t) →+* Localization.Away (linClass I t) :=
  eval₂Hom (fromChartQ I t hI) fun _ => algebraMap _ _ (linClass I t)
theorem fromPoly_C_mk (hI : IsHomogIdeal I) (a : MvPolynomial (Fin n) F) :
    fromPoly I t hI (C (Ideal.Quotient.mk _ a)) = fromChart I t a := by
  simp only [fromPoly, fromChartQ, coe_eval₂Hom, eval₂_C, Ideal.Quotient.lift_mk]
  rfl
theorem fromPoly_X (hI : IsHomogIdeal I) :
    fromPoly I t hI (X ()) = algebraMap _ _ (linClass I t) := by
  simp [fromPoly]
theorem fromPoly_toPolyR (hI : IsHomogIdeal I) (r : MvPolynomial (Fin n) F ⧸ I) :
    fromPoly I t hI (toPolyR I t hI r) = algebraMap _ _ r := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [toPolyR_mk]
  change ((fromPoly I t hI).comp (toPoly I t).toRingHom) a =
    ((algebraMap _ (Localization.Away (linClass I t))).comp (Ideal.Quotient.mk I)) a
  congr 1
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun m => ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply]
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
      MvPolynomial.algebraMap_apply,
      show algebraMap F (ChartRing I t) c = Ideal.Quotient.mk _ (algebraMap F _ c) from rfl, fromPoly_C_mk,
      AlgHom.commutes]
    rfl
  · simp only [RingHom.coe_comp, Function.comp_apply]
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, toPoly, aeval_X, map_mul, fromPoly_X]
    change _ * fromPoly I t hI (C (Ideal.Quotient.mk _ (X m))) = _
    rw [fromPoly_C_mk, fromChart, aeval_X, ← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]
    rfl
def toLoc (hI : IsHomogIdeal I) :
    Localization.Away (linClass I t) →+* Localization.Away (X () : MvPolynomial Unit (ChartRing I t)) :=
  IsLocalization.Away.lift (linClass I t)
    (g := (algebraMap _ (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))).comp (toPolyR I t hI))
    (by rw [RingHom.comp_apply, toPolyR_linClass]; exact IsLocalization.Away.algebraMap_isUnit _)
theorem toLoc_algebraMap (hI : IsHomogIdeal I) (r : MvPolynomial (Fin n) F ⧸ I) :
    toLoc I t hI (algebraMap _ _ r) = algebraMap _ _ (toPolyR I t hI r) :=
  IsLocalization.Away.lift_eq _ _ r
def fromLoc (hI : IsHomogIdeal I) :
    Localization.Away (X () : MvPolynomial Unit (ChartRing I t)) →+* Localization.Away (linClass I t) :=
  IsLocalization.Away.lift (X () : MvPolynomial Unit (ChartRing I t)) (g := fromPoly I t hI)
    (by rw [fromPoly_X]; exact IsLocalization.Away.algebraMap_isUnit _)
theorem fromLoc_algebraMap (hI : IsHomogIdeal I) (b : MvPolynomial Unit (ChartRing I t)) :
    fromLoc I t hI (algebraMap _ _ b) = fromPoly I t hI b :=
  IsLocalization.Away.lift_eq _ _ b
theorem fromLoc_toLoc (hI : IsHomogIdeal I) (x : Localization.Away (linClass I t)) :
    fromLoc I t hI (toLoc I t hI x) = x := by
  have : (fromLoc I t hI).comp (toLoc I t hI) = RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers (linClass I t)) (RingHom.ext fun r => by
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      rw [toLoc_algebraMap, fromLoc_algebraMap, fromPoly_toPolyR])
  exact congrArg (· x) this
theorem toLoc_fromPoly (hI : IsHomogIdeal I) (b : MvPolynomial Unit (ChartRing I t)) :
    toLoc I t hI (fromPoly I t hI b) = algebraMap _ _ b := by
  have hv : toLoc I t hI (IsLocalization.Away.invSelf (linClass I t)) *
      algebraMap (MvPolynomial Unit (ChartRing I t)) (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))
        (X ()) = 1 := by
    have h2 : algebraMap (MvPolynomial Unit (ChartRing I t))
        (Localization.Away (X () : MvPolynomial Unit (ChartRing I t))) (X ()) =
        toLoc I t hI (algebraMap _ _ (linClass I t)) := by
      rw [toLoc_algebraMap, toPolyR_linClass]
    rw [h2, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]
  change ((toLoc I t hI).comp (fromPoly I t hI)) b = (algebraMap _ _) b
  congr 1
  refine MvPolynomial.ringHom_ext (fun q => ?_) (fun _ => ?_)
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [fromPoly_C_mk]
    change ((toLoc I t hI).comp (fromChart I t).toRingHom) a =
      ((algebraMap _ (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))).comp
        (C.comp (Ideal.Quotient.mk _))) a
    congr 1
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun m => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes,
        show algebraMap F (Localization.Away (linClass I t)) c =
          algebraMap _ _ (Ideal.Quotient.mk I (algebraMap F _ c)) from rfl,
        toLoc_algebraMap, toPolyR_mk, AlgHom.commutes, MvPolynomial.algebraMap_apply]
      rfl
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [fromChart, aeval_X, map_mul]
      change _ * toLoc I t hI (algebraMap _ _ (Ideal.Quotient.mk I (X m))) = _
      rw [toLoc_algebraMap, toPolyR_mk, toPoly, aeval_X, map_mul, ← mul_assoc, hv, one_mul]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', Ideal.Quotient.mkₐ_eq_mk,
        MvPolynomial.algebraMap_eq]
  · simp only [RingHom.coe_comp, Function.comp_apply]
    rw [fromPoly_X, toLoc_algebraMap, toPolyR_linClass]
theorem toLoc_fromLoc (hI : IsHomogIdeal I) (y : Localization.Away (X () : MvPolynomial Unit (ChartRing I t))) :
    toLoc I t hI (fromLoc I t hI y) = y := by
  have : (toLoc I t hI).comp (fromLoc I t hI) = RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers (X () : MvPolynomial Unit (ChartRing I t))) (RingHom.ext fun b => by
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      rw [fromLoc_algebraMap, toLoc_fromPoly])
  exact congrArg (· y) this
def locEquiv (hI : IsHomogIdeal I) :
    Localization.Away (linClass I t) ≃+* Localization.Away (X () : MvPolynomial Unit (ChartRing I t)) :=
  RingEquiv.ofRingHom (toLoc I t hI) (fromLoc I t hI) (RingHom.ext (toLoc_fromLoc I t hI))
    (RingHom.ext (fromLoc_toLoc I t hI))
end DehomogOrd
end
end GroundTheory.Heights₂.Heights


