-- Prove2me | Definitions.Def_Esgk_PachDeZeeuwCurveSymmetryReduction
-- name    : Esgk_PachDeZeeuwCurveSymmetryReduction
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:59:30.376012+00:00
-- url     : https://prove2.me/theorems/d3e86ad1-2995-4bbb-b628-033aa1182136
-- title:
--   Reducing curve symmetry bounds to a common center
-- statement:
--   This formulates common-center and cardinality assertions for direct symmetries of an irreducible plane curve that is neither a line nor a circle. It proves reductions from a common fixed point to the direct-symmetry bound and from direct symmetries to all isometries.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_AuxiliaryCircleNoncontainment
import Definitions.Def_Esgk_BridgeIdentity
import Definitions.Def_Esgk_CirclePolynomialRestriction
import Definitions.Def_Esgk_CollisionRootGroupoid
import Definitions.Def_Esgk_DirectIsometryClassification
import Definitions.Def_Esgk_RichnessLevels
import Definitions.Def_Esgk_SelfCurveReflectionInvariance
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Bezout
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveSymmetries
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry

 
def CurveSymmetries.Lemma25DirectStatement : Prop :=
  ∀ (d : ℕ) (C : Set CurveSymmetries.Point2),
    CurveSymmetries.IsIrreducibleCurve d C →
    ¬ CurveSymmetries.IsLineOrCircle C →
    ∀ symmetries : Finset (CurveSymmetries.Point2 ≃ᵢ CurveSymmetries.Point2),
      (∀ g ∈ symmetries, IsDirect g) →
      (∀ g ∈ symmetries, g '' C = C) →
        symmetries.card ≤ 2 * d


def CurveSymmetries.DirectSymmetriesHaveCommonFixedPointStatement : Prop :=
  ∀ (d : ℕ) (C : Set CurveSymmetries.Point2),
    CurveSymmetries.IsIrreducibleCurve d C →
    ¬ CurveSymmetries.IsLineOrCircle C →
    ∀ symmetries : Finset (CurveSymmetries.Point2 ≃ᵢ CurveSymmetries.Point2),
      (∀ g ∈ symmetries, IsDirect g) →
      (∀ g ∈ symmetries, g '' C = C) →
      ∃ center : CurveSymmetries.Point2,
        ∀ g ∈ symmetries, g center = center


theorem CurveSymmetries.sphere_not_subset_of_irreducibleCurve_not_lineOrCircle
    {d : ℕ} {C : Set CurveSymmetries.Point2}
    (hcurve : CurveSymmetries.IsIrreducibleCurve d C)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle C)
    (center : CurveSymmetries.Point2) {r : ℝ} (hr : 0 < r) :
    ¬ Metric.sphere center r ⊆ C := by
  classical
  rcases hcurve with ⟨p, hp0, hpdeg, hpirreducible, hC⟩
  have hCzero : C = PachDeZeeuw.Algebraic.PlaneCurveZeroSet p := by
    have hz : CurveSymmetries.PlaneCurveZeroSet p =
        PachDeZeeuw.Algebraic.PlaneCurveZeroSet p := by
      ext x
      rfl
    change @Eq (Set CurveSymmetries.Point2) C
      (PachDeZeeuw.Algebraic.PlaneCurveZeroSet p)
    exact @Eq.trans (Set CurveSymmetries.Point2) C
      (CurveSymmetries.PlaneCurveZeroSet p)
      (PachDeZeeuw.Algebraic.PlaneCurveZeroSet p) hC hz
  have hCbounded :
      PachDeZeeuw.Algebraic.PlaneCurve.IsBoundedDegreeCurve d C := by
    refine ⟨p, hp0, hpdeg, ?_⟩
    simpa [PachDeZeeuw.Algebraic.PlaneCurveZeroSet] using hCzero
  intro hsubset
  have hnotNoCommon :
      ¬ PachDeZeeuw.Algebraic.NoCommonCurveComponent
        (Metric.sphere center r) C := by
    intro hnoCommon
    rcases PachDeZeeuw.Algebraic.bezout
        (circleEquationPolynomial center r).totalDegree d with
      ⟨_bound, _hboundPos, hbezout⟩
    have hfinite := (hbezout
      (Metric.sphere center r) C
      (sphere_isBoundedDegreeCurve center hr)
      hCbounded hnoCommon).1
    have hsphereFinite : (Metric.sphere center r).Finite := by
      simpa [Set.inter_eq_left.mpr hsubset] using hfinite
    exact sphere_infinite center hr hsphereFinite
  rcases Classical.not_not.mp hnotNoCommon with
    ⟨_e, D, hD, hDinfinite, hDsphere, hDC⟩
  rcases hD with ⟨q, _hq0, _hqdeg, hqirreducible, hDzero⟩
  have hDzero' : D = PachDeZeeuw.Algebraic.PlaneCurveZeroSet q := by
    simpa [PachDeZeeuw.Algebraic.PlaneCurveZeroSet] using hDzero
  have hqinfinite :
      (PachDeZeeuw.Algebraic.PlaneCurveZeroSet q).Infinite := by
    simpa [← hDzero'] using hDinfinite
  have hqsubset :
      PachDeZeeuw.Algebraic.PlaneCurveZeroSet q ⊆
        PachDeZeeuw.Algebraic.PlaneCurveZeroSet p := by
    rw [← hDzero', ← hCzero]
    exact hDC
  have hzeroSets :
      PachDeZeeuw.Algebraic.PlaneCurveZeroSet q =
        PachDeZeeuw.Algebraic.PlaneCurveZeroSet p :=
    zeroSet_eq_of_irreducible_of_infinite_subset hqirreducible
      hpirreducible hqinfinite hqsubset
  have hDeqC : D = C := by
    calc
      D = PachDeZeeuw.Algebraic.PlaneCurveZeroSet q := hDzero'
      _ = PachDeZeeuw.Algebraic.PlaneCurveZeroSet p := hzeroSets
      _ = C := hCzero.symm
  have hCsubsetSphere : C ⊆ Metric.sphere center r := by
    rw [← hDeqC]
    exact hDsphere
  exact hnot <| Or.inr ⟨center, r,
    Set.Subset.antisymm hCsubsetSphere hsubset⟩


theorem CurveSymmetries.exists_mem_ne_of_not_lineOrCircle
    {C : Set CurveSymmetries.Point2}
    (hnot : ¬ CurveSymmetries.IsLineOrCircle C)
    (center : CurveSymmetries.Point2) :
    ∃ p ∈ C, p ≠ center := by
  classical
  by_contra hexists
  push Not at hexists
  by_cases hcenter : center ∈ C
  · apply hnot
    refine Or.inr ⟨center, 0, ?_⟩
    calc
      C = {center} := Set.Subset.antisymm
        (fun p hp ↦ by simpa using hexists p hp)
        (Set.singleton_subset_iff.mpr hcenter)
      _ = Metric.sphere center 0 := Metric.sphere_zero.symm
  · apply hnot
    refine Or.inr ⟨center, -1, ?_⟩
    calc
      C = ∅ := by
        ext p
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hp
        apply hcenter
        rw [← hexists p hp]
        exact hp
      _ = Metric.sphere center (-1) :=
        (Metric.sphere_eq_empty_of_neg (by norm_num)).symm


theorem CurveSymmetries.lemma25Direct_of_commonFixedPoint
    (hcommon : CurveSymmetries.DirectSymmetriesHaveCommonFixedPointStatement) :
    CurveSymmetries.Lemma25DirectStatement := by
  intro d C hcurve hnot symmetries hdirect hpreserves
  classical
  obtain ⟨center, hcenter⟩ :=
    hcommon d C hcurve hnot symmetries hdirect hpreserves
  obtain ⟨p, hpC, hpne⟩ :=
    CurveSymmetries.exists_mem_ne_of_not_lineOrCircle hnot center
  have hr : 0 < dist p center := dist_pos.mpr hpne
  have hnotSphereC : ¬ Metric.sphere center (dist p center) ⊆ C :=
    CurveSymmetries.sphere_not_subset_of_irreducibleCurve_not_lineOrCircle
      hcurve hnot center hr
  rcases hcurve with ⟨f, _hf0, hfdeg, _hfirreducible, hC⟩
  have hCzero : C = PachDeZeeuw.Algebraic.PlaneCurveZeroSet f := by
    simpa [CurveSymmetries.PlaneCurveZeroSet,
      PachDeZeeuw.Algebraic.PlaneCurveZeroSet] using hC
  let orbit : Finset CurveSymmetries.Point2 :=
    symmetries.image fun g ↦ g p
  have horbitCard : orbit.card = symmetries.card := by
    change (symmetries.image fun g ↦ g p).card = symmetries.card
    rw [Finset.card_image_iff]
    intro g hg h hh heval
    exact direct_isometryEquiv_eq_of_send_pair hpne.symm
      (hdirect g hg) (hdirect h hh)
      ((hcenter g hg).trans (hcenter h hh).symm) heval
  have horbitZero : ∀ z ∈ orbit,
      MvPolynomial.eval (fun i ↦ z i) f = 0 := by
    intro z hz
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hz
    have hgpC : g p ∈ C := by
      have hgpImage : g p ∈ g '' C := ⟨p, hpC, rfl⟩
      rwa [hpreserves g hg] at hgpImage
    rw [hCzero] at hgpC
    exact hgpC
  have horbitCircle : ∀ z ∈ orbit,
      z ∈ Metric.sphere center (dist p center) := by
    intro z hz
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hz
    exact Metric.mem_sphere.mpr
      (planeIsometry_dist_fixedPoint (hcenter g hg) p)
  have hnotSphereZero :
      ¬ Metric.sphere center (dist p center) ⊆
        PachDeZeeuw.Algebraic.PlaneCurveZeroSet f := by
    intro hsubset
    apply hnotSphereC
    rwa [hCzero]
  rw [← horbitCard]
  exact finite_circle_zeroSet_card_le_two_mul_of_not_sphere_subset
    f center (dist p center) d orbit hr hfdeg horbitZero horbitCircle
      hnotSphereZero

 
theorem planeIsometryLinearPart_det_ne_zero
    (g : IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2) :
    LinearMap.det
      ((planeIsometryLinearPart g).toLinearEquiv :
        CurveSymmetries.Point2 →ₗ[ℝ] CurveSymmetries.Point2) ≠ 0 := by
  rw [← LinearEquiv.coe_det]
  exact Units.ne_zero _

 
theorem IsDirect.trans_of_not
    {g h : IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2}
    (hg : ¬ IsDirect g) (hh : ¬ IsDirect h) : IsDirect (g.trans h) := by
  have hgneg : LinearMap.det
      ((planeIsometryLinearPart g).toLinearEquiv :
        CurveSymmetries.Point2 →ₗ[ℝ] CurveSymmetries.Point2) < 0 :=
    lt_of_le_of_ne (le_of_not_gt hg) (planeIsometryLinearPart_det_ne_zero g)
  have hhneg : LinearMap.det
      ((planeIsometryLinearPart h).toLinearEquiv :
        CurveSymmetries.Point2 →ₗ[ℝ] CurveSymmetries.Point2) < 0 :=
    lt_of_le_of_ne (le_of_not_gt hh) (planeIsometryLinearPart_det_ne_zero h)
  show 0 < LinearMap.det
    ((planeIsometryLinearPart (g.trans h)).toLinearEquiv :
      CurveSymmetries.Point2 →ₗ[ℝ] CurveSymmetries.Point2)
  rw [planeIsometryLinearPart_trans]
  have hcomp : (((planeIsometryLinearPart g).trans
        (planeIsometryLinearPart h)).toLinearEquiv :
          CurveSymmetries.Point2 →ₗ[ℝ] CurveSymmetries.Point2) =
      ((planeIsometryLinearPart h).toLinearEquiv :
          CurveSymmetries.Point2 →ₗ[ℝ] CurveSymmetries.Point2) ∘ₗ
        ((planeIsometryLinearPart g).toLinearEquiv :
          CurveSymmetries.Point2 →ₗ[ℝ] CurveSymmetries.Point2) := rfl
  rw [hcomp, LinearMap.det_comp]
  exact mul_pos_of_neg_of_neg hhneg hgneg

 
theorem isometryEquiv_trans_left_injective
    (g : IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2) :
    Function.Injective fun h :
      IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2 ↦ g.trans h := by
  intro h k hhk
  apply IsometryEquiv.ext
  intro x
  have happ := congrArg (fun e :
    IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2 ↦
      e (g.symm x)) hhk
  simpa using happ

 
theorem isometryEquiv_trans_image_eq
    {C : Set CurveSymmetries.Point2}
    {g h : IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2}
    (hg : g '' C = C) (hh : h '' C = C) :
    (g.trans h) '' C = C := by
  rw [show (g.trans h) '' C = h '' (g '' C) by
    exact (Set.image_image h g C).symm]
  rw [hg, hh]

 
theorem CurveSymmetries.lemma25_of_direct
    (hdirect : CurveSymmetries.Lemma25DirectStatement) :
    CurveSymmetries.Lemma25Statement := by
  intro d C hcurve hnot symmetries hpreserves
  classical
  let direct := symmetries.filter IsDirect
  let indirect := symmetries.filter fun g ↦ ¬ IsDirect g
  have hsplit : direct.card + indirect.card = symmetries.card := by
    simpa [direct, indirect] using
      Finset.card_filter_add_card_filter_not (s := symmetries) IsDirect
  have hdirectCard : direct.card ≤ 2 * d := by
    apply hdirect d C hcurve hnot direct
    · intro g hg
      exact (Finset.mem_filter.mp hg).2
    · intro g hg
      exact hpreserves g (Finset.mem_filter.mp hg).1
  by_cases hindirect : indirect.Nonempty
  · obtain ⟨r, hr⟩ := hindirect
    let twist :
        IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2 ↪
          IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2 :=
      ⟨fun g ↦ r.trans g, isometryEquiv_trans_left_injective r⟩
    let twisted : Finset
        (IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2) :=
      indirect.map twist
    have hrNot : ¬ IsDirect r := (Finset.mem_filter.mp hr).2
    have hrPreserves : r '' C = C :=
      hpreserves r (Finset.mem_filter.mp hr).1
    have htwistedDirect : ∀ g ∈ twisted, IsDirect g := by
      intro g hg
      obtain ⟨h, hh, rfl⟩ := Finset.mem_map.mp hg
      exact IsDirect.trans_of_not hrNot (Finset.mem_filter.mp hh).2
    have htwistedPreserves : ∀ g ∈ twisted, g '' C = C := by
      intro g hg
      obtain ⟨h, hh, rfl⟩ := Finset.mem_map.mp hg
      exact isometryEquiv_trans_image_eq hrPreserves
        (hpreserves h (Finset.mem_filter.mp hh).1)
    have hindirectCard : indirect.card ≤ 2 * d := by
      rw [← Finset.card_map]
      exact hdirect d C hcurve hnot twisted htwistedDirect htwistedPreserves
    omega
  · have hindirectCard : indirect.card = 0 :=
      Finset.not_nonempty_iff_eq_empty.mp hindirect ▸ Finset.card_empty
    omega


theorem CurveSymmetries.lemma25_of_commonFixedPoint
    (hcommon : CurveSymmetries.DirectSymmetriesHaveCommonFixedPointStatement) :
    CurveSymmetries.Lemma25Statement :=
  CurveSymmetries.lemma25_of_direct
    (CurveSymmetries.lemma25Direct_of_commonFixedPoint hcommon)

end Esgk


