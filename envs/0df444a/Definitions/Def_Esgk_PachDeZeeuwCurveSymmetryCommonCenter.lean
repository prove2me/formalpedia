-- Prove2me | Definitions.Def_Esgk_PachDeZeeuwCurveSymmetryCommonCenter
-- name    : Esgk_PachDeZeeuwCurveSymmetryCommonCenter
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T05:00:58.724935+00:00
-- url     : https://prove2.me/theorems/91e9c11c-e920-486d-a0ba-b20b0a264700
-- title:
--   Common centers of direct curve symmetries
-- statement:
--   This formulates the absence of nontrivial translation symmetries and proves its consequences for direct isometries preserving a planar set: they commute, and every finite family has a common fixed point. It also relates these conclusions to symmetry bounds for irreducible curves that are neither lines nor circles.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_CollisionRootGroupoid
import Definitions.Def_Esgk_DirectIsometryClassification
import Definitions.Def_Esgk_PachDeZeeuwCurveSymmetryReduction
import Definitions.Def_Esgk_RichnessLevels
import Definitions.Def_LeanFormalizations_Geometry_Euclidean_IsometryClassification
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveSymmetries
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

local instance : Fact (Module.finrank ℝ CurveSymmetries.Point2 = 2) := ⟨by simp⟩

open EuclideanGeometry

noncomputable section


local notation "o" =>
  (positiveOrientation : Orientation ℝ CurveSymmetries.Point2 (Fin 2))


def CurveSymmetries.NoNontrivialTranslationSymmetryStatement : Prop :=
  ∀ (d : ℕ) (C : Set CurveSymmetries.Point2),
    CurveSymmetries.IsIrreducibleCurve d C →
    ¬ CurveSymmetries.IsLineOrCircle C →
    ∀ g : IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2,
      g '' C = C → planeIsometryLinearPart g = 1 → g = 1

theorem bundle_Esgk_PachDeZeeuwCurveSymmetryCommonCenter_image_symm_eq_of_image_eq
    {C : Set CurveSymmetries.Point2}
    {g : IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2}
    (hg : g '' C = C) :
    g.symm '' C = C := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ g '' C := by
      rw [hg]
      exact hy
    obtain ⟨z, hz, hzy⟩ := hy'
    rw [← hzy]
    simp
    exact hz
  · intro x hx
    have hgx : g x ∈ C := by
      rw [← hg]
      exact ⟨x, hx, rfl⟩
    exact ⟨g x, hgx, by simp⟩

theorem bundle_Esgk_PachDeZeeuwCurveSymmetryCommonCenter_planeIsometryLinearPart_one :
    planeIsometryLinearPart
      (1 : IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2) = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  have h := planeIsometry_apply_eq_linearPart_add
    (1 : IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2) x
  simpa using h.symm

theorem bundle_Esgk_PachDeZeeuwCurveSymmetryCommonCenter_planeIsometryLinearPart_symm
    (g : IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2) :
    planeIsometryLinearPart g.symm = (planeIsometryLinearPart g).symm := by
  have h : g.trans g.symm = 1 := by
    apply IsometryEquiv.ext
    intro x
    simp [IsometryEquiv.trans_apply]
  have h' := congrArg planeIsometryLinearPart h
  rw [planeIsometryLinearPart_trans, bundle_Esgk_PachDeZeeuwCurveSymmetryCommonCenter_planeIsometryLinearPart_one] at h'
  apply LinearIsometryEquiv.ext
  intro x
  have hx := congrArg
    (fun f : CurveSymmetries.Point2 ≃ₗᵢ[ℝ] CurveSymmetries.Point2 ↦
      f ((planeIsometryLinearPart g).symm x)) h'
  simpa [LinearIsometryEquiv.trans_apply] using hx

theorem bundle_Esgk_PachDeZeeuwCurveSymmetryCommonCenter_planeIsometryLinearPart_commutator
    (g h : IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2)
    (hg : IsDirect g) (hh : IsDirect h) :
    planeIsometryLinearPart
        (g.trans (h.trans (g.symm.trans h.symm))) = 1 := by
  obtain ⟨θg, hθg⟩ := direct_planeIsometryLinearPart_exists_rotation hg
  obtain ⟨θh, hθh⟩ := direct_planeIsometryLinearPart_exists_rotation hh
  rw [planeIsometryLinearPart_trans, planeIsometryLinearPart_trans,
    planeIsometryLinearPart_trans]
  simp only [hθg, hθh, bundle_Esgk_PachDeZeeuwCurveSymmetryCommonCenter_planeIsometryLinearPart_symm g,
    bundle_Esgk_PachDeZeeuwCurveSymmetryCommonCenter_planeIsometryLinearPart_symm h]
  have assoc (a b c : CurveSymmetries.Point2 ≃ₗᵢ[ℝ] CurveSymmetries.Point2) :
      a.trans (b.trans c) = (a.trans b).trans c := by
    ext x
    rfl
  rw [assoc, assoc, o.rotation_trans θg θh]
  rw [o.rotation_symm θg, o.rotation_symm θh]
  rw [o.rotation_trans (θh + θg) (-θg)]
  rw [o.rotation_trans (-θg + (θh + θg)) (-θh)]
  simp [add_comm]
  apply LinearIsometryEquiv.ext
  intro x
  rfl


theorem direct_carrier_symmetry_commutes_of_no_translations
    {C : Set CurveSymmetries.Point2}
    (hnotrans : ∀ {u : IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2},
      u '' C = C → planeIsometryLinearPart u = 1 → u = 1)
    {g h : IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2}
    (hg : IsDirect g) (hh : IsDirect h)
    (hCg : g '' C = C) (hCh : h '' C = C) :
    g.trans h = h.trans g := by
  let q := g.trans (h.trans (g.symm.trans h.symm))
  have hqC : q '' C = C := by
    dsimp [q]
    exact isometryEquiv_trans_image_eq hCg
      (isometryEquiv_trans_image_eq hCh
        (isometryEquiv_trans_image_eq
          (bundle_Esgk_PachDeZeeuwCurveSymmetryCommonCenter_image_symm_eq_of_image_eq hCg)
          (bundle_Esgk_PachDeZeeuwCurveSymmetryCommonCenter_image_symm_eq_of_image_eq hCh)))
  have hqLP : planeIsometryLinearPart q = 1 := by
    dsimp [q]
    exact bundle_Esgk_PachDeZeeuwCurveSymmetryCommonCenter_planeIsometryLinearPart_commutator g h hg hh
  have hq : q = 1 := hnotrans hqC hqLP
  apply IsometryEquiv.ext
  intro x
  have hx := congrArg (fun z : CurveSymmetries.Point2 ↦ g (h z))
    (congrArg
      (fun k : IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2 ↦ k x)
      hq)
  simpa [q, IsometryEquiv.trans_apply] using hx


theorem exists_common_fixedPoint_of_finset_of_no_translations
    {C : Set CurveSymmetries.Point2}
    (G : Finset
      (IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2))
    (hnotrans : ∀ {u : IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2},
      u '' C = C → planeIsometryLinearPart u = 1 → u = 1)
    (hGdirect : ∀ g ∈ G, IsDirect g)
    (hGcarrier : ∀ g ∈ G, g '' C = C) :
    ∃ center : CurveSymmetries.Point2, ∀ g ∈ G, g center = center := by
  classical
  by_cases hall : ∀ g ∈ G, g = 1
  · refine ⟨0, ?_⟩
    intro g hg
    rw [hall g hg]
    simp
  · push Not at hall
    obtain ⟨g₀, hg₀, hne₀⟩ := hall
    obtain ⟨center, hcenter, hunique⟩ :=
      direct_isometry_existsUnique_fixedPoint_of_linearPart_ne_one
        (hGdirect g₀ hg₀)
        (by
          intro hlinear
          apply hne₀
          exact hnotrans (hGcarrier g₀ hg₀) hlinear)
    refine ⟨center, ?_⟩
    intro h hh
    have hcomm := direct_carrier_symmetry_commutes_of_no_translations
      hnotrans (hGdirect h hh) (hGdirect g₀ hg₀)
      (hGcarrier h hh) (hGcarrier g₀ hg₀)
    apply hunique (h center)
    have hx := congrArg
      (fun k : IsometryEquiv CurveSymmetries.Point2 CurveSymmetries.Point2 ↦
        k center) hcomm
    simpa [IsometryEquiv.trans_apply, hcenter] using hx


theorem CurveSymmetries.directSymmetriesHaveCommonFixedPoint_of_noTranslations
    (hnotrans : CurveSymmetries.NoNontrivialTranslationSymmetryStatement) :
    CurveSymmetries.DirectSymmetriesHaveCommonFixedPointStatement := by
  intro d C hcurve hnot G hGdirect hGcarrier
  exact exists_common_fixedPoint_of_finset_of_no_translations G
    (fun {u} huC huLP ↦ hnotrans d C hcurve hnot u huC huLP)
    hGdirect hGcarrier


theorem CurveSymmetries.lemma25_of_noNontrivialTranslationSymmetry
    (hnotrans : CurveSymmetries.NoNontrivialTranslationSymmetryStatement) :
    CurveSymmetries.Lemma25Statement :=
  CurveSymmetries.lemma25_of_commonFixedPoint
    (CurveSymmetries.directSymmetriesHaveCommonFixedPoint_of_noTranslations
      hnotrans)

end

end Esgk


