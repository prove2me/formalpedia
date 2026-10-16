-- Prove2me | Definitions.Def_Esgk_SelfCurveCompleteSymmetryFamily
-- name    : Esgk_SelfCurveCompleteSymmetryFamily
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T05:04:58.966463+00:00
-- url     : https://prove2.me/theorems/fa3759b8-ac63-4526-a793-38b9ed213c1d
-- title:
--   The finite family of curve-preserving isometries
-- statement:
--   This defines isometries preserving a planar set and constructs their finite family for an irreducible curve of degree at most $d$ that is neither a line nor a circle, using the $4d$ symmetry bound. It specializes the construction to prepared incidence data whose two supporting curves coincide.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PachDeZeeuwCurveSymmetryTranslation
import Definitions.Def_Esgk_PachDeZeeuwQuadraticDegree
import Definitions.Def_Esgk_SelfCurveExceptionalIsometryFamilies
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Basic
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveSymmetries
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open PachDeZeeuw

 
abbrev CarrierSymmetry (C : Set Point2) :=
  {g : Point2 ≃ᵢ Point2 // g '' C = C}


@[implicit_reducible]
noncomputable def carrierSymmetryFintype_of_lemma25
    {d : ℕ} {C : Set Point2}
    (hcurve : CurveSymmetries.IsIrreducibleCurve d C)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle C) :
    Fintype (CarrierSymmetry C) := by
  classical
  apply fintypeOfFinsetCardLe (4 * d)
  intro family
  let images : Finset (Point2 ≃ᵢ Point2) :=
    family.map ⟨Subtype.val, Subtype.val_injective⟩
  have hpreserves : ∀ g ∈ images, g '' C = C := by
    intro g hg
    obtain ⟨g', _hg', rfl⟩ := Finset.mem_map.mp hg
    exact g'.property
  simpa [images] using
    CurveSymmetries.lemma25 d C hcurve hnot images hpreserves

 
noncomputable def carrierSymmetriesFinset
    {d : ℕ} {C : Set Point2}
    (hcurve : CurveSymmetries.IsIrreducibleCurve d C)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle C) :
    Finset (Point2 ≃ᵢ Point2) := by
  classical
  letI : Fintype (CarrierSymmetry C) :=
    carrierSymmetryFintype_of_lemma25 hcurve hnot
  exact (Finset.univ : Finset (CarrierSymmetry C)).image Subtype.val


theorem preparedSecondCurve_isIrreducibleCurve
    {d : ℕ} (X : PreparedBipartiteInput d) :
    CurveSymmetries.IsIrreducibleCurve d X.C₂ := by
  simpa [CurveSymmetries.IsIrreducibleCurve,
    PlaneCurve.IsIrreducibleCurve, CurveSymmetries.PlaneCurveZeroSet] using X.hC₂


theorem selfCurvePreparedInput_not_isLineOrCircle
    {d : ℕ} {X : PreparedBipartiteInput d}
    (hself : SelfCurvePreparedInput X) :
    ¬ CurveSymmetries.IsLineOrCircle X.C₂ := by
  intro hcontrolled
  apply X.notExceptional
  rcases hcontrolled with hline | hcircle
  · rcases hline with ⟨a, b, c, hab, hC⟩
    apply exceptionalCurvePair_of_parallelLines
    refine ⟨a, b, c, c, hab, ?_, ?_⟩
    · rw [hself]
      exact hC
    · exact hC
  · rcases hcircle with ⟨center, r, hC⟩
    apply exceptionalCurvePair_of_concentricCircles
    refine ⟨center, r, r, ?_, hC⟩
    rw [hself]
    exact hC

 
noncomputable def selfCurveCarrierSymmetries
    {d : ℕ} {X : PreparedBipartiteInput d}
    (hself : SelfCurvePreparedInput X) : Finset (Point2 ≃ᵢ Point2) :=
  carrierSymmetriesFinset (preparedSecondCurve_isIrreducibleCurve X)
    (selfCurvePreparedInput_not_isLineOrCircle hself)


end Esgk


