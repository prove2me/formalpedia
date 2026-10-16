-- Prove2me | Definitions.Def_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves
-- name    : LeanFormalizations_PachDeZeeuw_AuxiliaryCurves
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:47:16.79813+00:00
-- url     : https://prove2.me/theorems/ffcfeaf8-0b30-4ec8-b9d8-c82b8a716d3c
-- title:
--   Auxiliary curves for equal-distance incidences
-- statement:
--   This encodes ordered pairs of sample points as points in four-dimensional space and defines auxiliary curves by two curve equations and an equality of squared distances. It also defines their incidence set and the proposition comparing its size with the number of equal-distance quadruples.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Basic
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


set_option linter.style.longLine false

namespace PachDeZeeuw

open EuclideanGeometry

 
noncomputable def bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_curveWitnessPoly₂ {d : ℕ}
    (X : PreparedBipartiteInput d) : MvPolynomial (Fin 2) ℝ :=
  Classical.choose X.hC₂


noncomputable def bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxPointOfPair (pq : Point2 × Point2) : Point4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm fun
    | 0 => pq.1 0
    | 1 => pq.1 1
    | 2 => pq.2 0
    | _ => pq.2 1


noncomputable def bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxFirstPair (z : Point4) : Point2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm fun
    | 0 => z 0
    | _ => z 1

noncomputable def bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxSecondPair (z : Point4) : Point2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm fun
    | 0 => z 2
    | _ => z 3


noncomputable def auxPointSet {d : ℕ} (X : PreparedBipartiteInput d) :
    Finset Point4 :=
  (X.P₂.product X.P₂).image bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxPointOfPair


noncomputable def auxCurve {d : ℕ} (X : PreparedBipartiteInput d)
    (i j : X.P₁) : Set Point4 :=
  {z : Point4 |
    MvPolynomial.eval (fun k => bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxFirstPair z k) (bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_curveWitnessPoly₂ X) = 0 ∧
    MvPolynomial.eval (fun k => bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxSecondPair z k) (bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_curveWitnessPoly₂ X) = 0 ∧
    dist (i : Point2) (bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxFirstPair z) ^ 2 = dist (j : Point2) (bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxSecondPair z) ^ 2}

 
noncomputable def auxIncidences {d : ℕ} (X : PreparedBipartiteInput d) :
    Finset (Point4 × (X.P₁ × X.P₁)) :=
  by
    classical
    exact
      ((auxPointSet X).product (Finset.univ : Finset (X.P₁ × X.P₁))).filter
        (fun p => p.1 ∈ auxCurve X p.2.1 p.2.2)


def AuxIncidenceBridgeStatement : Prop :=
  ∀ d : ℕ, ∀ X : PreparedBipartiteInput d,
    (equalDistanceQuadruples X).card ≤ (auxIncidences X).card


end PachDeZeeuw


