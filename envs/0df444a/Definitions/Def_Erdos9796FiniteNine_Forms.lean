-- Prove2me | Definitions.Def_Erdos9796FiniteNine_Forms
-- name    : Erdos9796FiniteNine_Forms
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-09T06:31:35.018742+00:00
-- url     : https://prove2.me/theorems/e3a66ec7-cdfc-43f6-a6ab-a05bdf87951b
-- title:
--   Finite-nine escaped-class forms
-- statement:
--   Distance classes with at least four points, their nine possible locations relative to the boundary triangle's cap regions, and predicates excluding those patterns.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/a46894f6078319d3001d06310531df50af0f6bbd/lean/Erdos9796Proof/P97/N9Endpoint/N4e.lean

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796FiniteNine_Shell

/-! Definition-only N4 witness forms and public exclusion predicates. -/

set_option backward.isDefEq.respectTransparency false
open scoped EuclideanGeometry
open Finset

namespace Batch3N9
namespace Problem97
namespace FiniteEndpointShell

@[reducible] noncomputable def witnessClassAt_v1 {A : Finset ℝ²}
    (S : FiniteEndpointShell A) (r : ℝ) : Finset ℝ² :=
  A.filter (fun x => dist S.triangle.v1 x = r)
@[reducible] noncomputable def witnessClassAt_v2 {A : Finset ℝ²}
    (S : FiniteEndpointShell A) (r : ℝ) : Finset ℝ² :=
  A.filter (fun x => dist S.triangle.v2 x = r)
@[reducible] noncomputable def witnessClassAt_v3 {A : Finset ℝ²}
    (S : FiniteEndpointShell A) (r : ℝ) : Finset ℝ² :=
  A.filter (fun x => dist S.triangle.v3 x = r)

def IsFormA_v1 {A : Finset ℝ²} (S : FiniteEndpointShell A) (r : ℝ) : Prop :=
  ∃ x y : ℝ²,
    x ∈ S.I2 ∧
    y ∈ S.I3 ∧
    (S.witnessClassAt_v1 r ∩ S.CP.C2 = ({x} : Finset ℝ²)) ∧
    (S.witnessClassAt_v1 r ∩ S.CP.C3 = ({y} : Finset ℝ²))
def IsFormB_v1 {A : Finset ℝ²} (S : FiniteEndpointShell A) (r : ℝ) : Prop :=
  ∃ x : ℝ²,
    x ∈ S.I2 ∧
    (S.witnessClassAt_v1 r ∩ S.CP.C2 = ({x} : Finset ℝ²)) ∧
    (S.witnessClassAt_v1 r ∩ S.CP.C3 = ({S.triangle.v2} : Finset ℝ²))
def IsFormC_v1 {A : Finset ℝ²} (S : FiniteEndpointShell A) (r : ℝ) : Prop :=
  ∃ y : ℝ²,
    y ∈ S.I3 ∧
    (S.witnessClassAt_v1 r ∩ S.CP.C2 = ({S.triangle.v3} : Finset ℝ²)) ∧
    (S.witnessClassAt_v1 r ∩ S.CP.C3 = ({y} : Finset ℝ²))
def IsFormA_v2 {A : Finset ℝ²} (S : FiniteEndpointShell A) (r : ℝ) : Prop :=
  ∃ x y : ℝ²,
    x ∈ S.I3 ∧
    y ∈ S.I1 ∧
    (S.witnessClassAt_v2 r ∩ S.CP.C3 = ({x} : Finset ℝ²)) ∧
    (S.witnessClassAt_v2 r ∩ S.CP.C1 = ({y} : Finset ℝ²))
def IsFormB_v2 {A : Finset ℝ²} (S : FiniteEndpointShell A) (r : ℝ) : Prop :=
  ∃ x : ℝ²,
    x ∈ S.I3 ∧
    (S.witnessClassAt_v2 r ∩ S.CP.C3 = ({x} : Finset ℝ²)) ∧
    (S.witnessClassAt_v2 r ∩ S.CP.C1 = ({S.triangle.v3} : Finset ℝ²))
def IsFormC_v2 {A : Finset ℝ²} (S : FiniteEndpointShell A) (r : ℝ) : Prop :=
  ∃ y : ℝ²,
    y ∈ S.I1 ∧
    (S.witnessClassAt_v2 r ∩ S.CP.C3 = ({S.triangle.v1} : Finset ℝ²)) ∧
    (S.witnessClassAt_v2 r ∩ S.CP.C1 = ({y} : Finset ℝ²))
def IsFormA_v3 {A : Finset ℝ²} (S : FiniteEndpointShell A) (r : ℝ) : Prop :=
  ∃ x y : ℝ²,
    x ∈ S.I1 ∧
    y ∈ S.I2 ∧
    (S.witnessClassAt_v3 r ∩ S.CP.C1 = ({x} : Finset ℝ²)) ∧
    (S.witnessClassAt_v3 r ∩ S.CP.C2 = ({y} : Finset ℝ²))
def IsFormB_v3 {A : Finset ℝ²} (S : FiniteEndpointShell A) (r : ℝ) : Prop :=
  ∃ x : ℝ²,
    x ∈ S.I1 ∧
    (S.witnessClassAt_v3 r ∩ S.CP.C1 = ({x} : Finset ℝ²)) ∧
    (S.witnessClassAt_v3 r ∩ S.CP.C2 = ({S.triangle.v1} : Finset ℝ²))
def IsFormC_v3 {A : Finset ℝ²} (S : FiniteEndpointShell A) (r : ℝ) : Prop :=
  ∃ y : ℝ²,
    y ∈ S.I2 ∧
    (S.witnessClassAt_v3 r ∩ S.CP.C1 = ({S.triangle.v2} : Finset ℝ²)) ∧
    (S.witnessClassAt_v3 r ∩ S.CP.C2 = ({y} : Finset ℝ²))

abbrev N4dExcludesFormA_v1 {A : Finset ℝ²} (S : FiniteEndpointShell A) : Prop :=
  ∀ {r : ℝ} (_hr : 0 < r) (_hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
      (_hesc : ¬ S.witnessClassAt_v1 r ⊆ S.CP.C1),
    S.IsFormA_v1 r → False

abbrev N4dExcludesFormB_v1 {A : Finset ℝ²} (S : FiniteEndpointShell A) : Prop :=
  ∀ {r : ℝ} (_hr : 0 < r) (_hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
      (_hesc : ¬ S.witnessClassAt_v1 r ⊆ S.CP.C1),
    S.IsFormB_v1 r → False

abbrev N4dExcludesFormC_v1 {A : Finset ℝ²} (S : FiniteEndpointShell A) : Prop :=
  ∀ {r : ℝ} (_hr : 0 < r) (_hcard : 4 ≤ (S.witnessClassAt_v1 r).card)
      (_hesc : ¬ S.witnessClassAt_v1 r ⊆ S.CP.C1),
    S.IsFormC_v1 r → False

abbrev N4dExcludesFormA_v2 {A : Finset ℝ²} (S : FiniteEndpointShell A) : Prop :=
  ∀ {r : ℝ} (_hr : 0 < r) (_hcard : 4 ≤ (S.witnessClassAt_v2 r).card)
      (_hesc : ¬ S.witnessClassAt_v2 r ⊆ S.CP.C2),
    S.IsFormA_v2 r → False

abbrev N4dExcludesFormB_v2 {A : Finset ℝ²} (S : FiniteEndpointShell A) : Prop :=
  ∀ {r : ℝ} (_hr : 0 < r) (_hcard : 4 ≤ (S.witnessClassAt_v2 r).card)
      (_hesc : ¬ S.witnessClassAt_v2 r ⊆ S.CP.C2),
    S.IsFormB_v2 r → False

abbrev N4dExcludesFormC_v2 {A : Finset ℝ²} (S : FiniteEndpointShell A) : Prop :=
  ∀ {r : ℝ} (_hr : 0 < r) (_hcard : 4 ≤ (S.witnessClassAt_v2 r).card)
      (_hesc : ¬ S.witnessClassAt_v2 r ⊆ S.CP.C2),
    S.IsFormC_v2 r → False

abbrev N4dExcludesFormA_v3 {A : Finset ℝ²} (S : FiniteEndpointShell A) : Prop :=
  ∀ {r : ℝ} (_hr : 0 < r) (_hcard : 4 ≤ (S.witnessClassAt_v3 r).card)
      (_hesc : ¬ S.witnessClassAt_v3 r ⊆ S.CP.C3),
    S.IsFormA_v3 r → False

abbrev N4dExcludesFormB_v3 {A : Finset ℝ²} (S : FiniteEndpointShell A) : Prop :=
  ∀ {r : ℝ} (_hr : 0 < r) (_hcard : 4 ≤ (S.witnessClassAt_v3 r).card)
      (_hesc : ¬ S.witnessClassAt_v3 r ⊆ S.CP.C3),
    S.IsFormB_v3 r → False

abbrev N4dExcludesFormC_v3 {A : Finset ℝ²} (S : FiniteEndpointShell A) : Prop :=
  ∀ {r : ℝ} (_hr : 0 < r) (_hcard : 4 ≤ (S.witnessClassAt_v3 r).card)
      (_hesc : ¬ S.witnessClassAt_v3 r ⊆ S.CP.C3),
    S.IsFormC_v3 r → False

end FiniteEndpointShell
end Problem97
end Batch3N9


