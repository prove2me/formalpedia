-- Prove2me | Definitions.Def_Erdos9796FiniteNine_N8Interface
-- name    : Erdos9796FiniteNine_N8Interface
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-09T06:32:22.445991+00:00
-- url     : https://prove2.me/theorems/8338ae4d-30db-4944-bb5e-fa2cdb502144
-- title:
--   Finite-nine N4/N8 endpoint interface
-- statement:
--   Cap containment and indexed cap interiors used in the final exact nine-point contradiction.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/tree/a46894f6078319d3001d06310531df50af0f6bbd/lean/Erdos9796Proof/P97/N8

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796FiniteNine_Forms

/-! Definition-only final N4/N8 interface used by the nine public child statements. -/

set_option backward.isDefEq.respectTransparency false
open scoped EuclideanGeometry
open Finset

namespace Batch3N9
namespace Problem97
namespace FiniteEndpointShell

def N4eCapContainment {A : Finset ℝ²} (S : FiniteEndpointShell A) : Prop :=
  (∀ {r : ℝ}, 0 < r →
      4 ≤ (A.filter (fun x => dist S.triangle.v1 x = r)).card →
      A.filter (fun x => dist S.triangle.v1 x = r) ⊆ S.CP.C1) ∧
  (∀ {r : ℝ}, 0 < r →
      4 ≤ (A.filter (fun x => dist S.triangle.v2 x = r)).card →
      A.filter (fun x => dist S.triangle.v2 x = r) ⊆ S.CP.C2) ∧
  (∀ {r : ℝ}, 0 < r →
      4 ≤ (A.filter (fun x => dist S.triangle.v3 x = r)).card →
      A.filter (fun x => dist S.triangle.v3 x = r) ⊆ S.CP.C3)

@[reducible] noncomputable def capByIndex
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (i : Fin 3) : Finset ℝ² :=
  match i.1 with
  | 0 => S.CP.C1
  | 1 => S.CP.C2
  | _ => S.CP.C3
@[reducible] noncomputable def capInteriorByIndex
    {A : Finset ℝ²} (S : FiniteEndpointShell A) (i : Fin 3) : Finset ℝ² :=
  match i.1 with
  | 0 => S.I1
  | 1 => S.I2
  | _ => S.I3

end FiniteEndpointShell
end Problem97
end Batch3N9


