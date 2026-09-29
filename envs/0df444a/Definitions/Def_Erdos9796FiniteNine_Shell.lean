-- Prove2me | Definitions.Def_Erdos9796FiniteNine_Shell
-- name    : Erdos9796FiniteNine_Shell
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-09T06:30:48.899414+00:00
-- url     : https://prove2.me/theorems/ce37debe-f180-46db-96cb-4cea533473dc
-- title:
--   Finite-nine endpoint shell
-- statement:
--   The boundary triangle, three cap regions, distinguished vertices, and related geometric data used by the exact nine-point argument.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/a46894f6078319d3001d06310531df50af0f6bbd/lean/Erdos9796Proof/P97/N9Endpoint/Shell.lean

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796FiniteNine_CountingCore

/-! Definition-only endpoint shell extracted from the authenticated finite-nine source. -/

set_option backward.isDefEq.respectTransparency false
open scoped EuclideanGeometry InnerProductSpace
open Finset

namespace Batch3N9
namespace Problem97

structure FiniteEndpointShell (A : Finset ℝ²) where
  hne : A.Nonempty
  hcard9 : A.card = 9
  hconv : ConvexIndep A
  hK4 : HasNEquidistantProperty 4 A
  hnoncol : ¬ Collinear ℝ (A : Set ℝ²)
  hbd : 3 ≤ (A.filter (fun p =>
    dist p (Problem97.MEC.mec A hne).center =
      (Problem97.MEC.mec A hne).radius)).card
  MT : Problem97.MEC.NonObtuseCircumscribedMoserTriangle A hne hnoncol
  hCirc : ∃ h12 h23 h13,
    MT.toMoserTriangle.case_split = Or.inl ⟨h12, h23, h13⟩
  CP : Problem97.CapTriple A (MT.toMoserTriangle.toStructural hCirc)
  hcapSum12 : CP.C1.card + CP.C2.card + CP.C3.card = 12
  Packet : Problem97.CircumscribedMECPacket A (MT.toMoserTriangle.toStructural hCirc)

namespace FiniteEndpointShell

@[reducible] def triangle {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    Problem97.MoserTriangle A :=
  S.MT.toMoserTriangle.toStructural S.hCirc
@[reducible] def triangle2 {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    Problem97.MoserTriangle A :=
  { v1 := S.triangle.v2
    v2 := S.triangle.v3
    v3 := S.triangle.v1
    v1_mem := S.triangle.v2_mem
    v2_mem := S.triangle.v3_mem
    v3_mem := S.triangle.v1_mem
    v12_ne := S.triangle.v23_ne
    v13_ne := S.triangle.v12_ne.symm
    v23_ne := S.triangle.v13_ne.symm }
@[reducible] def triangle3 {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    Problem97.MoserTriangle A :=
  { v1 := S.triangle.v3
    v2 := S.triangle.v1
    v3 := S.triangle.v2
    v1_mem := S.triangle.v3_mem
    v2_mem := S.triangle.v1_mem
    v3_mem := S.triangle.v2_mem
    v12_ne := S.triangle.v13_ne.symm
    v13_ne := S.triangle.v23_ne.symm
    v23_ne := S.triangle.v12_ne }
@[reducible] def packet2 {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    Problem97.CircumscribedMECPacket A S.triangle2 :=
  { center := S.Packet.center
    radius := S.Packet.radius
    radius_pos := S.Packet.radius_pos
    moser_on_boundary_1 := S.Packet.moser_on_boundary_2
    moser_on_boundary_2 := S.Packet.moser_on_boundary_3
    moser_on_boundary_3 := S.Packet.moser_on_boundary_1
    inner_at_v1 := S.Packet.inner_at_v2
    inner_at_v2 := S.Packet.inner_at_v3
    inner_at_v3 := S.Packet.inner_at_v1
    disk_contains_A := S.Packet.disk_contains_A }
@[reducible] def packet3 {A : Finset ℝ²} (S : FiniteEndpointShell A) :
    Problem97.CircumscribedMECPacket A S.triangle3 :=
  { center := S.Packet.center
    radius := S.Packet.radius
    radius_pos := S.Packet.radius_pos
    moser_on_boundary_1 := S.Packet.moser_on_boundary_3
    moser_on_boundary_2 := S.Packet.moser_on_boundary_1
    moser_on_boundary_3 := S.Packet.moser_on_boundary_2
    inner_at_v1 := S.Packet.inner_at_v3
    inner_at_v2 := S.Packet.inner_at_v1
    inner_at_v3 := S.Packet.inner_at_v2
    disk_contains_A := S.Packet.disk_contains_A }
@[reducible] noncomputable def I1 {A : Finset ℝ²} (S : FiniteEndpointShell A) : Finset ℝ² :=
  (S.CP.C1.erase S.MT.toMoserTriangle.v2).erase S.MT.toMoserTriangle.v3
@[reducible] noncomputable def I2 {A : Finset ℝ²} (S : FiniteEndpointShell A) : Finset ℝ² :=
  (S.CP.C2.erase S.MT.toMoserTriangle.v3).erase S.MT.toMoserTriangle.v1
@[reducible] noncomputable def I3 {A : Finset ℝ²} (S : FiniteEndpointShell A) : Finset ℝ² :=
  (S.CP.C3.erase S.MT.toMoserTriangle.v1).erase S.MT.toMoserTriangle.v2

end FiniteEndpointShell
end Problem97
end Batch3N9


