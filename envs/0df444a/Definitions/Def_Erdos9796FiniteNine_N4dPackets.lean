-- Prove2me | Definitions.Def_Erdos9796FiniteNine_N4dPackets
-- name    : Erdos9796FiniteNine_N4dPackets
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-10T01:51:07.785852+00:00
-- url     : https://prove2.me/theorems/20e77876-f67d-4a4a-bb0e-7613b5d63ace
-- title:
--   Finite-nine N4d packet and core-support interface
-- statement:
--   Public data types recording escaped four-point witness patterns, together with the geometric facts supplied by the first cap-containment case analysis.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/0707e2c26e2e570e2b56ce656242cf5dec4d2584/lean/Erdos9796Proof/P97/N9Endpoint/N4e.lean

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796FiniteNine_N8Interface
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_CGN_CGN4g
import Definitions.Def_Erdos9796Counting_CGN_CGN6
import Definitions.Def_Erdos9796Counting_Cap_Partition
import Definitions.Def_Erdos9796Counting_Cap_PartitionFromMEC
import Definitions.Def_Erdos9796Counting_Cap_Structure
import Definitions.Def_Erdos9796Counting_CircumscribedMECPacket
import Definitions.Def_Erdos9796Counting_ConvexCyclicOrder_Construct
import Definitions.Def_Erdos9796Counting_Dumitrescu_L6
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_IsoscelesCount
import Definitions.Def_Erdos9796Counting_MEC_ArcAngle
import Definitions.Def_Erdos9796Counting_MEC_Basic
import Definitions.Def_Erdos9796Counting_MEC_Boundary
import Definitions.Def_Erdos9796Counting_Moser_Triangle
import Definitions.Def_Erdos9796Counting_Moser_TriangleNonObtuse
import Definitions.Def_Erdos9796Counting_SignedAreaOangle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Geometry.Euclidean.Simplex
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Lattice
import Theorems.Thm_Problem97_CGN_CGN4g_strictCapBlockData_of_supportCap_oriented
import Theorems.Thm_Problem97_CGN_CGN6b_nonacute_of_minorCapChainCoords
import Theorems.Thm_Problem97_CGN_CGN6norm_minorCapChainModel_of_mecCapPacket
import Theorems.Thm_Problem97_ConvexIndep_not_collinear_of_card_ge_three
import Theorems.Thm_Problem97_ConvexIndep_not_wbtw
import Theorems.Thm_Problem97_Dumitrescu_three_cap_decomposition
import Theorems.Thm_Problem97_MEC_exists_nonobtuse_circumscribed_triple
import Theorems.Thm_Problem97_MEC_no_diameter_under_k4
import Theorems.Thm_Problem97_MEC_not_collinear_of_three_dist_eq
import Theorems.Thm_Problem97_affineSpan_eq_top_of_not_collinear
import Theorems.Thm_Problem97_card_ge_five_of_K4
import Theorems.Thm_Problem97_center_same_side_as_apex_of_nonobtuse
import Theorems.Thm_Problem97_collinear_of_signedArea2_eq_zero
import Theorems.Thm_Problem97_exists_cut_sorted_enumeration_of_convexIndep
import Theorems.Thm_Problem97_inner_chord_eq_two_mul_inner_midpoint
import Theorems.Thm_Problem97_isCcwConvexPolygon_of_cut_sorted_arcAngle
import Theorems.Thm_Problem97_signedArea2_eq_zero_iff_collinear
import Theorems.Thm_Problem97_signedArea2_sign_eq_oangle_sign
import Theorems.Thm_Problem97_signedArea_prod_eq_inner_mul_dist_sq
import Theorems.Thm_Problem97_three_le_card_of_convexIndep_noncoll

open scoped EuclideanGeometry InnerProductSpace

namespace Batch3N9
open scoped EuclideanGeometry
open Finset
namespace Problem97
export _root_.Problem97 (signedArea2)
end Problem97
namespace Problem97
namespace FiniteEndpointShell

inductive EscapedForm where
  | a
  | b
  | c
  deriving DecidableEq, Repr

structure ZeroDefectCapLayout {A : Finset ℝ²} (S : FiniteEndpointShell A) where
  a1 : ℝ²
  b1 : ℝ²
  a2 : ℝ²
  b2 : ℝ²
  a3 : ℝ²
  b3 : ℝ²
  hI1 : S.I1 = ({a1, b1} : Finset ℝ²)
  hI2 : S.I2 = ({a2, b2} : Finset ℝ²)
  hI3 : S.I3 = ({a3, b3} : Finset ℝ²)

def SelectorV2Qv1Packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) (r : ℝ) : Prop :=
  let T := S.witnessClassAt_v2 r
  T.card = 4 ∧
  S.I2 ⊆ T ∧
  ∃ p : ℝ²,
    p ∈ ({Z.a1, Z.b1, S.triangle.v3} : Finset ℝ²) ∧
    T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
    T ∩ S.CP.C3 = ({S.triangle.v1} : Finset ℝ²)

def SelectorV3Qv1Packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) (r : ℝ) : Prop :=
  let T := S.witnessClassAt_v3 r
  ∃ p : ℝ²,
    p ∈ ({Z.a1, Z.b1, S.triangle.v2} : Finset ℝ²) ∧
    T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
    T ∩ S.CP.C2 = ({S.triangle.v1} : Finset ℝ²)

def SelectorV3Qa2Packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) (r : ℝ) : Prop :=
  let T := S.witnessClassAt_v3 r
  S.I3 ⊆ T ∧
  ∃ p : ℝ²,
    p ∈ ({Z.a1, Z.b1, S.triangle.v2} : Finset ℝ²) ∧
    T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
    T ∩ S.CP.C2 = ({Z.a2} : Finset ℝ²)

abbrev I3OnV3RadiusAtA2CardLeOne
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) : Prop :=
  (S.I3.filter (fun x => dist S.triangle.v3 x = dist S.triangle.v3 Z.a2)).card ≤ 1

abbrev I3NoPointOnV3RadiusAtA2
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) : Prop :=
  ∀ x ∈ S.I3, dist S.triangle.v3 x ≠ dist S.triangle.v3 Z.a2

abbrev I3V3A2NormalizedHeightGap
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) : Prop :=
  ∃ T : ℝ² → ℝ², ∃ tau : Problem97.CGN.SimilarityTransportData T,
    dist (T S.triangle.v3) (T Z.a2) < (T S.triangle.v3) 1 ∧
    ∀ x ∈ S.I3, (T x) 1 < 0

abbrev I3V3A2DeltaNormalization
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) : Prop :=
  ∃ T : ℝ² → ℝ², ∃ tau : Problem97.CGN.SimilarityTransportData T, ∃ δ : ℝ,
    T S.triangle.v1 = Problem97.CGN.vec2 0 0 ∧
    T S.triangle.v2 = Problem97.CGN.vec2 1 0 ∧
    T Z.a2 = Problem97.CGN.vec2 ((1 : ℝ) / 2) (Real.sqrt 3 / 2) ∧
    T S.triangle.v3 =
      Problem97.CGN.vec2
        (2 * Real.cos δ * Real.cos δ)
        (2 * Real.cos δ * Real.sin δ) ∧
    Real.pi / 4 ≤ δ ∧ δ < Real.pi / 3 ∧
    ∀ x ∈ S.I3, (T x) 1 < 0

def ZeroDefectCapLayout.b3n9m051_swapI1
    {A : Finset ℝ²} {S : FiniteEndpointShell A}
    (Z : ZeroDefectCapLayout S) : ZeroDefectCapLayout S where
  a1 := Z.b1
  b1 := Z.a1
  a2 := Z.a2
  b2 := Z.b2
  a3 := Z.a3
  b3 := Z.b3
  hI1 := by simpa [Finset.pair_comm] using Z.hI1
  hI2 := Z.hI2
  hI3 := Z.hI3

def ZeroDefectCapLayout.swapI2
    {A : Finset ℝ²} {S : FiniteEndpointShell A}
    (Z : ZeroDefectCapLayout S) : ZeroDefectCapLayout S where
  a1 := Z.a1
  b1 := Z.b1
  a2 := Z.b2
  b2 := Z.a2
  a3 := Z.a3
  b3 := Z.b3
  hI1 := Z.hI1
  hI2 := by
    ext x
    constructor <;> intro hx <;> simpa [Z.hI2, or_comm] using hx
  hI3 := Z.hI3

def FormBv1A2Packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) (r : ℝ) : Prop :=
  (Z.a2 : ℝ²) ∈ S.I2 ∧
  S.witnessClassAt_v1 r ∩ S.CP.C2 = ({Z.a2} : Finset ℝ²) ∧
  S.witnessClassAt_v1 r ∩ S.CP.C3 = ({S.triangle.v2} : Finset ℝ²)

def FormBv1A2SelectorV2Qv1Packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) (r s : ℝ) : Prop :=
  FormBv1A2Packet S Z r ∧ 0 < s ∧ SelectorV2Qv1Packet S Z s

def FormBv1B2Packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) (r : ℝ) : Prop :=
  (Z.b2 : ℝ²) ∈ S.I2 ∧
  S.witnessClassAt_v1 r ∩ S.CP.C2 = ({Z.b2} : Finset ℝ²) ∧
  S.witnessClassAt_v1 r ∩ S.CP.C3 = ({S.triangle.v2} : Finset ℝ²)

def FormBv1B2SelectorV2Qv1Packet
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) (r s : ℝ) : Prop :=
  FormBv1B2Packet S Z r ∧ 0 < s ∧ SelectorV2Qv1Packet S Z s

abbrev I3V3A2DeltaNormalizationOfExactPacket
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) : Prop :=
  ∀ {r s : ℝ},
    FormBv1A2SelectorV2Qv1Packet S Z r s →
    S.witnessClassAt_v2 s =
      insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²)) →
    S.I3V3A2DeltaNormalization Z

abbrev SharedCirclePointForcesV3
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) (r s : ℝ) : Prop :=
  ∀ p : ℝ²,
    p ∈ ({Z.a1, Z.b1, S.triangle.v3} : Finset ℝ²) →
    p ∈ S.witnessClassAt_v2 s →
    p ∈ S.witnessClassAt_v1 r →
    p = S.triangle.v3

def FormBv1A2SelectorV2LowerPacket
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) (r s : ℝ) : Prop :=
  let T := S.witnessClassAt_v2 s
  (Z.a2 : ℝ²) ∈ S.I2 ∧
  S.witnessClassAt_v1 r ∩ S.CP.C2 = ({Z.a2} : Finset ℝ²) ∧
  T.card = 4 ∧
  S.I2 ⊆ T ∧
  T ∩ S.CP.C1 = ({S.triangle.v3} : Finset ℝ²) ∧
  ((T ∩ S.CP.C3 = ({Z.a3} : Finset ℝ²)) ∨
   (T ∩ S.CP.C3 = ({Z.b3} : Finset ℝ²)))

def FormBv1B2SelectorV2LowerPacket
    {A : Finset ℝ²} (S : FiniteEndpointShell A)
    (Z : ZeroDefectCapLayout S) (r s : ℝ) : Prop :=
  let T := S.witnessClassAt_v2 s
  (Z.b2 : ℝ²) ∈ S.I2 ∧
  S.witnessClassAt_v1 r ∩ S.CP.C2 = ({Z.b2} : Finset ℝ²) ∧
  T.card = 4 ∧
  S.I2 ⊆ T ∧
  T ∩ S.CP.C1 = ({S.triangle.v3} : Finset ℝ²) ∧
  ((T ∩ S.CP.C3 = ({Z.a3} : Finset ℝ²)) ∨
   (T ∩ S.CP.C3 = ({Z.b3} : Finset ℝ²)))

/-- Explicit reusable facts established by the first N4e proof slice. -/
structure N4eCoreSupport {A : Finset ℝ²} (S : FiniteEndpointShell A) where
  layout : ZeroDefectCapLayout (S := S)
  I1_card_eq_two :
      S.I1.card = 2
  I2_card_eq_two :
      S.I2.card = 2
  I3_card_eq_two :
      S.I3.card = 2
  coreSelector_v1 {r : ℝ}
      (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v1 r).card) :
      (S.witnessClassAt_v1 r).card = 4 ∧
        S.I1 ⊆ S.witnessClassAt_v1 r ∧
        ((S.witnessClassAt_v1 r) ∩ S.CP.C2).card ≤ 1 ∧
        ((S.witnessClassAt_v1 r) ∩ S.CP.C3).card ≤ 1
  coreSelector_v2 {r : ℝ}
      (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v2 r).card) :
      (S.witnessClassAt_v2 r).card = 4 ∧
        S.I2 ⊆ S.witnessClassAt_v2 r ∧
        ((S.witnessClassAt_v2 r) ∩ S.CP.C1).card ≤ 1 ∧
        ((S.witnessClassAt_v2 r) ∩ S.CP.C3).card ≤ 1
  coreSelector_v3 {r : ℝ}
      (hr : 0 < r) (hcard : 4 ≤ (S.witnessClassAt_v3 r).card) :
      (S.witnessClassAt_v3 r).card = 4 ∧
        S.I3 ⊆ S.witnessClassAt_v3 r ∧
        ((S.witnessClassAt_v3 r) ∩ S.CP.C1).card ≤ 1 ∧
        ((S.witnessClassAt_v3 r) ∩ S.CP.C2).card ≤ 1
  formB_v1_split
      (Z : ZeroDefectCapLayout S) {r : ℝ}
      (hB : S.IsFormB_v1 r) :
      (∃ h : (Z.a2 : ℝ²) ∈ S.I2,
          S.witnessClassAt_v1 r ∩ S.CP.C2 = ({Z.a2} : Finset ℝ²)) ∨
        (∃ h : (Z.b2 : ℝ²) ∈ S.I2,
          S.witnessClassAt_v1 r ∩ S.CP.C2 = ({Z.b2} : Finset ℝ²))
  selectorShape_v2_split
      (Z : ZeroDefectCapLayout S) :
      ∃ r : ℝ, 0 < r ∧
        let T := S.witnessClassAt_v2 r
        T.card = 4 ∧
        S.I2 ⊆ T ∧
        ((∃ p : ℝ²,
            p ∈ ({Z.a1, Z.b1, S.triangle.v3} : Finset ℝ²) ∧
            T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
            T ∩ S.CP.C3 = ({S.triangle.v1} : Finset ℝ²)) ∨
         (∃ p : ℝ²,
            p ∈ ({Z.a1, Z.b1, S.triangle.v3} : Finset ℝ²) ∧
            T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
            T ∩ S.CP.C3 = ({Z.a3} : Finset ℝ²)) ∨
         (∃ p : ℝ²,
            p ∈ ({Z.a1, Z.b1, S.triangle.v3} : Finset ℝ²) ∧
            T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
            T ∩ S.CP.C3 = ({Z.b3} : Finset ℝ²)))
  selectorShape_v3_split
      (Z : ZeroDefectCapLayout S) :
      ∃ r : ℝ, 0 < r ∧
        let T := S.witnessClassAt_v3 r
        T.card = 4 ∧
        S.I3 ⊆ T ∧
        ((∃ p : ℝ²,
            p ∈ ({Z.a1, Z.b1, S.triangle.v2} : Finset ℝ²) ∧
            T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
            T ∩ S.CP.C2 = ({S.triangle.v1} : Finset ℝ²)) ∨
         (∃ p : ℝ²,
            p ∈ ({Z.a1, Z.b1, S.triangle.v2} : Finset ℝ²) ∧
            T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
            T ∩ S.CP.C2 = ({Z.a2} : Finset ℝ²)) ∨
         (∃ p : ℝ²,
            p ∈ ({Z.a1, Z.b1, S.triangle.v2} : Finset ℝ²) ∧
            T ∩ S.CP.C1 = ({p} : Finset ℝ²) ∧
            T ∩ S.CP.C2 = ({Z.b2} : Finset ℝ²)))
  qEqE_capOrder_opposite {q qs : ℝ²}
      (hqI3 : q ∈ S.I3) (hqsI3 : qs ∈ S.I3) (hne : q ≠ qs) :
      (dist S.triangle.v2 qs ^ 2 - dist S.triangle.v2 q ^ 2)
        * (dist S.triangle.v1 qs ^ 2 - dist S.triangle.v1 q ^ 2) < 0
  dist_sq_eq_coord_sq_add_coord_sq (x y : ℝ²) :
      dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2
  qEqE_f1_sinusoid (r δ ε t S : ℝ) (hS : S ^ 2 = 2 - 2 * Real.cos (δ - ε)) :
      ((((1 + r * Real.cos δ) + r * S * Real.cos t) - (1 + r * Real.cos (2 * δ - ε)))
            * ((1 + r * Real.cos δ) - 1)
          + (((r * Real.sin δ) + r * S * Real.sin t) - r * Real.sin (2 * δ - ε))
            * ((r * Real.sin δ) - 0))
        = r ^ 2 * S * (Real.cos (t - δ) + S / 2)
  qEqE_f2_sinusoid (r δ ε t S : ℝ) :
      ((((1 + r * Real.cos δ) + r * S * Real.cos t) - (1 + r * Real.cos (2 * δ - ε)))
            * (1 + r * Real.cos δ)
          + (((r * Real.sin δ) + r * S * Real.sin t) - r * Real.sin (2 * δ - ε))
            * (r * Real.sin δ))
        = r * S * ((1 + r * Real.cos δ) * Real.cos t + r * Real.sin δ * Real.sin t)
          + r * (r - r * (Real.cos δ * Real.cos ε + Real.sin δ * Real.sin ε) + Real.cos δ
                 - ((2 * Real.cos δ ^ 2 - 1) * Real.cos ε
                    + (2 * Real.sin δ * Real.cos δ) * Real.sin ε))
  qEqE_lowerArc_sameSign (r δ ε t S : ℝ)
      (hr : 0 < r) (hr1 : r < 1) (hS : 0 < S)
      (hS2eq : S ^ 2 = 2 - 2 * Real.cos (δ - ε))
      (hsd : 0 < Real.sin δ) (hcd : -(r / 2) < Real.cos δ)
      (hse : 0 < Real.sin ε) (hce : Real.cos ε < -(r / 2))
      (hs2de : Real.sin (2 * δ - ε) < 0) (hc2de : Real.cos (2 * δ - ε) < -(r / 2))
      (hlower : r * Real.sin δ + r * S * Real.sin t < 0) :
      0 ≤ (r ^ 2 * S * (Real.cos (t - δ) + S / 2))
          * (r * S * ((1 + r * Real.cos δ) * Real.cos t
                + r * Real.sin δ * Real.sin t)
             + r * (r - r * (Real.cos δ * Real.cos ε + Real.sin δ * Real.sin ε)
                  + Real.cos δ
                  - ((2 * Real.cos δ ^ 2 - 1) * Real.cos ε
                     + (2 * Real.sin δ * Real.cos δ) * Real.sin ε)))
  qEqE_lowerArc_sameSign_flipped_of_c2Side (r δ ε t S : ℝ)
      (hr : 0 < r) (hS : 0 < S)
      (hS2eq : S ^ 2 = 2 - 2 * Real.cos (δ - ε))
      (hsd : 0 < Real.sin δ) (hcd : -(r / 2) < Real.cos δ)
      (hse : 0 < Real.sin ε)
      (hδ0 : 0 ≤ δ) (hδπ : δ ≤ Real.pi)
      (hε0 : 0 ≤ ε) (hεπ : ε ≤ Real.pi)
      (hs2de : Real.sin (2 * δ - ε) < 0)
      (hside :
        Real.sin δ - Real.sin ε
          - r * (Real.sin ε * Real.cos δ - Real.cos ε * Real.sin δ) ≤ 0)
      (hlower : r * Real.sin δ + r * S * Real.sin t < 0) :
      0 ≤ (r ^ 2 * S * (Real.cos (t - δ) + S / 2))
          * (r * S * ((1 + r * Real.cos δ) * Real.cos t
                + r * Real.sin δ * Real.sin t)
             + r * (r - r * (Real.cos δ * Real.cos ε + Real.sin δ * Real.sin ε)
                  + Real.cos δ
                  - ((2 * Real.cos δ ^ 2 - 1) * Real.cos ε
                     + (2 * Real.sin δ * Real.cos δ) * Real.sin ε)))
  i3_v3_a2_normalized_height_gap_of_delta_normalization
      (Z : ZeroDefectCapLayout S)
      (hnorm : S.I3V3A2DeltaNormalization Z) :
      S.I3V3A2NormalizedHeightGap Z
  i3_no_point_on_v3_radius_at_a2_of_normalized_height_gap
      (Z : ZeroDefectCapLayout S)
      (hgap : S.I3V3A2NormalizedHeightGap Z) :
      S.I3NoPointOnV3RadiusAtA2 Z
  i3_on_v3_radius_at_a2_card_le_one_of_no_hit
      (Z : ZeroDefectCapLayout S)
      (hnohit : S.I3NoPointOnV3RadiusAtA2 Z) :
      S.I3OnV3RadiusAtA2CardLeOne Z
  selectorShape_v3_q_eq_v1_impossible
      (Z : ZeroDefectCapLayout S) {r : ℝ}
      (hpacket : SelectorV3Qv1Packet S Z r)
      (hv2v1 : dist S.triangle.v3 S.triangle.v2 < dist S.triangle.v3 S.triangle.v1) :
      False
  selectorShape_v3_q_eq_a2_impossible
      (Z : ZeroDefectCapLayout S) {r : ℝ}
      (hpacket : SelectorV3Qa2Packet S Z r)
      (hbound : S.I3OnV3RadiusAtA2CardLeOne Z) :
      False
  C2_same_open_side_of_base_chord_as_v3
      (Z : ZeroDefectCapLayout S) {r s : ℝ}
      (hbranch : FormBv1A2SelectorV2Qv1Packet S Z r s)
      (hexact : S.witnessClassAt_v2 s =
        insert Z.a2 (insert Z.b2 ({S.triangle.v3, S.triangle.v1} : Finset ℝ²))) :
      ∀ y ∈ ({Z.a2, S.triangle.v3} : Finset ℝ²),
        signedArea2 y S.triangle.v1 S.triangle.v2 *
          signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2 > 0
  c2_vertex_same_open_side_as_v3 {a₂ : ℝ²}
      (ha2 : a₂ ∈ S.I2) :
      0 < signedArea2 a₂ S.triangle.v1 S.triangle.v2 *
        signedArea2 S.triangle.v3 S.triangle.v1 S.triangle.v2
  signedArea2_baseChord_vec2 (p : ℝ²) :
      signedArea2 p (Problem97.CGN.vec2 (-1) 0) (Problem97.CGN.vec2 1 0) = 2 * p 1
  exists_base_transportData
      (q1 q2 : ℝ²) (hqne : q1 ≠ q2) :
      ∃ T0, ∃ tau0 : Problem97.CGN.SimilarityTransportData T0,
        T0 q1 = Problem97.CGN.vec2 (-1) 0 ∧
        T0 q2 = Problem97.CGN.vec2 1 0

end FiniteEndpointShell
end Problem97
end Batch3N9


