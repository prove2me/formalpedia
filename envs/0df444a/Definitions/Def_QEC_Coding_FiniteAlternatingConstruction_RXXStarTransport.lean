-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T12:51:06.161297+00:00
-- url     : https://prove2.me/theorems/5daaf33b-a232-4564-9239-5373c9ba4eab
-- title:
--   RXXStar Transport
-- statement:
--   Definitions and structural lemmas for RXXStar Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXXStarTransport.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport_Geometry
import Theorems.Thm_QEC_Coding_BDL26RXErrorPullback_updated_delta
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_actual_coboundary1
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_map2_x_zero
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RXXStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
def OneX (x : XCoord S i) (a b : Upper S depth i) : Prop :=
  hammingSupport (a+b) ⊆ (rxLx S depth i h).correctionRegion x
theorem updated_x_kernel (x : XCoord S i) (a b : Upper S depth i) :
    (rxContract S depth i h).rx_local_complexes.cxDelta1 x
      (restrictWordLinear ((rxLx S depth i h).correctionRegion x) (updated S depth i h a b))=0 := by
  have hk := (rxContract S depth i h).support_decomposition.cxDelta1_restriction_global x
    (updated S depth i h a b)
  rw [actual_coboundary1 S depth,updated_delta,map2_x_zero] at hk
  exact hk.symm
theorem localPotential_exists (x : XCoord S i) (a b : Upper S depth i) :
    ∃ s : LocalPotential S i x, (rxContract S depth i h).rx_local_complexes.cxDelta0 x s =
      restrictWordLinear ((rxLx S depth i h).correctionRegion x) (updated S depth i h a b) := by
  have hk := updated_x_kernel S depth i h x a b
  change _ ∈ LinearMap.ker ((rxContract S depth i h).rx_local_complexes.cxDelta1 x) at hk
  rw [(rxContract S depth i h).rx_local_cohomology.cx_h1_ker_eq_range x] at hk
  exact hk
def localPotential (x : XCoord S i) (a b : Upper S depth i) : LocalPotential S i x :=
  if restrictWordLinear ((rxLx S depth i h).correctionRegion x) (updated S depth i h a b)=0 then 0
  else Classical.choose (localPotential_exists S depth i h x a b)
def potential (x : XCoord S i) (a b : Upper S depth i) : Potential S depth i :=
  (rxContract S depth i h).support_decomposition.cxLift0 x (localPotential S depth i h x a b)
def remainder (x : XCoord S i) (a b : Upper S depth i) : Upper S depth i :=
  updated S depth i h a b + (indexedFamily S depth).coboundary0 i.succ
    (potential S depth i h x a b)
def lowerWord (x : XCoord S i) (a b : Upper S depth i) : Lower S depth i :=
  fun q => remainder S depth i h x a b
    (rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).val
def twoCopyImage (Y : Finset (ZCoord S i)) : Finset (FamilyZ S depth i.succ) :=
  Y.biUnion (zPairImage (rxData S depth i h))
end QEC.Coding.BDL26RXXStarTransport


