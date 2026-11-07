-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:38:19.347453+00:00
-- url     : https://prove2.me/theorems/c59e49a6-b187-4c5d-89b6-b8f245fc54fc
-- title:
--   LPSOriginal Filled Topology
-- statement:
--   Definitions and structural lemmas for LPSOriginal Filled Topology, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledTopology.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Mathlib.Topology.Bases
import Mathlib.Topology.Order
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
@[instance_reducible]
def lpsOriginalFilledTopology (N : ℕ) [NeZero N] : TopologicalSpace (LPSOriginalFilledCurve N) :=
  TopologicalSpace.coinduced
    (Sum.inl : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N)
    inferInstance ⊔
    ⨆ c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
      TopologicalSpace.coinduced (lpsOriginalFilledCuspParam N c) inferInstance
end
end QEC.Coding.TannerLiftedProduct


