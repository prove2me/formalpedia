-- Prove2me | Definitions.Def_PricingWithTips3DM_2a87ccd5372380dd3c8e0fc1
-- name    : PricingWithTips3DM_2a87ccd5372380dd3c8e0fc1
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:44:42.227757+00:00
-- url     : https://prove2.me/theorems/6b2b3d8e-713f-48b0-a408-66bcc2c71509
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OneHotMap
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_a46ec1070e8b9fcb3ebc4d0c
import Definitions.Def_PricingWithTips3DM_f343fdd0ddecda3ae03e650c
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Concrete serialization of finite one-hot maps

The semantic finite lookup builds one false-seeded disjunction per target
coordinate.  This module supplies the bridge to one fixed runtime controller:
the encoded target fibers execute to the exact `oneHotMapGateTrace`, including
empty fibers, with a linear machine-step bound.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

/-- Canonical runtime groups for every target fiber of a finite one-hot map. -/
def affineOneHotMapCanonicalGroups {n m : Nat} (start : Nat)
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m) :
    List AffineOrFinGroup :=
  affineOrFinCanonicalGroupsFrom start (oneHotMapFibers source f)

/-- The controller's forward symbol stream is the exact encoded semantic
one-hot-map trace. -/
theorem affineOneHotMapGateStream_eq_trace {n m : Nat} (start : Nat)
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m) :
    affineOrFinFamilyGateStream
        (affineOneHotMapCanonicalGroups start source f) =
      (oneHotMapGateTrace start source f).gates.flatMap
        encodeCircuitGate := by
  rw [affineOneHotMapCanonicalGroups,
    affineOrFinCanonicalFamilyGateStream_eq_trace,
    oneHotMapGateTrace_gates_eq_family]

/-- The fixed family controller executes a complete one-hot-map suffix and
halts with the exact semantic gate trace. -/
def affineOneHotMap_run {n m : Nat} (start : Nat)
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m)
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinFamilyLoopCfg
        (encodeAffineOrFinGroups
          (affineOneHotMapCanonicalGroups start source f)) output)
      (some (haltCfg affineOrFinRevProgram
        (((oneHotMapGateTrace start source f).gates.flatMap
          encodeCircuitGate).reverse ++ output)))
      (affineOrFinFamilyRevSteps
        (affineOneHotMapCanonicalGroups start source f)) := by
  simpa [affineOneHotMapCanonicalGroups,
    oneHotMapGateTrace_gates_eq_family] using
      affineOrFinFamilyCanonical_run start
        (oneHotMapFibers source f) output

/-- The concrete one-hot-map execution has a linear bound in its runtime
fiber encoding. -/
theorem affineOneHotMap_steps_le {n m : Nat} (start : Nat)
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m) :
    affineOrFinFamilyRevSteps
        (affineOneHotMapCanonicalGroups start source f) ≤
      100 * (encodeAffineOrFinGroups
        (affineOneHotMapCanonicalGroups start source f)).length + 2 :=
  affineOrFinFamilyRev_steps_le _

/-- The semantic builder itself appends exactly the family trace consumed by
the concrete controller. -/
theorem oneHotMap_gates_eq_disjunctionFamily (base : CircuitBuilder)
    {n m : Nat} (source : Fin n → CircuitBuilder.Wire)
    (f : Fin n → Fin m)
    (hsource : ∀ i, base.WireValid (source i)) :
    (oneHotMap base source f hsource).builder.gates =
      base.gates ++ CircuitBuilder.disjunctionFamilyGateTrace
        base.gates.length (oneHotMapFibers source f) := by
  rw [oneHotMap_gates_eq, oneHotMapGateTrace_gates_eq_family]

end CLRS.Chapter34.Turing.PolyBuilder


