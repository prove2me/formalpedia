-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:27.916292+00:00
-- url     : https://prove2.me/theorems/4bdab79b-5d51-48f0-b43a-b5a43d5e5a39
-- title:
--   Is Bichar Pairing
-- statement:
--   Definitions and structural lemmas for Is Bichar Pairing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IsBicharPairing.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology
namespace GlobalTheory.LocMod.Inhab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
variable (Y Y') in

def box (a : kˣ) : AddSubgroup (Matrix Y Y' k) where
  carrier := {x | ∀ r q, valuation k (x r q) ≤ valuation k (a : k)}
  zero_mem' := fun r q => by simp
  add_mem' := fun ha hb r q => Valuation.map_add_le _ (ha r q) (hb r q)
  neg_mem' := fun ha r q => by simpa using ha r q
def pairing (ψ : AddChar k Circle) (t b : Matrix Y Y' k) : ℂ := ψ (∑ r, ∑ q, b r q * t r q)
end GlobalTheory.LocMod.Inhab
end


