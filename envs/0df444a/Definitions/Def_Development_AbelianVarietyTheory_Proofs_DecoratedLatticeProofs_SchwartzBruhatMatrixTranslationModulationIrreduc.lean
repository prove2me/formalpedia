-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:59.529856+00:00
-- url     : https://prove2.me/theorems/0dfc68c7-92c6-4112-b77e-650b6dff97b9
-- title:
--   Schwartz Bruhat Matrix Translation Modulation Irreduc
-- statement:
--   Definitions and structural lemmas for Schwartz Bruhat Matrix Translation Modulation Irreduc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SchwartzBruhatMatrixTranslationModulationIrreduc.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
open scoped Topology
noncomputable section
namespace GlobalTheory.IrredSB
section Alg
variable {G : Type} [AddCommGroup G]
open Classical in

def ind (K : AddSubgroup G) (t : G) : ℂ := if t ∈ K then 1 else 0
end Alg
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [Fintype Y']
def pair (b t : Matrix Y Y' k) : k := ∑ r, ∑ q, b r q * t r q
variable (k Y Y') in

def intMat : AddSubgroup (Matrix Y Y' k) where
  carrier := {u | ∀ r q, u r q ∈ 𝒪[k]}
  add_mem' ha hb r q := add_mem (ha r q) (hb r q)
  zero_mem' _ _ := zero_mem _
  neg_mem' ha r q := neg_mem (ha r q)
variable (k Y Y') in

def lat (n : ℕ) : AddSubgroup (Matrix Y Y' k) := (intMat k Y Y').map (nsmulAddMonoidHom n)
end GlobalTheory.IrredSB
namespace GlobalTheory.IrredSB
end GlobalTheory.IrredSB


