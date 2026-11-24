-- Prove2me | Definitions.Def_CSL_Circuit_Framework_CircuitWorkspace
-- name    : CSL_Circuit_Framework_CircuitWorkspace
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:35:14.098322+00:00
-- url     : https://prove2.me/theorems/e8c7a28d-fabf-4467-a49a-b05cff34d785
-- title:
--   Coded sorting library: Circuit / Framework / CircuitWorkspace
-- statement:
--   Module `CodedSorting.Circuit.Framework.CircuitWorkspace` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Named file slots of the already implemented network layer. This list
--   covers banks, gate outputs, and all matrix/scalar address programs. Outer
--   partition/gather/initialization programs must be added before calling it a
--   complete invocation workspace.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Framework.CircuitWorkspace

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Memory_ProgramWorkspace
import Definitions.Def_CSL_Shared_Memory_PhysicalLayerCost

/-! Named file slots of the already implemented network layer. This list
covers banks, gate outputs, and all matrix/scalar address programs. Outer
partition/gather/initialization programs must be added before calling it a
complete invocation workspace. -/
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 250000
namespace CSL.CircuitWorkspace
open RecursiveExchange RecursiveExchangeCost PhysicalLayerCost ProgramWorkspace
open scoped BigOperators
noncomputable section

/-- A fresh result file for each actual XOR scan, including intermediate
control sums; forwarded source/pass outputs do not allocate a new file. -/
def GateSlot := (e : Edge) × Fin (edgeGateScans e)

instance gateSlotFintype : Fintype GateSlot :=
  inferInstanceAs (Fintype ((e : Edge) × Fin (edgeGateScans e)))

theorem gate_slot_bound : Fintype.card GateSlot≤gateLocalConstant := by
  have h : Fintype.card GateSlot = ∑ e : Edge, edgeGateScans e := by
    rw [show Fintype.card GateSlot = Fintype.card ((e : Edge) × Fin (edgeGateScans e)) from
      Fintype.card_congr (Equiv.refl _)]
    simp [Fintype.card_sigma]
  rw [h, gateLocalConstant]
  exact Finset.sum_le_sum (fun e _ => Nat.le_mul_of_pos_left (edgeGateScans e) (by decide : 0<3))

/-- Two boundary files, all source registers, all stored physical edges,
actual XOR-control results, and actual per-pass bucket/output files. -/
def KnownLayerSlot (f P G S : ℕ) (hG : 0<G) (hS : 0<S) :=
  Fin 2 ⊕ Reg ⊕ Edge ⊕ GateSlot ⊕ AddressSlot f P G S hG hS

/-- Compose two finite file-name assignments without enumerating the enormous
combined network type. -/
def sumIndex {α β : Type*} {a b : ℕ} (left : α↪Fin a) (right : β↪Fin b) :
    α⊕β↪Fin (a+b) :=
  (left.sumMap right).trans finSumFinEquiv.toEmbedding

def gateSlotIndex : GateSlot↪Fin gateLocalConstant where
  toFun slot := ((Fintype.equivFin GateSlot) slot).castLE gate_slot_bound
  inj' x y h := by
    apply (Fintype.equivFin GateSlot).injective
    apply Fin.ext
    simpa only [Fin.coe_castLE] using congrArg (@Fin.val gateLocalConstant) h

/-- Tagged finite budgets avoid forcing evaluation of the enormous closed
network enumeration merely to flatten its file identifiers. -/
abbrev BudgetSlot := Fin 2 ⊕ Fin Parameters.W ⊕ Fin (Fintype.card Edge) ⊕
  Fin gateLocalConstant ⊕ Fin addressLocalConstant

/-- The budget is exactly the cardinality of the explicit tagged family,
so no unspecified large constant is used. -/
def knownLayerBudget := Fintype.card BudgetSlot

/-- Every actual known-layer file has a distinct tag within the explicit
fixed finite budgets. -/
def knownLayerTagIndex (f P G S : ℕ) (hG : 0<G) (hS : 0<S) :
    KnownLayerSlot f P G S hG hS↪BudgetSlot :=
  (Function.Embedding.refl _).sumMap
    (roleEnumeration.toEmbedding.sumMap
      ((Fintype.equivFin Edge).toEmbedding.sumMap
        (gateSlotIndex.sumMap (addressSlotIndex f P G S hG hS))))

def knownLayerIndex (f P G S : ℕ) (hG : 0<G) (hS : 0<S) :
    KnownLayerSlot f P G S hG hS↪Fin knownLayerBudget :=
  (knownLayerTagIndex f P G S hG hS).trans (Fintype.equivFin BudgetSlot).toEmbedding

theorem knownLayerIndex_injective (f P G S : ℕ) (hG : 0<G) (hS : 0<S) :
    Function.Injective (knownLayerIndex f P G S hG hS) :=
  (knownLayerIndex f P G S hG hS).injective

/-- Uniform polynomial exponent for allocating all known-layer files of
all real recursive invocations simultaneously. -/
def knownExponent := Nat.clog 2 knownLayerBudget+2*Nat.clog radix (Parameters.S+1)+1

end
end CSL.CircuitWorkspace


