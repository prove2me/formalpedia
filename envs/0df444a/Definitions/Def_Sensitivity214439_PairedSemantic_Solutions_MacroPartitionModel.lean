-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroPartitionModel
-- name    : Sensitivity214439_PairedSemantic_Solutions_MacroPartitionModel
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:45:41.833941+00:00
-- url     : https://prove2.me/theorems/35972bbb-49dd-4dc3-a1ee-5354b952289f
-- title:
--   Finite representative partitions and compressed incidence budgets
-- statement:
--   Defines a lower-index representative map on Fin n, its fibers and guard multiplicities, incoming representative groups capped at two, and cross-class orientation consistency. Each group's allowed count is bounded by the minimum residual of its members. The weighted total charges counts by guard multiplicity, while compressedCount replaces repeated charges by one per group. Actual cluster maps obtain representatives by choosing their least equal-cluster index, with the required membership and order proofs.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MacroPartitionModel.lean lines 15–74; SHA256 75bc63c3566013a2fbd5cc11e3f36b7fc02c45fa9ea9e1025d1c4d8776dd5ea6; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

namespace SensitivityMacroPartitionModel
end SensitivityMacroPartitionModel



/-! Every partition of a finite indexed head set is represented by choosing
its least index in each class. The finite search may enumerate all functions
whose value at index i is at most i; no canonicality test is needed for
completeness. -/
namespace SensitivityMacroPartitionModel

open scoped BigOperators
set_option autoImplicit false

abbrev Partition (n : ℕ) := (i : Fin n) → Fin (i.val + 1)

def rootOf {n : ℕ} (p : Partition n) (i : Fin n) : Fin n :=
  ⟨(p i).val, (Nat.lt_succ_iff.mp (p i).isLt).trans_lt i.isLt⟩

def members {n : ℕ} (p : Partition n) (k : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => rootOf p i = k

def guardMembers {n : ℕ} (p : Partition n) (G : Finset (Fin n)) (k : Fin n) : Finset (Fin n) :=
  G.filter fun i => rootOf p i = k

def guardMultiplicity {n : ℕ} (p : Partition n) (G : Finset (Fin n)) (k : Fin n) : ℕ :=
  (guardMembers p G k).card

def incomingGroups {n : ℕ} (p : Partition n) (G : Finset (Fin n))
    (arc : Fin n → Fin n → Prop) [DecidableRel arc] (w : Fin n) : Finset (Fin n) :=
  (G.filter fun v => rootOf p v ≠ rootOf p w ∧ arc v w).image (rootOf p)

def incomingLevel {n : ℕ} (p : Partition n) (G : Finset (Fin n))
    (arc : Fin n → Fin n → Prop) [DecidableRel arc] (w : Fin n) : ℕ := min 2 (incomingGroups p G arc w).card

def CrossConsistent {n : ℕ} (p : Partition n) (arc : Fin n → Fin n → Prop) : Prop :=
  ∀ i j u v : Fin n, rootOf p i ≠ rootOf p j →
    rootOf p i = rootOf p v → rootOf p j = rootOf p u → arc i j → ¬ arc u v

instance {n : ℕ} (p : Partition n) (arc : Fin n → Fin n → Prop) [DecidableRel arc] :
    Decidable (CrossConsistent p arc) := by
  unfold CrossConsistent
  infer_instance

def groupCap {n : ℕ} (p : Partition n) (residual : Fin n → ℕ) (k : Fin n) : ℕ :=
  if h : (members p k).Nonempty then ((members p k).image residual).min' (h.image residual)
  else 0

abbrev BoundedCounts {n : ℕ} (p : Partition n) (residual : Fin n → ℕ) :=
  (k : Fin n) → Fin (groupCap p residual k + 1)

def weightedCount {n : ℕ} (p : Partition n) (G : Finset (Fin n)) (c : Fin n → ℕ) : ℕ :=
  ∑ k, guardMultiplicity p G k * c k

def compressedCount {n : ℕ} (p : Partition n) (G : Finset (Fin n)) (c : Fin n → ℕ) (e : ℕ) : ℕ :=
  e - weightedCount p G c + ∑ k, c k

noncomputable section
open scoped Classical

def fiber {n : ℕ} {M : Type} (cluster : Fin n → M) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => cluster j = cluster i

theorem mem_fiber_self {n : ℕ} {M : Type} (cluster : Fin n → M) (i : Fin n) : i ∈ fiber cluster i := by
  simp [fiber]

def least {n : ℕ} {M : Type} (cluster : Fin n → M) (i : Fin n) : Fin n :=
  (fiber cluster i).min' ⟨i,mem_fiber_self cluster i⟩

theorem least_le {n : ℕ} {M : Type} (cluster : Fin n → M) (i : Fin n) : least cluster i ≤ i :=
  Finset.min'_le _ _ (mem_fiber_self cluster i)

def representative {n : ℕ} {M : Type} (cluster : Fin n → M) : Partition n :=
  fun i => ⟨(least cluster i).val, Nat.lt_succ_of_le (least_le cluster i)⟩























end
end SensitivityMacroPartitionModel


