-- Prove2me | Definitions.Def_r03_defs_de73be8e06_r03_sp01_cyclic_residual_assembly_candidate_v1
-- name    : r03_defs_de73be8e06_r03_sp01_cyclic_residual_assembly_candidate_v1
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T01:20:41.39823+00:00
-- url     : https://prove2.me/theorems/ceec3f61-7338-4627-9082-fb14a28aa170
-- title:
--   R03 P3-factor definition module: r03_defs_de73be8e06_r03_sp01_cyclic_residual_assembly_candidate_v1
-- statement:
--   This module packages source-faithful finite-graph, matching, port, or bookkeeping structures used by reusable auxiliary theorems in the cubic P3-partition formalization. It contains definitions and structural interfaces only; it does not assert closure of the open root problem.
--
--   **Formalization Note** The code was extracted from the cited candidate artifact and its exact digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-cyclic-residual-assembly-candidate-v1.lean; source SHA-256 e23bffcd20bcb1b9a46fb9327ef8ac9b17731d58c0ff29de5fb06327cb8d5a18; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Definitions.Def_cubic_p3_partition_models

/-!
# Cyclic residue suffix and residual assembly bridge

Candidate-only formalization for `problem:opg-46613-p3-partition`.
A cyclic component of order `3*k+r` is reduced to its suffix of order
`3*k`, leaving a prefix of `r` exceptional vertices.  If a supplied factor
covers the exceptional vertices across all components, the suffix factors and
that residual factor assemble into an ambient factor.

This source deliberately treats the residual factor, the component
presentation, and all ambient edge inclusions as hypotheses.  It does not
prove that a cubic 3-connected graph supplies them.
-/

namespace CubicP3Partition

universe u v
set_option maxHeartbeats 1000000

/-- The suffix of a cyclicly ordered component after a prefix of `lo` vertices.
The proof that the displayed `Fin n` indices exist is retained in the subtype
rather than hidden in a proof argument to the definition. -/
def R03SP01V2SuffixSet
    {V : Type u} (n k lo : Nat) (e : Fin n ≃ V) : Set V :=
  {v | ∃ i : Fin (k * 3), ∃ h : lo + i.val < n,
    v = e ⟨lo + i.val, h⟩}

def R03SP01V2P3FactorEquiv
    {U : Type u} {W : Type v} [Fintype U]
    (GU : SimpleGraph U) (GW : SimpleGraph W)
    (e : U ≃ W)
    (hAdj : ∀ {x y : U}, GU.Adj x y → GW.Adj (e x) (e y))
    (p : P3Factor GU) : P3Factor GW := by
  refine {
    blockCount := p.blockCount
    place := p.place.trans e
    edge01 := ?_
    edge12 := ?_
  }
  · intro i
    exact hAdj (p.edge01 i)
  · intro i
    exact hAdj (p.edge12 i)

/-- Distribute `(Σ i, α i) × β` over the dependent sum. -/
def R03SP01V2SigmaProdDistrib {ι : Type u} {α : ι → Type v} {β : Type v} :
    ((Σ i, α i) × β) ≃ (Σ i, (α i × β)) where
  toFun z := ⟨z.1.1, (z.1.2, z.2)⟩
  invFun z := ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  left_inv z := by cases z with | mk s b => cases s <;> rfl
  right_inv z := by cases z with | mk i z => cases z <;> rfl

end CubicP3Partition


