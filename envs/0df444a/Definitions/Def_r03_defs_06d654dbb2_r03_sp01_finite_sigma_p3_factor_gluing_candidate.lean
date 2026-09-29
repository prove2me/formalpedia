-- Prove2me | Definitions.Def_r03_defs_06d654dbb2_r03_sp01_finite_sigma_p3_factor_gluing_candidate
-- name    : r03_defs_06d654dbb2_r03_sp01_finite_sigma_p3_factor_gluing_candidate
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T01:20:52.355592+00:00
-- url     : https://prove2.me/theorems/c80ae8f1-6a28-4c9d-83e5-466396d42d9b
-- title:
--   R03 P3-factor definition module: r03_defs_06d654dbb2_r03_sp01_finite_sigma_p3_factor_gluing_candidate
-- statement:
--   This module packages source-faithful finite-graph, matching, port, or bookkeeping structures used by reusable auxiliary theorems in the cubic P3-partition formalization. It contains definitions and structural interfaces only; it does not assert closure of the open root problem.
--
--   **Formalization Note** The code was extracted from the cited candidate artifact and its exact digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-finite-sigma-p3-factor-gluing-candidate-v1.lean; source SHA-256 da38b82fb351e130899db86c06a959f6c979e6f23d57b66170f7c297a7886a26; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Definitions.Def_cubic_p3_partition_models

/-!
# Finite dependent-sum gluing for P3 factors

Candidate-only formalization for `problem:opg-46613-p3-partition`.
Bindings: problem contract SHA-256
`4a95f992a4ad0225a5d28b64ebb8172cfa123a0c75158e1c680f3266d16341dd`,
statement SHA-256
`3c1569b2adae0a7571fcd9b8ade6f0db66df27bc341cd2324fe28ab11f807dc0`,
attempt `attempt:opg46613-obligation-planning-v1`, graph
`graph:opg46613-obligations-v1`, and obligation
`obligation:r03-root-p3-factor`.

The theorem generalizes binary disjoint-sum gluing to an arbitrary finite
family of possibly dependent vertex types.  It only transports local edges
into an ambient graph; it does not assert that the summands are graph
components, choose a matching or 2-factor, or close the root.
-/

namespace CubicP3Partition

universe u v
set_option maxHeartbeats 1000000

/-- Distribute a fixed product over a dependent finite sum. -/
def R03SP01SigmaProdDistrib {ι : Type u} {α : ι → Type v} {β : Type v} :
    ((Σ i, α i) × β) ≃ (Σ i, (α i × β)) where
  toFun z := ⟨z.1.1, (z.1.2, z.2)⟩
  invFun z := ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  left_inv z := by cases z with | mk s b => cases s <;> rfl
  right_inv z := by cases z with | mk i z => cases z <;> rfl

/-- Transport a P3Factor along an equivalence when its local edges remain
edges in the target graph. -/
def R03SP01P3FactorEquiv
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

end CubicP3Partition


