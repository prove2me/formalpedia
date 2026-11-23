-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsLevelInverseCongruence
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsLevelInverseCongruence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:33.799574+00:00
-- url     : https://prove2.me/theorems/1328077a-b0a6-4ae2-87b5-8f672240d6cc
-- title:
--   Exists Level Inverse Congruence
-- statement:
--   Definitions and structural lemmas for Exists Level Inverse Congruence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsLevelInverseCongruence.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix Filter Topology
namespace GlobalTheory.CompanionTheory.GLSmall
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def small (ϖ : k) (n l : ℕ) : Set (GL (Fin n) k) :=
  {g | (∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j)
        ≤ valuation k ϖ ^ l) ∧
    ∀ i j, valuation k (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
        - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k ϖ ^ l}
end GlobalTheory.CompanionTheory.GLSmall


