-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchGermDimOne
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchGermDimOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:03:23.256162+00:00
-- url     : https://prove2.me/theorems/eae77ae7-f300-456d-84e4-fa06db2c086a
-- title:
--   St Branch Germ Dim One
-- statement:
--   Definitions and structural lemmas for St Branch Germ Dim One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StBranchGermDimOne.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchNormalisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets Filter Topology
noncomputable section
def BranchGermDimOne.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (m : ℕ) (c : Fin m → VarBranch I 1 q),
    0 < m → (∃ N ∈ 𝓝 q, zeroSet I ∩ N ⊆ ⋃ b, (c b).image) →
      ringKrullDim (curveLocalRing I q) = 1
end
end GroundTheory.Heights₂.Heights


