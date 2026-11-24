-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpen
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:29.296319+00:00
-- url     : https://prove2.me/theorems/0262868b-70b3-4d3b-952f-c1e4974e36cf
-- title:
--   St Isolated Fibre Open
-- statement:
--   Definitions and structural lemmas for St Isolated Fibre Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StIsolatedFibreOpen.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology Matrix
noncomputable section
def IsolatedFibreOpen.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin k) (Fin n) ℂ) (x : Fin n → ℂ),
    IsAffVariety J k → x ∈ zeroLocus J →
    (∃ W ∈ 𝓝 x, ∀ z ∈ W, z ∈ zeroLocus J → A *ᵥ z = A *ᵥ x → z = x) →
    ∀ W' ∈ 𝓝 x, (fun z => A *ᵥ z) '' (zeroLocus J ∩ W') ∈ 𝓝 (A *ᵥ x)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


