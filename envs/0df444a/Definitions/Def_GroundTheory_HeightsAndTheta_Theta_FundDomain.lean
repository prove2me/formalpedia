-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_FundDomain
-- name    : GroundTheory_HeightsAndTheta_Theta_FundDomain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:46.482361+00:00
-- url     : https://prove2.me/theorems/6e032565-02c4-437e-9e70-f30826674304
-- title:
--   Fund Domain
-- statement:
--   Definitions and structural lemmas for Fund Domain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/FundDomain.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Theta
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G]
def saturate (Γ : Subgroup G) (A : Set G) : Set G := {y | ∃ γ ∈ Γ, γ⁻¹ * y ∈ A}
def firstHit (Γ : Subgroup G) (A : ℕ → Set G) : Set G :=
  ⋃ i, (A i \ saturate Γ (⋃ j < i, A j))
end GroundTheory.Heights₂.Theta


