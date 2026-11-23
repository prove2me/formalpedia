-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_EigenLift
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_EigenLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:42.267881+00:00
-- url     : https://prove2.me/theorems/9b181f73-4244-472f-b393-66a79a16297e
-- title:
--   Eigen Lift
-- statement:
--   Definitions and structural lemmas for Eigen Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/EigenLift.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
def BetaSesqSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k]
    [Algebra R k] (B : FB R d O) (a : O) (ξ η : (Fin d → k) × (Fin d → k)),
    betaH k (OactH k B a ξ) η = betaH k ξ (OactH k B (star a) η)
def EigenOrthSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k]
    [Algebra R k] (B : FB R d O) (χ χ' : O → k) (ξ η : (Fin d → k) × (Fin d → k)),
    (∀ a, OactH k B a ξ = χ a • ξ) → (∀ a, OactH k B a η = χ' a • η) →
    (∃ a, IsUnit (χ a - χ' (star a))) → betaH k ξ η = 0
end ReciprocityTheory.ChartRestriction.G.TB


