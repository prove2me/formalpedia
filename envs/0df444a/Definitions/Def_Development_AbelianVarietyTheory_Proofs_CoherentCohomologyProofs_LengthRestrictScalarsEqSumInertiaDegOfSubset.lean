-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:31.984114+00:00
-- url     : https://prove2.me/theorems/dc26c2df-8a70-4eb2-acfb-ebc68a8aeefd
-- title:
--   Length Restrict Scalars Eq Sum Inertia Deg Of Subset
-- statement:
--   Definitions and structural lemmas for Length Restrict Scalars Eq Sum Inertia Deg Of Subset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
namespace GlobalTheory
section Local
variable (R S X : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]
end Local
section Localized
variable {S : Type*} [CommRing S]
end Localized
section General
variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
end General
section Semilocal
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
theorem liesOver_maximalIdeal_of_isIntegral [Algebra.IsIntegral R S] (n : Ideal S)
    [n.IsMaximal] : n.LiesOver (maximalIdeal R) :=
  ⟨(eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) n)).symm⟩
end Semilocal
end GlobalTheory


