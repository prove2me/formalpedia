-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousCohomologyVanishesOfPrimeToLNormalNoIn
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousCohomologyVanishesOfPrimeToLNormalNoIn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:06.566824+00:00
-- url     : https://prove2.me/theorems/d651cff0-f047-4aa3-ab07-3dfba9bdc5f4
-- title:
--   Continuous Cohomology Vanishes Of Prime To LNormal No In
-- statement:
--   Definitions and structural lemmas for Continuous Cohomology Vanishes Of Prime To LNormal No In, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ContinuousCohomologyVanishesOfPrimeToLNormalNoIn.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Gal
namespace GlobalTheory.PrimeToNormalVanishing
section Algebra
variable {G Q R M : Type} [Group G] [Group Q] [CommRing R] [AddCommGroup M] [Module R M]
  (ρ : Representation R G M) (π : G →* Q) (J : Subgroup G) (K : Subgroup Q) [Fintype K]
end Algebra
end GlobalTheory.PrimeToNormalVanishing


