-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsBaseChangeAwayOfIntertwine
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsBaseChangeAwayOfIntertwine
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T23:44:30.369797+00:00
-- url     : https://prove2.me/theorems/3c3cef04-a301-45c3-b706-fbceefeae888
-- title:
--   Is Base Change Away Of Intertwine
-- statement:
--   Definitions and structural lemmas for Is Base Change Away Of Intertwine, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsBaseChangeAwayOfIntertwine.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
namespace GlobalTheory
section
variable {R₀ R A₀ A : Type} [CommRing R₀] [CommRing R] [CommRing A₀] [CommRing A] [Algebra R₀ R]
  [Algebra R₀ A₀] [Algebra R A] [Algebra R₀ A] [IsScalarTower R₀ R A]
  {N₀ N : Type} [AddCommGroup N₀] [Module R₀ N₀] [Module A₀ N₀] [IsScalarTower R₀ A₀ N₀]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] [Module R₀ N]
  [IsScalarTower R₀ R N] [IsScalarTower R₀ A N]
end
end GlobalTheory


