-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_WeightedHomogeneousSubmoduleBlockWeightIntEqRing
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_WeightedHomogeneousSubmoduleBlockWeightIntEqRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:38.855883+00:00
-- url     : https://prove2.me/theorems/80b22bc8-20d1-456d-a311-5128051d0958
-- title:
--   Weighted Homogeneous Submodule Block Weight Int Eq Ring
-- statement:
--   Definitions and structural lemmas for Weighted Homogeneous Submodule Block Weight Int Eq Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/WeightedHomogeneousSubmoduleBlockWeightIntEqRing.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
section Grading
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
  {M : Type*} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
end Grading
section Multiplicity
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
  (M : Type*) [AddCommGroup M] [Module (MRing ι R) M]
end Multiplicity
section Cycle
variable {K : Type*} [Fintype K] [DecidableEq K] (ι : K → Type*) (F : Type*) [Field F]
  (M : Type*) [AddCommGroup M] [Module (MRing ι F) M]
end Cycle
section Examples
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
end Examples
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel


