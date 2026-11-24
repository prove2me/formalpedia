-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdGraphModel
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdGraphModel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:28.11681+00:00
-- url     : https://prove2.me/theorems/3e6ac4c2-3430-40a0-bc21-701b56f29ed0
-- title:
--   PDual Std Graph Model
-- statement:
--   Definitions and structural lemmas for PDual Std Graph Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdGraphModel.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdImageBot
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
namespace StandardDualGraphModel
open StandardDualImageBottom
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T]
def coneLift (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    MRing (dualBlocks T) ⧸ dualIdeal b →+* MvPolynomial Unit (ProjField K i) :=
  Ideal.Quotient.lift (dualIdeal b)
    (mConeMap (dualLatticeCoord b) : MRing (dualBlocks T) →+* MvPolynomial Unit (ProjField K i)) fun _ ha => ha
def modelMap (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    MvPolynomial Unit (MRing (dualBlocks T) ⧸ dualIdeal b) →+* dualStdModelField K i :=
  (algebraMap (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) _).comp (MvPolynomial.map (coneLift b))
end StandardDualGraphModel
end
end GroundTheory.Heights₂.Heights


