-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticeEuclidean
-- name    : GroundTheory_GlobalFields_TateThesis_TraceLatticeEuclidean
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:26.983332+00:00
-- url     : https://prove2.me/theorems/6c351939-29b6-4063-831f-32fc6831383f
-- title:
--   Trace Lattice Euclidean
-- statement:
--   Definitions and structural lemmas for Trace Lattice Euclidean, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceLatticeEuclidean.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceDualLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical RealInnerProductSpace nonZeroDivisors
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
abbrev euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (idealLattice K I) (mixedToEuclidean K).symm.toLinearMap
abbrev euclideanConjIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (idealLattice K I) (mixedToEuclideanConj K).symm.toLinearMap
end
end GroundTheory.Global


