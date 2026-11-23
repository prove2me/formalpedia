-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeCosetScaledRiemannSum
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeCosetScaledRiemannSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:30:32.157072+00:00
-- url     : https://prove2.me/theorems/bcad13c2-a40d-4716-ae6f-1eccc53b34a4
-- title:
--   Lattice Coset Scaled Riemann Sum
-- statement:
--   Definitions and structural lemmas for Lattice Coset Scaled Riemann Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeCosetScaledRiemannSum.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScalingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanFundamentalDomainIntegersStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ScalingMeasureProductArchimedeanStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
noncomputable section
namespace GlobalTheory.CompanionTheory.Equi.LatSum
section Abstract
variable {A O Q ι : Type} [AddCommGroup A] [AddCommGroup O] [Fintype ι] [Fintype Q]
def reps (j : O →+ A) (rep : Q → O) : Finset (ι → A) :=
  Finset.univ.image fun (c : ι → Q) (i : ι) => j (rep (c i))
end Abstract
def scal {R : Type} (ι : Type) [CommRing R] (t : R) : (ι → R) →+ (ι → R) where
  toFun y i := t * y i
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp [mul_add]
end GlobalTheory.CompanionTheory.Equi.LatSum


