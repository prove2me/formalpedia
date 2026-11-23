-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormDiagonalizes
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormDiagonalizes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:30.420358+00:00
-- url     : https://prove2.me/theorems/56f0e657-3a75-4400-b52b-73885f31f137
-- title:
--   Hermitian Unit Form Diagonalizes
-- statement:
--   Definitions and structural lemmas for Hermitian Unit Form Diagonalizes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormDiagonalizes.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinatePolynomialsFormMemKernelDifferential
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
namespace GlobalTheory.CompanionTheory.SW.RingDiag
open HeckeCharacterZeroLocus.SiegelWeilU
variable {A : Type} [CommRing A] {m : ℕ}
def bd (a : A) (M : Matrix (Fin m) (Fin m) A) : Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
  fun i j => Fin.cases (Fin.cases a (fun _ => 0) j)
    (fun i' => Fin.cases 0 (fun j' => M i' j') j) i
def uni (r : Fin m → A) : Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
  fun i j => Fin.cases (Fin.cases 1 r j)
    (fun i' => Fin.cases 0 (fun j' => (1 : Matrix (Fin m) (Fin m) A) i' j') j) i
def schur (K : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (b : A) : Matrix (Fin m) (Fin m) A :=
  fun i j => K i.succ j.succ - K i.succ 0 * b * K 0 j.succ
end GlobalTheory.CompanionTheory.SW.RingDiag


