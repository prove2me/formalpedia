-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixTransvectionDiagonalDecomposition
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixTransvectionDiagonalDecomposition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:01.092228+00:00
-- url     : https://prove2.me/theorems/66967a2a-c0a6-4336-94cf-8f3120b9b335
-- title:
--   Matrix Transvection Diagonal Decomposition
-- statement:
--   Definitions and structural lemmas for Matrix Transvection Diagonal Decomposition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixTransvectionDiagonalDecomposition.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
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
namespace GlobalTheory.CompanionTheory.SW.ArtinElem
variable {K K' : Type*} [CommRing K] [CommRing K'] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [DecidableEq M] {F : M → Type*} [∀ m, CommRing (F m)]
noncomputable def coord (e : K ≃+* ∀ m, F m) (m : M) : K →+* F m :=
  (Pi.evalRingHom F m).comp e.toRingHom
noncomputable def liftT (e : K ≃+* ∀ m, F m) (m : M) (t : TransvectionStruct ι (F m)) :
    TransvectionStruct ι K :=
  ⟨t.i, t.j, t.hij, e.symm (Pi.single m t.c)⟩
noncomputable def big (e : K ≃+* ∀ m, F m) (T : ∀ m, List (TransvectionStruct ι (F m))) (l : List M) :
    List (TransvectionStruct ι K) :=
  l.flatMap fun m => (T m).map (liftT e m)
end GlobalTheory.CompanionTheory.SW.ArtinElem
namespace GlobalTheory.CompanionTheory.SW
end GlobalTheory.CompanionTheory.SW


