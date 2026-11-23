-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdeleHaarMapEqScaledVolume
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdeleHaarMapEqScaledVolume
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:50.215792+00:00
-- url     : https://prove2.me/theorems/9bc06771-97d9-4a13-84be-0c2de5445899
-- title:
--   Infinite Adele Haar Map Eq Scaled Volume
-- statement:
--   Definitions and structural lemmas for Infinite Adele Haar Map Eq Scaled Volume, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteAdeleHaarMapEqScaledVolume.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.RealCoord
open InfinitePlace InfinitePlace.Completion
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
def rho (w : InfinitePlace F) : F →+* ℝ := embedding_of_isReal (IsTotallyReal.isReal w)
def coord : Ainf F ≃+* (InfinitePlace F → ℝ) :=
  RingEquiv.piCongrRight (R := fun w : InfinitePlace F => w.Completion) (S := fun _ => ℝ)
    (fun w => ringEquivRealOfIsReal (IsTotallyReal.isReal w))
def coordHomeo : Ainf F ≃ₜ (InfinitePlace F → ℝ) :=
  Homeomorph.piCongrRight (Y₁ := fun w : InfinitePlace F => w.Completion) (Y₂ := fun _ => ℝ)
    (fun w => (isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).toHomeomorph)
instance : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
  ⟨fun w => not_isReal_iff_isComplex.mpr w.2 (IsTotallyReal.isReal w.1)⟩
def toMixed (y : InfinitePlace F → ℝ) : mixedEmbedding.mixedSpace F :=
  (fun w => y w.1, 0)
end GlobalTheory.CompanionTheory.SW.RealCoord


