-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousScale
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousScale
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:09.880709+00:00
-- url     : https://prove2.me/theorems/f89e1a41-82ab-4f9b-98ef-967fcfbc4518
-- title:
--   Exists Continuous Scale
-- statement:
--   Definitions and structural lemmas for Exists Continuous Scale, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsContinuousScale.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensor
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
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
namespace GlobalTheory.CompanionTheory.SW.HaarScale
variable {V P : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [LocallyCompactSpace V] [T2Space V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace P] [LocallyCompactSpace P]
def addEquivOf (T Ti : V → V) (hadd : ∀ x y, T (x + y) = T x + T y)
    (hl : ∀ x, Ti (T x) = x) (hr : ∀ x, T (Ti x) = x) : V ≃+ V where
  toFun := T
  invFun := Ti
  left_inv := hl
  right_inv := hr
  map_add' := hadd
end GlobalTheory.CompanionTheory.SW.HaarScale
namespace GlobalTheory.CompanionTheory.SW.HaarScale
section Mat
variable {K : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}
end Mat
section Tup
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
end Tup
section Herm
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
def conjT (σ : E →ₐ[F] E) {n : ℕ} (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (g.map (sigR R σ))ᵀ
end Herm
section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Main
end GlobalTheory.CompanionTheory.SW.HaarScale


