-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:14.862643+00:00
-- url     : https://prove2.me/theorems/94b0ce59-08da-489c-aab8-810bdacfda5f
-- title:
--   Coordinate Haar Measure
-- statement:
--   Definitions and structural lemmas for Coordinate Haar Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateHaarMeasure.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
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
namespace GlobalTheory.CompanionTheory.SW.HaarCoord
section Alg
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
end Alg
section Herm
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
def hermMat (σ : E →ₐ[F] E) (n : ℕ) (x : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) := fun a b =>
  if h : a < b then x.2 ⟨(a, b), h⟩
  else if h' : b < a then sigR R σ (x.2 ⟨(b, a), h'⟩)
  else x.1 a ⊗ₜ[F] (1 : E)
variable [TopologicalSpace R]
def hermCoord (σ : E →ₐ[F] E) (n : ℕ) (S : HermR R σ n) :
    (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) :=
  ((fun i : Fin n => algebraMap F R (1 / 2) *
      Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i i)),
    (fun p : {p : Fin n × Fin n // p.1 < p.2} => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) p.1.1 p.1.2))
end Herm
end GlobalTheory.CompanionTheory.SW.HaarCoord
namespace GlobalTheory.CompanionTheory.SW
end GlobalTheory.CompanionTheory.SW


