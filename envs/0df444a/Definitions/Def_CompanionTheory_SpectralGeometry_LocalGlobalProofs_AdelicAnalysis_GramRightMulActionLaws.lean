-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightMulActionLaws
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightMulActionLaws
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:07.270935+00:00
-- url     : https://prove2.me/theorems/e2096451-2c1f-4deb-819a-28224838ed5b
-- title:
--   Gram Right Mul Action Laws
-- statement:
--   Definitions and structural lemmas for Gram Right Mul Action Laws, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramRightMulActionLaws.lean

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
namespace GlobalTheory.CompanionTheory.SW.RMulGram
section
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
def colsM {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : Matrix (Fin M) (Fin n) (R ⊗[F] E) :=
  fun i a => X a i
end
end GlobalTheory.CompanionTheory.SW.RMulGram


