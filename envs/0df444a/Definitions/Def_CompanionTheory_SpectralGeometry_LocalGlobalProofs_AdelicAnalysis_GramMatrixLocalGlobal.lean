-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramMatrixLocalGlobal
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramMatrixLocalGlobal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:06.086343+00:00
-- url     : https://prove2.me/theorems/0575c2a5-899a-4025-afe5-53f1a7503c69
-- title:
--   Gram Matrix Local Global
-- statement:
--   Definitions and structural lemmas for Gram Matrix Local Global, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramMatrixLocalGlobal.lean

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
namespace GlobalTheory.CompanionTheory.SW.GramLocal
section Ring
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
abbrev bcE (E : Type) [Field E] [Algebra F E] (f : R →ₐ[F] S) : R ⊗[F] E →ₐ[F] S ⊗[F] E :=
  Algebra.TensorProduct.map f (AlgHom.id F E)
end Ring
section Adelic
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
end Adelic
end GlobalTheory.CompanionTheory.SW.GramLocal


