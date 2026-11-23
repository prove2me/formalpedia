-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryFiniteSetDecomposition
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryFiniteSetDecomposition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:49.089706+00:00
-- url     : https://prove2.me/theorems/9540627a-9032-43ec-a002-65ccdb8b5dd3
-- title:
--   Adelic Unitary Finite Set Decomposition
-- statement:
--   Definitions and structural lemmas for Adelic Unitary Finite Set Decomposition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryFiniteSetDecomposition.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere
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
namespace GlobalTheory.CompanionTheory.SW.PureH
section Glob
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
end Glob
end GlobalTheory.CompanionTheory.SW.PureH
namespace GlobalTheory.CompanionTheory.SW.PureH
section Core
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  [DecidableEq (HeightOneSpectrum (𝓞 F))]
variable {d M : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E)
  (Jp : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (h : HA (AF F) σ Jp) (ginf : HA (Ainf F) σ Jp)
  (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ Jp) (S Sh : Finset (HeightOneSpectrum (𝓞 F)))
end Core
end GlobalTheory.CompanionTheory.SW.PureH


