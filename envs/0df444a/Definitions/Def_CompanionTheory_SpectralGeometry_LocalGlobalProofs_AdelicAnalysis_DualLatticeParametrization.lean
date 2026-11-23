-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DualLatticeParametrization
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DualLatticeParametrization
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:35.163505+00:00
-- url     : https://prove2.me/theorems/37ebd791-b48a-42a4-a38d-e5f8571af702
-- title:
--   Dual Lattice Parametrization
-- statement:
--   Definitions and structural lemmas for Dual Lattice Parametrization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DualLatticeParametrization.lean

import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
namespace GlobalTheory.CompanionTheory.SW.ThW.DualLattice
noncomputable def ratBasis {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (b : Module.Basis κ ℤ (𝓞 F)) : Module.Basis κ ℚ F :=
  b.localizationLocalization ℚ (nonZeroDivisors ℤ) F
end GlobalTheory.CompanionTheory.SW.ThW.DualLattice


