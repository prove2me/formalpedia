-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthLocalizedModuleEqZeroOfNotAnnihilatorLe
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthLocalizedModuleEqZeroOfNotAnnihilatorLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:11.698938+00:00
-- url     : https://prove2.me/theorems/ef37b60f-829e-44ff-b476-45f6a3d8f524
-- title:
--   Length Localized Module Eq Zero Of Not Annihilator Le
-- statement:
--   Definitions and structural lemmas for Length Localized Module Eq Zero Of Not Annihilator Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthLocalizedModuleEqZeroOfNotAnnihilatorLe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain Function
namespace GlobalTheory
section General
variable {R : Type*} [CommRing R]
section Submodules
variable (T : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization T S]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]
end Submodules
end General
section Dedekind
variable {O : Type*} [CommRing O] [IsDedekindDomain O]
section Torsion
variable {X : Type*} [AddCommGroup X] [Module O X] [Module.Finite O X]
variable [Ring.HasFiniteQuotients O]
variable [Module.Free ℤ O]
end Torsion
section Lattices
variable [Ring.HasFiniteQuotients O] [Module.Free ℤ O]
end Lattices
end Dedekind
end GlobalTheory


