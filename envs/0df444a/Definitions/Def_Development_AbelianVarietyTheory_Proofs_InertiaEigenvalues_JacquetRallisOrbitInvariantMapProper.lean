-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProper
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProper
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:49.124413+00:00
-- url     : https://prove2.me/theorems/5a8b768f-0afc-48bc-a2e0-0bef6cb4d162
-- title:
--   Jacquet Rallis Orbit Invariant Map Proper
-- statement:
--   Definitions and structural lemmas for Jacquet Rallis Orbit Invariant Map Proper, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitInvariantMapProper.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.JR.OrbitProper
section Alg
variable {r : ℕ} {k : Type} [CommRing k]
end Alg
section Top
variable {r : ℕ} {F : Type} [NontriviallyNormedField F]
end Top
section Cpt
variable {r : ℕ} {F : Type} [NontriviallyNormedField F]
end Cpt
end GlobalTheory.JR.OrbitProper


