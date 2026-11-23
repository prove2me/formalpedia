-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralOrInvIsIntegralFiniteExtUltrametric
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralOrInvIsIntegralFiniteExtUltrametric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:10.26104+00:00
-- url     : https://prove2.me/theorems/3a754250-c2a1-49f3-bfd0-c67368b89f41
-- title:
--   Is Integral Or Inv Is Integral Finite Ext Ultrametric
-- statement:
--   Definitions and structural lemmas for Is Integral Or Inv Is Integral Finite Ext Ultrametric, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralOrInvIsIntegralFiniteExtUltrametric.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open Polynomial
noncomputable section
namespace GlobalTheory.JR.Spec
variable {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F]
  {k : Type} [Field k] [Algebra F k]
end GlobalTheory.JR.Spec


