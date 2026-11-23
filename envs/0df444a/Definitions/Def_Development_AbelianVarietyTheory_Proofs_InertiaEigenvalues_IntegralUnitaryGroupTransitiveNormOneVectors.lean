-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralUnitaryGroupTransitiveNormOneVectors
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralUnitaryGroupTransitiveNormOneVectors
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:49.810629+00:00
-- url     : https://prove2.me/theorems/93588dc3-e9da-4b25-a609-a7a1ef29fabd
-- title:
--   Integral Unitary Group Transitive Norm One Vectors
-- statement:
--   Definitions and structural lemmas for Integral Unitary Group Transitive Norm One Vectors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralUnitaryGroupTransitiveNormOneVectors.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.UnitaryTransitive
variable {E : Type} [NormedField E] [StarRing E]
def ext0 {r : ℕ} (x : Fin r → E) : Fin (r + 1) → E := Fin.snoc (α := fun _ => E) x 0
end GlobalTheory.UnitaryTransitive
namespace GlobalTheory.UnitaryTransitive
variable {E : Type} [Field E] [StarRing E]
end GlobalTheory.UnitaryTransitive
namespace GlobalTheory.UnitaryTransitive
end GlobalTheory.UnitaryTransitive
namespace GlobalTheory.UnitaryTransitive
end GlobalTheory.UnitaryTransitive


