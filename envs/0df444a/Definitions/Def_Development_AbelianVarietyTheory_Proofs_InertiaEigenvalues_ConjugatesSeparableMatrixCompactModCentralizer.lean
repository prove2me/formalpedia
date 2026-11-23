-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjugatesSeparableMatrixCompactModCentralizer
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjugatesSeparableMatrixCompactModCentralizer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:50.041498+00:00
-- url     : https://prove2.me/theorems/fc86e316-5bd3-4b11-a709-75bf170ed272
-- title:
--   Conjugates Separable Matrix Compact Mod Centralizer
-- statement:
--   Definitions and structural lemmas for Conjugates Separable Matrix Compact Mod Centralizer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ConjugatesSeparableMatrixCompactModCentralizer.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactPreimageNormCentralizerHermitianStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology Polynomial
noncomputable section
namespace GlobalTheory.OrbCpt
variable {k : Type} [NontriviallyNormedField k] {r : ℕ}
noncomputable def gsum (X Y : Matrix (Fin r) (Fin r) k) : ℕ → Matrix (Fin r) (Fin r) k
  | 0 => 0
  | m + 1 => X ^ m + gsum X Y m * Y
def hm (p : k[X]) (X Y : Matrix (Fin r) (Fin r) k) : Matrix (Fin r) (Fin r) k :=
  ∑ m ∈ Finset.range (p.natDegree + 2), p.coeff m • gsum X Y m
end GlobalTheory.OrbCpt
noncomputable section
namespace GlobalTheory.OrbCpt
variable {k : Type} [NontriviallyNormedField k] {r : ℕ}
end GlobalTheory.OrbCpt
noncomputable section
namespace GlobalTheory.OrbCpt
end GlobalTheory.OrbCpt
namespace GlobalTheory.OrbCpt
end GlobalTheory.OrbCpt


