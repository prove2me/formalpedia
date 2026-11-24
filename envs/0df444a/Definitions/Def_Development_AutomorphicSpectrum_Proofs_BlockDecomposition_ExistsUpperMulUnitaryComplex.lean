-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperMulUnitaryComplex
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperMulUnitaryComplex
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:36.026002+00:00
-- url     : https://prove2.me/theorems/74a61e81-1cbb-4e7f-a508-050416ed29d7
-- title:
--   Exists Upper Mul Unitary Complex
-- statement:
--   Definitions and structural lemmas for Exists Upper Mul Unitary Complex, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperMulUnitaryComplex.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
namespace GlobalTheory.CompanionTheory.Iwasawa
noncomputable abbrev evalMat {ι : Type} {n : ℕ} (w : ι) :
    Matrix (Fin n) (Fin n) (ι → ℂ) →+* Matrix (Fin n) (Fin n) ℂ :=
  (Pi.evalRingHom (fun _ : ι => ℂ) w).mapMatrix
end GlobalTheory.CompanionTheory.Iwasawa


