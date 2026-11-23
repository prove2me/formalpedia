-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVector
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVector
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:54.999114+00:00
-- url     : https://prove2.me/theorems/f3402ffb-c79f-40da-abeb-8283864e941b
-- title:
--   Similitude Definite Form Is Algebraic On Vector
-- statement:
--   Definitions and structural lemmas for Similitude Definite Form Is Algebraic On Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SimilitudeDefiniteFormIsAlgebraicOnVector.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
namespace GlobalTheory.SimAlg
noncomputable def form (g : ℕ → ℕ → ℤ) : ℂ[X] →ₗ[ℂ] ℂ[X] →ₗ[ℂ] ℂ :=
  (basisMonomials ℂ).constr ℂ fun i => (basisMonomials ℂ).constr ℂ fun j => (g i j : ℂ)
end GlobalTheory.SimAlg


