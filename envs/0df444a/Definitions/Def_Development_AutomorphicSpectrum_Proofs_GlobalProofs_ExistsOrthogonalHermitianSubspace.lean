-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExistsOrthogonalHermitianSubspace
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExistsOrthogonalHermitianSubspace
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T12:39:41.419934+00:00
-- url     : https://prove2.me/theorems/8cce3c2d-eb10-4a75-9cf5-553c57738cb3
-- title:
--   Exists Orthogonal Hermitian Subspace
-- statement:
--   Definitions and structural lemmas for Exists Orthogonal Hermitian Subspace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExistsOrthogonalHermitianSubspace.lean

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace GlobalTheory.CompanionTheory.JStable
variable {n : ℕ} (ε : Fin n → Bool)
def ext0 (s : Bool) : EuclideanSpace ℂ {i : Fin n // ε i = s} →ₗ[ℂ] (Fin n → ℂ) where
  toFun x a := if h : ε a = s then x ⟨a, h⟩ else 0
  map_add' x y := by
    funext a
    by_cases h : ε a = s <;> simp [h]
  map_smul' c x := by
    funext a
    by_cases h : ε a = s <;> simp [h]
def res0 (s : Bool) (v : Fin n → ℂ) : EuclideanSpace ℂ {i : Fin n // ε i = s} :=
  WithLp.toLp 2 fun i => v i
end GlobalTheory.CompanionTheory.JStable


