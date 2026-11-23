-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzPolyMulGauss
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzPolyMulGauss
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:18.338665+00:00
-- url     : https://prove2.me/theorems/d3b612d6-7366-43e3-bc5c-608466cfda0f
-- title:
--   Exists Schwartz Poly Mul Gauss
-- statement:
--   Definitions and structural lemmas for Exists Schwartz Poly Mul Gauss, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSchwartzPolyMulGauss.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.PolyGaussSchwartz
variable {m n : ℕ}
def coord (k : Fin m × Fin n × Bool) (u : Fin m → Fin n → ℂ) : ℂ :=
  if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1
def entryL (a : Fin m) (i : Fin n) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a)
def toEuclid (m n : ℕ) : (Fin m → Fin n → ℂ) ≃L[ℝ] PiLp 2 (fun _ : Fin m × Fin n => ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    (((LinearEquiv.curry ℝ ℂ (Fin m) (Fin n)).symm.trans
      (WithLp.linearEquiv 2 ℝ (Fin m × Fin n → ℂ)).symm).trans
      (LinearEquiv.smulOfNeZero ℝ _ (√2) (by positivity)))
end GlobalTheory.CompanionTheory.PolyGaussSchwartz


