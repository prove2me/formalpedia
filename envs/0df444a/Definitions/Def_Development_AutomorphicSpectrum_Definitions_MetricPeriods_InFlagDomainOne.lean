-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_InFlagDomainOne
-- name    : Development_AutomorphicSpectrum_Definitions_MetricPeriods_InFlagDomainOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:20:04.432825+00:00
-- url     : https://prove2.me/theorems/4bac441d-ffbe-4e5a-9b7d-705479077eb5
-- title:
--   In Flag Domain One
-- statement:
--   Definitions and structural lemmas for In Flag Domain One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/InFlagDomainOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB
open Matrix
open scoped ComplexOrder
def gramOf {N : ℕ} (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  gᴴ * diagonal (fun i => (hd i : ℂ)) * g
def gramHead {N : ℕ} (hd : Fin N → ℝ) (k : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) :
    Matrix {a : Fin N // (a : ℕ) < k} {a : Fin N // (a : ℕ) < k} ℂ :=
  (gramOf hd g).submatrix Subtype.val Subtype.val
def gramLog {N : ℕ} (hd : Fin N → ℝ) (k : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (1 / 2) * Real.log ‖(gramHead hd k g).det‖
def sigForm (N j : ℕ) : Fin N → ℝ := fun a => if (a : ℕ) < N - j then -1 else 1
def InFlagDomain (N j : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsUnit g.det ∧ (-gramHead (sigForm N j) (N - j) g).PosDef
def stepPot (N j : ℕ) (i : Fin N) (g : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  if (i : ℕ) + 1 ≤ j then gramLog (sigForm N j) (N - j + ((i : ℕ) + 1)) g - gramLog (sigForm N j) (N - j) g
  else gramLog (sigForm N j) N g - gramLog (sigForm N j) (N - j) g + gramLog (sigForm N j) ((i : ℕ) + 1 - j) g
def herm2 (G : Matrix (Fin 2) (Fin 2) ℂ) (u w : Fin 2 → ℂ) : ℂ := star u ⬝ᵥ (G *ᵥ w)
def xiPot (G : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) : ℝ :=
  -Real.log (herm2 G ![1, a] ![1, a]).re + (1 / 2) * Real.log G.det.re
def logSin (G : Matrix (Fin 2) (Fin 2) ℂ) (a₀ a₁ : ℂ) : ℝ :=
  (1 / 2) * Real.log (1 - ‖herm2 G ![1, a₀] ![1, a₁]‖ ^ 2 /
    ((herm2 G ![1, a₀] ![1, a₀]).re * (herm2 G ![1, a₁] ![1, a₁]).re))
end GlobalTheory.CompanionTheory.Ar.PB


