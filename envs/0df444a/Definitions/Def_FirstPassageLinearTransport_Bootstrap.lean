-- Prove2me | Definitions.Def_FirstPassageLinearTransport_Bootstrap
-- name    : FirstPassageLinearTransport_Bootstrap
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:12:23.325321+00:00
-- url     : https://prove2.me/theorems/37c70312-7f67-4202-9a48-fdee1bb986da
-- title:
--   Bootstrap
-- statement:
--   Definitions and structural lemmas for Bootstrap, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
def bootstrapSet {r eta : ℝ} (p : StageSetup r eta) : ℕ → Set ℕ
  | 0 => extendedWindow p
  | R + 1 => firstPassagePullback p (bootstrapSet p R)
def bootstrapD (chi Dc : ℝ) (R : ℕ) : ℝ := Dc * chi ^ R
def bootstrapC {r eta : ℝ} (p : StageSetup r eta)
    (chi Dc : ℝ) : ℕ → ℝ
  | 0 => quadraticWindowGlobalConstant eta
  | R + 1 =>
      pullbackGlobalConstant p chi Dc * (bootstrapC p chi Dc R + 1) *
        (bootstrapD chi Dc R)⁻¹ ^ 2
def stageK {r eta : ℝ} (p : StageSetup r eta) : ℝ :=
  (2 : ℝ) ^ p.M0
def stageOrbit {r eta : ℝ} (p : StageSetup r eta) : ℕ → ℕ → ℕ
  | 0, n => n
  | R + 1, n => stageOrbit p R (stageMap p n)
def stageClock {r eta : ℝ} (p : StageSetup r eta) : ℕ → ℕ → ℕ
  | 0, _n => 0
  | R + 1, n => stageLength p n + stageClock p R (stageMap p n)
def bootstrapStageK {r eta : ℝ} (p : StageSetup r eta)
    (chi Dc : ℝ) : ℝ :=
  pullbackGlobalConstant p chi Dc + 2
def clockGeom (r : ℝ) : ℕ → ℝ
  | 0 => 0
  | R + 1 => 1 + r * clockGeom r R
end
end FirstPassageLinearTransport


