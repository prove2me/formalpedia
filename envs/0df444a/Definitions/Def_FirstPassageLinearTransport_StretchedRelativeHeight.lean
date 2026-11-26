-- Prove2me | Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
-- name    : FirstPassageLinearTransport_StretchedRelativeHeight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:18:14.324027+00:00
-- url     : https://prove2.me/theorems/c9992c08-7de0-5cc8-80d3-1023cf9f3ee5
-- title:
--   Stretched Relative Height
-- statement:
--   Definitions and structural lemmas for Stretched Relative Height, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
def stretchedHeightShellAllowance (zeta alpha : ℝ) (M : ℕ) : ℝ :=
  Real.exp (zeta * (((M : ℝ) * Real.log 2) ^ alpha))
def heightCertifiedShell
    {r eta : ℝ} (p : StageSetup r eta)
    (omega zeta alpha : ℝ) (M : ℕ) : Set ℕ :=
  shellBootstrap p omega M ∩
    {n | n ∉ shellMultiplicativeHit M
      (stretchedHeightShellAllowance zeta alpha M / 4)}
def assembledHeightCertified
    {r eta : ℝ} (p : StageSetup r eta)
    (omega zeta alpha : ℝ) : Set ℕ :=
  assembleDyadic (heightCertifiedShell p omega zeta alpha)
end
end FirstPassageLinearTransport


