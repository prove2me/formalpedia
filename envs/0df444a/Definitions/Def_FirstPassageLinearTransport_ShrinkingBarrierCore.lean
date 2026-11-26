-- Prove2me | Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
-- name    : FirstPassageLinearTransport_ShrinkingBarrierCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:05:01.27284+00:00
-- url     : https://prove2.me/theorems/5c877f82-a15c-5597-9e30-189f91fa36ee
-- title:
--   Shrinking Barrier Core
-- statement:
--   Definitions and structural lemmas for Shrinking Barrier Core, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingBarrierCore.lean

import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Theorems.Thm_FirstPassageLinearTransport_centralOrbitScale_pos

set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped Real
noncomputable section
def StageSetup.lowerTolerance
    {r eta : ℝ} (p : StageSetup r eta) (t : ℝ)
    (ht0 : 0 < t) (hteta : t ≤ eta) : StageSetup r t where
  M0 := p.M0
  r_pos := p.r_pos
  r_lt_one := p.r_lt_one
  eta_pos := ht0
  eta_le_one := hteta.trans p.eta_le_one
  target_one_lt := p.target_one_lt
  target_lt_shell := p.target_lt_shell
  horizon_small := p.horizon_small
  terminal_budget := by
    intro M hM
    have hbase : (1 : ℝ) ≤ (2 : ℝ) ^ (M + 1) :=
      one_le_pow₀ (by norm_num)
    have hpow :
        ((2 : ℝ) ^ (M + 1)) ^ (1 + t) ≤
          ((2 : ℝ) ^ (M + 1)) ^ (1 + eta) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    exact (mul_le_mul_of_nonneg_left hpow (centralOrbitScale_pos M).le).trans
      (p.terminal_budget M hM)
end
end FirstPassageLinearTransport


