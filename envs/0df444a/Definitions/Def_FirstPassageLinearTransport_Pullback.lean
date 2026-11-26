-- Prove2me | Definitions.Def_FirstPassageLinearTransport_Pullback
-- name    : FirstPassageLinearTransport_Pullback
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:03:52.438729+00:00
-- url     : https://prove2.me/theorems/37d3cb24-f623-4596-8831-583c16b97e19
-- title:
--   Pullback
-- statement:
--   Definitions and structural lemmas for Pullback, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped Real
noncomputable section
noncomputable def targetScale (r : ℝ) (M : ℕ) : ℕ :=
  2 ^ ⌊r * M⌋₊
structure StageSetup (r eta : ℝ) where
  M0 : ℕ
  r_pos : 0 < r
  r_lt_one : r < 1
  eta_pos : 0 < eta
  eta_le_one : eta ≤ 1
  target_one_lt : ∀ M, M0 ≤ M → 1 < targetScale r M
  target_lt_shell : ∀ M, M0 ≤ M → targetScale r M < 2 ^ M
  horizon_small : ∀ M, M0 ≤ M →
    (M : ℚ) / (2 * (targetScale r M : ℚ)) ≤ 1 / 3
  terminal_budget : ∀ M, M0 ≤ M →
    centralOrbitScale M * ((2 : ℝ) ^ (M + 1)) ^ (1 + eta) ≤
      targetScale r M
noncomputable def boundedFirstPassage (Y H n : ℕ) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, k ≤ H ∧ orbit k n ≤ Y then Nat.find h else 0
noncomputable def stageLength {r eta : ℝ} (p : StageSetup r eta)
    (n : ℕ) : ℕ :=
  if p.M0 ≤ Nat.log 2 n then
    boundedFirstPassage (targetScale r (Nat.log 2 n)) (Nat.log 2 n) n
  else 0
noncomputable def stageMap {r eta : ℝ} (p : StageSetup r eta)
    (n : ℕ) : ℕ :=
  orbit (stageLength p n) n
def extendedWindow {r eta : ℝ} (p : StageSetup r eta) : Set ℕ :=
  initialWindowGood eta ∪ {n | n < 2 ^ p.M0}
def firstPassagePullback {r eta : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) : Set ℕ :=
  extendedWindow p ∩ stageMap p ⁻¹' S
noncomputable def badTarget (S : Set ℕ) (Y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 Y).filter (fun y => y ∉ S)
def transportGap (r chi : ℝ) : ℝ := (r - chi) * Real.log 2
def pullbackShellConstant {r eta : ℝ} (p : StageSetup r eta)
    (chi Dc : ℝ) : ℝ :=
  Real.exp (chi * Dc * Real.log 2 * p.M0) +
    2 * quadraticWindowGlobalConstant eta +
    20 / transportGap r chi ^ 2
def pullbackGlobalConstant {r eta : ℝ} (p : StageSetup r eta)
    (chi Dc : ℝ) : ℝ :=
  2 * pullbackShellConstant p chi Dc /
    (2 * Real.exp (-(chi * Dc * Real.log 2)) - 1)
end
end FirstPassageLinearTransport


