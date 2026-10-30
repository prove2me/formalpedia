-- Prove2me | Definitions.Def_CubicTurning_unit_disk
-- name    : CubicTurning_unit_disk
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:20:55.795926+00:00
-- url     : https://prove2.me/theorems/87bdfba4-019d-41eb-ac04-4299e95ee261
-- title:
--   Unit-disk scaling of the sharp cubic root family
-- statement:
--   For every real $t$, let $a_t,b_t,c_t$ be the sharp-family roots. Define the unit-disk candidate roots by
--
--   $$\widehat a_t=\tfrac12a_t,\qquad\widehat b_t=\tfrac12b_t,\qquad\widehat c_t=\tfrac12c_t.$$
--
--   The definitions apply to every real parameter. For $0<t\le1$, the subsequent theorems prove that all three norms are at most one and their sum is zero. The critical radius is $1/2$ and the physical transverse parameter is $t/2$.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicUnitDiskSharpness.lean, lines 54-54, SHA-256 3486e16bcc09bab7538233bfe9db0c946150a8b63d7fd8e010d7b7e24a4c2a8b. The new Lean file is not present in the analytic source commit.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicUnitDiskSharpness.lean, lines 55-55, SHA-256 3486e16bcc09bab7538233bfe9db0c946150a8b63d7fd8e010d7b7e24a4c2a8b. The new Lean file is not present in the analytic source commit.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicUnitDiskSharpness.lean, lines 56-56, SHA-256 3486e16bcc09bab7538233bfe9db0c946150a8b63d7fd8e010d7b7e24a4c2a8b. The new Lean file is not present in the analytic source commit.

import Mathlib
import Definitions.Def_CubicTurning_finite_balanced
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning











noncomputable def unitDiskCentral (t : ℝ) : ℂ := (1/2:ℂ)*sharpCentral t
noncomputable def unitDiskOuterPlus (t : ℝ) : ℂ := (1/2:ℂ)*sharpOuterPlus t
noncomputable def unitDiskOuterMinus (t : ℝ) : ℂ := (1/2:ℂ)*sharpOuterMinus t




















end CubicTurning


