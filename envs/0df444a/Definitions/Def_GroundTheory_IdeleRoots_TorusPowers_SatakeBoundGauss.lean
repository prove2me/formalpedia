-- Prove2me | Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_SatakeBoundGauss
-- name    : GroundTheory_IdeleRoots_TorusPowers_SatakeBoundGauss
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:13.231042+00:00
-- url     : https://prove2.me/theorems/c24275f6-0c7d-45ee-83be-80b8dd2e609b
-- title:
--   Satake Bound Gauss
-- statement:
--   Definitions and structural lemmas for Satake Bound Gauss, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/SatakeBoundGauss.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.BlockD
namespace SatakeBound
open Finset
def gauss (q : ℝ) (N k : ℕ) : ℝ :=
  (∏ j ∈ range k, (q ^ (N - j) - 1)) / ∏ j ∈ range k, (q ^ (j + 1) - 1)
variable {q : ℝ}
def wt (N : ℕ) (S : Finset (Fin N)) : ℕ := ∑ i ∈ S, (N - 1 - (i : ℕ))
def pw (q : ℝ) (N : ℕ) (S : Finset (Fin N)) : ℝ := q ^ wt N S / q ^ S.card.choose 2
end SatakeBound
end GroundTheory.BlockD


