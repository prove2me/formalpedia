-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannZetaNeZeroOfMemIoo
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannZetaNeZeroOfMemIoo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:10.785129+00:00
-- url     : https://prove2.me/theorems/d59075b2-821c-436c-a616-0a8e736457e9
-- title:
--   Riemann Zeta Ne Zero Of Mem Ioo
-- statement:
--   Definitions and structural lemmas for Riemann Zeta Ne Zero Of Mem Ioo, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannZetaNeZeroOfMemIoo.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
namespace GlobalTheory.RealZeros
noncomputable def br (N c d k : ℕ) (s : ℂ) : ℂ :=
  ((N * k + c : ℕ) : ℂ) ^ (-s) - ((N * k + d : ℕ) : ℂ) ^ (-s)
end GlobalTheory.RealZeros


