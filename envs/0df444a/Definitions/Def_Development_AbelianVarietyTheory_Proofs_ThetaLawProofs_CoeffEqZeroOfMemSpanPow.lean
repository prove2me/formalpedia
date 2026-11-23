-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:35.267932+00:00
-- url     : https://prove2.me/theorems/50c64bb3-6df3-41e0-bb14-ca124c126d2b
-- title:
--   Coeff Eq Zero Of Mem Span Pow
-- statement:
--   Definitions and structural lemmas for Coeff Eq Zero Of Mem Span Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CoeffEqZeroOfMemSpanPow.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.SocleDet
open Matrix
section General
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
end General
section PowerSeries
open MvPowerSeries
variable {k : Type*} [CommRing k] {σ : Type*}
end PowerSeries
end GlobalTheory.SocleDet


