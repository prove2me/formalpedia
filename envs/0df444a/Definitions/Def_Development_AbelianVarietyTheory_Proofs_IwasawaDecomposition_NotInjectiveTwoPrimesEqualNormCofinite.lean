-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NotInjectiveTwoPrimesEqualNormCofinite
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NotInjectiveTwoPrimesEqualNormCofinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:45.179031+00:00
-- url     : https://prove2.me/theorems/25df1d20-f061-4ee5-9154-236ad3e917cb
-- title:
--   Not Injective Two Primes Equal Norm Cofinite
-- statement:
--   Definitions and structural lemmas for Not Injective Two Primes Equal Norm Cofinite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NotInjectiveTwoPrimesEqualNormCofinite.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealMulAbsNormCpowEqExpTsum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter Topology
namespace GlobalTheory.Mem.ZetaPole
noncomputable def logFactor (n : ℕ) (s : ℝ) : ℝ := -Real.log (1 - (n : ℝ) ^ (-s))
end GlobalTheory.Mem.ZetaPole


