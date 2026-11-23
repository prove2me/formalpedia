-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RankUpdateMul
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RankUpdateMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:34.53381+00:00
-- url     : https://prove2.me/theorems/b590429d-828b-4090-b7bf-99c02edb80ad
-- title:
--   Rank Update Mul
-- statement:
--   Definitions and structural lemmas for Rank Update Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RankUpdateMul.lean

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
open Matrix
namespace Formalism.L2.S.L6.UnitaryStandardVectors
variable {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι] [DecidableEq ι]
def Ymat (J : Matrix n n ℂ) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ) : Matrix n n ℂ :=
  1 + W * M * (Wᴴ * J * W)⁻¹ * Wᴴ * J
end Formalism.L2.S.L6.UnitaryStandardVectors


