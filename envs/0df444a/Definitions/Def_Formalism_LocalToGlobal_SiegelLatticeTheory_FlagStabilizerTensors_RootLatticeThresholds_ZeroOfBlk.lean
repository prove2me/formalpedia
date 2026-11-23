-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ZeroOfBlk
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ZeroOfBlk
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:12.433797+00:00
-- url     : https://prove2.me/theorems/00f5d8ee-f27e-4efc-8ced-e040258e1852
-- title:
--   Zero Of Blk
-- statement:
--   Definitions and structural lemmas for Zero Of Blk, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ZeroOfBlk.lean

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
variable {m : ℕ}
def IsUB (blk : Fin m → ℕ) (C : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  (∀ i, C i i = 1) ∧ ∀ i j, C i j ≠ 0 → i ≤ j ∧ blk i = blk j
section Mono
variable (π : Fin m → Fin m) (hπ : ∀ a, π (π a) = a) (Z : Matrix (Fin m) (Fin m) ℂ)
  (hZ : ∀ c b, Z c b ≠ 0 ↔ c = π b)
include hπ hZ
def Zi : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun b c => if b = π c then (Z c b)⁻¹ else 0
end Mono
section Pair
variable {blk : Fin m → ℕ} (π : Fin m → Fin m) (hπ : ∀ a, π (π a) = a) (hblk : ∀ a, blk (π a) = blk a)
  (hanti : ∀ a b, blk a = blk b → a < b → π b < π a) (Z : Matrix (Fin m) (Fin m) ℂ)
  (hZ : ∀ c b, Z c b ≠ 0 ↔ c = π b)
include hπ hblk hanti hZ
end Pair
end Formalism.L2.S.L6.UnitaryStandardVectors


