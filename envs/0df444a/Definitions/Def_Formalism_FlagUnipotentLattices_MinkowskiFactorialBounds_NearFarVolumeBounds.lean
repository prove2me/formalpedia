-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:16.737841+00:00
-- url     : https://prove2.me/theorems/03fbfc59-7c87-44fe-9586-dab2fb88ec04
-- title:
--   Near Far Volume Bounds
-- statement:
--   Definitions and structural lemmas for Near Far Volume Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/NearFarVolumeBounds.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder
namespace Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open scoped ENNReal
section Dedekind
open Ideal UniqueFactorizationMonoid
variable {K : Type} [Field K] [NumberField K]
noncomputable def normWeight_b (K : Type) [Field K] [NumberField K] (i : ℕ) : Ideal (𝓞 K) →* ℝ where
  toFun I := ((absNorm I : ℝ)⁻¹) ^ i
  map_one' := by simp
  map_mul' I J := by
    rw [map_mul, Nat.cast_mul, mul_inv, mul_pow]
end Dedekind
end Formalism.HermitianLatticeCounting.P


