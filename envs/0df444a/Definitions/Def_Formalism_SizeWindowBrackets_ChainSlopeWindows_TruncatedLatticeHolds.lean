-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
-- name    : Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:58.126644+00:00
-- url     : https://prove2.me/theorems/28fec212-fad5-42d6-ac69-aaa064a16cc7
-- title:
--   Truncated Lattice Holds
-- statement:
--   Definitions and structural lemmas for Truncated Lattice Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/TruncatedLatticeHolds.lean

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
namespace Formalism.LFunctionChainParameters.LLcv
open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData
section Loc
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
def pLen (p : Ideal R) [p.IsPrime] (A B : Submodule R W) : ℕ∞ :=
  Module.length R ((localization₂ p A) ⧸ (localization₂ p B).comap (localization₂ p A).subtype)
end Loc
section Span
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end Span
section Main
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
end Main
section Mod
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K
end Mod
section BaseChange
open scoped Matrix
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
end BaseChange
end Formalism.LFunctionChainParameters.LLcv


