-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LocalizationStructureHolds
-- name    : Formalism_SizeWindowBrackets_ChainSlopeWindows_LocalizationStructureHolds
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:46:49.44777+00:00
-- url     : https://prove2.me/theorems/8d76b516-8c01-46c2-b512-88cef411feb5
-- title:
--   Localization Structure Holds
-- statement:
--   Definitions and structural lemmas for Localization Structure Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/LocalizationStructureHolds.lean

import Definitions.Def_Formalism_SizeWindowBrackets_JointCSlopeExists
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_IntersectionFailsForSubmodule
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChainLatticeSizesModelEventually
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Pointwise
noncomputable section
namespace Formalism.LFunctionChainParameters.LJC
open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData Formalism.LFunctionChainParameters.DiagonalSublatticeLength
section Str
variable {K : Type} [Field K] [NumberField K]
end Str
section Glob
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
end Glob
section Loc
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
end Loc
section Joint
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
end Joint
section Smith
variable {R : Type} [CommRing R] [IsDomain R]
variable {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
variable {W : Type} [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
end Smith
section Smith2
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
end Smith2
section Slope
end Slope
section Local
end Local
section Fam
variable {K V V₂ : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V₂] [Module K V₂] [Module (𝓞 K) V₂]
  [IsScalarTower (𝓞 K) K V₂]
end Fam
section More
end More
section Prim
end Prim
section Real
variable {ι κ : Type*} [DecidableEq ι]
end Real
section Tests
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
end Tests
end Formalism.LFunctionChainParameters.LJC


