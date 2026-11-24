-- Prove2me | Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
-- name    : Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:26:34.000802+00:00
-- url     : https://prove2.me/theorems/acaf8590-3be0-4f03-8577-d3e5df954652
-- title:
--   Exists Unit Norm
-- statement:
--   Definitions and structural lemmas for Exists Unit Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/ExistsUnitNorm.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def InJ (p : Ideal (𝓞 K)) (a : K) : Prop :=
  ∃ r s : 𝓞 K, s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p ∧ r ∈ p ∧ r ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p ∧
    a = algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s
variable {V : Type} [AddCommGroup V] [Module K V]
end Formalism.L2.SG.Pf.LatDictZ.Z0.SGA


