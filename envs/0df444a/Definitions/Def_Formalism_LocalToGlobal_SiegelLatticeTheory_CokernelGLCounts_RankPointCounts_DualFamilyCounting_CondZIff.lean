-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CondZIff
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CondZIff
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:19.215868+00:00
-- url     : https://prove2.me/theorems/5bbb4887-1b4d-4cbc-b8cf-faecb888bd73
-- title:
--   Cond ZIff
-- statement:
--   Definitions and structural lemmas for Cond ZIff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CondZIff.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DivMulMemSPOfSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
namespace Formalism.L2.SG.Pf.fibreCountingData
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
section
variable {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsMaximal] {k : ℕ}
local notation "mk" => Ideal.Quotient.mk (extP K 𝔭 ^ k)
variable {m : ℕ} (a : Fin m → 𝓞 F)
def gramO (Y : Matrix (Fin m) (Fin m) (𝓞 K)) : Matrix (Fin m) (Fin m) (𝓞 K) :=
  Yᴴ * diagonal (fun i => ι (a i)) * Y - diagonal (fun i => ι (a i))
variable {a}
end
end Formalism.L2.SG.Pf.fibreCountingData


