-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IsomFixOfExpOf
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IsomFixOfExpOf
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T10:47:01.133799+00:00
-- url     : https://prove2.me/theorems/f7b0be67-0e7d-5e8b-9903-572b03eeb200
-- title:
--   Isom Fix Of Exp Of
-- statement:
--   Definitions and structural lemmas for Isom Fix Of Exp Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/IsomFixOfExpOf.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IncOInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.L2.SG.Pf.G8
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
def extU {U W : Submodule K V} (hUc : IsCompl U W) (g : W ≃ₗ[K] W) : V ≃ₗ[K] V :=
  ((Submodule.prodEquivOfIsCompl U W hUc).symm.trans ((LinearEquiv.refl K U).prodCongr g)).trans
    (Submodule.prodEquivOfIsCompl U W hUc)
end Formalism.L2.SG.Pf.G8


