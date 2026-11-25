-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscIsoOfProj
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscIsoOfProj
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T10:04:01.531447+00:00
-- url     : https://prove2.me/theorems/b8f8145b-02f8-5909-82c8-e2ebad81b1e4
-- title:
--   Disc Iso Of Proj
-- statement:
--   Definitions and structural lemmas for Disc Iso Of Proj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscIsoOfProj.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SameGenusFix
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
namespace Formalism.L2.SG.Pf.G6
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def prO {X Y : Submodule K V} (hc : IsCompl X Y) : V →ₗ[𝓞 K] V :=
  (X.projection Y hc).restrictScalars (𝓞 K)
def toDisc (h : V →ₗ⋆[K] V →ₗ[K] K) {X Y : Submodule K V} (hc : IsCompl X Y) (L Λ : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (hP : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h X L)) :
    ↥Λ →ₗ[𝓞 K] DiscMod h X L 𝔭 :=
  Submodule.mkQ _ ∘ₗ LinearMap.codRestrict _ (prO hc ∘ₗ Λ.subtype) (fun x => hP x x.2)
end Formalism.L2.SG.Pf.G6


