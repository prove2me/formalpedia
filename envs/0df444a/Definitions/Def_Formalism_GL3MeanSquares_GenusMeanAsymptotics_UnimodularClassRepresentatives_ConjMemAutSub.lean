-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjMemAutSub
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjMemAutSub
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T07:15:03.243965+00:00
-- url     : https://prove2.me/theorems/97516c2a-2d3f-4559-bdc1-1924bb2b4b39
-- title:
--   Conj Mem Aut Sub
-- statement:
--   Definitions and structural lemmas for Conj Mem Aut Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjMemAutSub.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtHomInjective
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsGlobalOfFibLocNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomMapOfEq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_IsStep_change
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
@[reducible] def actV (S : VecSplit h h') : MulAction (Formalism.HermitianLatticesTheory.isom h') (Submodule (𝓞 K) V) where
  smul g M := Formalism.HermitianLatticesTheory.gmap (extHom S g.1) M
  one_smul M := by
    change Formalism.HermitianLatticesTheory.gmap (extHom S 1) M = M
    rw [map_one]
    exact autSub_gmap_one M
  mul_smul a b M := by
    change Formalism.HermitianLatticesTheory.gmap (extHom S (a.1 * b.1)) M = _
    rw [map_mul]
    exact autSub_gmap_mul _ _ _
@[reducible] def actV' (h' : V' →ₗ⋆[K] V' →ₗ[K] K) :
    MulAction (Formalism.HermitianLatticesTheory.isom h') (Submodule (𝓞 K) V') where
  smul g T := Formalism.HermitianLatticesTheory.gmap g.1 T
  one_smul T := autSub_gmap_one T
  mul_smul _ _ _ := autSub_gmap_mul _ _ _
end Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF


