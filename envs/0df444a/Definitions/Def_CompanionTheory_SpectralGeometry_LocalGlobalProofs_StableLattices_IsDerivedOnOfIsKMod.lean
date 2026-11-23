-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsDerivedOnOfIsKMod
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsDerivedOnOfIsKMod
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:25:58.443074+00:00
-- url     : https://prove2.me/theorems/0110dc35-9cc5-4829-b707-8099b8e76238
-- title:
--   Is Derived On Of Is KMod
-- statement:
--   Definitions and structural lemmas for Is Derived On Of Is KMod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsDerivedOnOfIsKMod.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Theorems.Thm_CompanionTheory_D_LK_cyc_stab
import Theorems.Thm_CompanionTheory_D_LK_mem_cyc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset WithLp
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.CompanionTheory.DSUniq
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight Cas)
open PI.UpqRep (lowK IsURepOn IsIrredOn UJset IsDS)
open CompanionTheory.D.DSIC (KUnit KStab)
open CompanionTheory.D.LK (Cyc LocFin IsMin IsKMod MultAlg KModExists OrthCyc mem_cyc cyc_stab ev)
open ReciprocityTheory.ChartRestriction.DS (genSub IsDerivedOn)
open ReciprocityTheory.ChartRestriction.DS.USum (sD sE sσ ofP toP lift)
variable {n : ℕ}
section Alg
variable {V : Type} [AddCommGroup V] [Module ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
end Alg
section Unit
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
  {ε : Fin n → Bool}
end Unit
section Sum
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {D : Submodule ℂ H} {D' : Submodule ℂ H'} {E : Fin n → Fin n → Module.End ℂ D}
  {E' : Fin n → Fin n → Module.End ℂ D'} {ε : Fin n → Bool}
end Sum
end GlobalTheory.CompanionTheory.DSUniq


