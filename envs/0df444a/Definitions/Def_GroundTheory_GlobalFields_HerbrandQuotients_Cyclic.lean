-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
-- name    : GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:08.186702+00:00
-- url     : https://prove2.me/theorems/4367e3a2-3d23-4185-904e-d46fe0d17b36
-- title:
--   Cyclic
-- statement:
--   Definitions and structural lemmas for Cyclic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/Cyclic.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CyclicSubtraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open GroundTheory.GroupCoh
section Defs
variable {G M : Type*} [Group G] [AddCommGroup M]
def cycSub (ρ : Representation ℤ G M) (σ : G) : M →+ M :=
  (ρ σ - LinearMap.id).toAddMonoidHom
def normHom [Fintype G] (ρ : Representation ℤ G M) : M →+ M :=
  ρ.norm.toAddMonoidHom
noncomputable def cyclicHerbrand [Fintype G] (ρ : Representation ℤ G M) (σ : G) : ℚ :=
  herbrandQuotient (cycSub ρ σ) (normHom ρ)
def HasCyclicHerbrand [Fintype G] (ρ : Representation ℤ G M) (σ : G) : Prop :=
  HasHerbrandQuotient (cycSub ρ σ) (normHom ρ)
end Defs
section Generator
variable {G M : Type*} [Group G] [AddCommGroup M] (ρ : Representation ℤ G M) {σ : G}
variable [Fintype G]
end Generator
section Finiteness
variable {G M : Type*} [Group G] [Fintype G] [AddCommGroup M] [Module.Finite ℤ M]
end Finiteness
section Trivial
variable {G : Type*} [Group G] [Fintype G]
end Trivial
end GroundTheory.Global


