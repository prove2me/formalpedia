-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_HerbrandRep
-- name    : GroundTheory_TateCohomology_HerbrandRep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:53.204566+00:00
-- url     : https://prove2.me/theorems/484f0836-5b1b-4403-b1fe-872c500f38b6
-- title:
--   Herbrand Rep
-- statement:
--   Definitions and structural lemmas for Herbrand Rep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandRep.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.GroupCoh
universe w u v
variable {k : Type u} {G : Type v} [CommRing k] [Group G]
def repSubOne (A : Rep.{w} k G) (σ : G) : A →+ A :=
  (A.ρ σ - 1 : Module.End k A).toAddMonoidHom
variable [Fintype G]
def repNorm (A : Rep.{w} k G) : A →+ A :=
  A.ρ.norm.toAddMonoidHom
noncomputable def repHerbrandQuotient (A : Rep.{w} k G) (σ : G) : ℚ :=
  herbrandQuotient (repSubOne A σ) (repNorm A)
def RepHasHerbrandQuotient (A : Rep.{w} k G) (σ : G) : Prop :=
  HasHerbrandQuotient (repSubOne A σ) (repNorm A)
end GroundTheory.GroupCoh


