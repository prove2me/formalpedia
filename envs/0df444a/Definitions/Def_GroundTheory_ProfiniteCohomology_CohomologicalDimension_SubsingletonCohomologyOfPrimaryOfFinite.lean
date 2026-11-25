-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
-- name    : GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:37:35.659801+00:00
-- url     : https://prove2.me/theorems/fd368923-d3cc-4d67-a7f5-d70f45c3f827
-- title:
--   Subsingleton Cohomology Of Primary Of Finite
-- statement:
--   Definitions and structural lemmas for Subsingleton Cohomology Of Primary Of Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Theorems.Thm_GroundTheory_ProfCoh_cohomologyCoindCokernelIso_hom
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.cohomologyCoindCokernelIso_hom
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open CategoryTheory Limits
universe u
attribute [local instance 2000] Rep.hV2
attribute [-instance] ULift.module
section General
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
noncomputable def subQuotShortComplex (A : Rep.{u} k G) (W : Submodule k A)
    (h : ∀ g, W ≤ W.comap (A.ρ g)) : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (Rep.subtype A W h) (Rep.mkQ A W h) (by
    ext w
    exact (Submodule.Quotient.mk_eq_zero _).2 w.2)
instance (A : Rep.{u} k G) [IsDiscreteRep A] (W : Submodule k A) (h : ∀ g, W ≤ W.comap (A.ρ g)) :
    IsDiscreteRep (subQuotShortComplex A W h).X₁ :=
  isDiscreteRep_subrepresentation A W h
instance (A : Rep.{u} k G) [IsDiscreteRep A] (W : Submodule k A) (h : ∀ g, W ≤ W.comap (A.ρ g)) :
    IsDiscreteRep (subQuotShortComplex A W h).X₂ :=
  (inferInstance : IsDiscreteRep A)
instance (A : Rep.{u} k G) [IsDiscreteRep A] (W : Submodule k A) (h : ∀ g, W ≤ W.comap (A.ρ g)) :
    IsDiscreteRep (subQuotShortComplex A W h).X₃ :=
  isDiscreteRep_quotient A W h
end General
section Integers
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
section Primary
variable {k : Type u} [CommRing k]
omit [IsTopologicalGroup G] in

def primarySubmodule (A : Rep.{u} k G) (p : ℕ) : Submodule k A where
  carrier := {a | ∃ k : ℕ, p ^ k • a = 0}
  add_mem' := fun {a b} ha hb => (AddCommGroup.primaryComponent A p).add_mem ha hb
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := fun r a ⟨k, hk⟩ => ⟨k, by rw [smul_comm, hk, smul_zero]⟩
end Primary
end Integers
section Devissage
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
end Devissage
section Criteria
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
end Criteria
section Strict
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
end Strict
end GroundTheory.ProfCoh


