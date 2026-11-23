-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsSaturatedSubmoduleIffExistsIsComplOfValuationR
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsSaturatedSubmoduleIffExistsIsComplOfValuationR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:22.544229+00:00
-- url     : https://prove2.me/theorems/3c9e1c04-cfdd-4b9d-854c-1e35d6d8a814
-- title:
--   Is Saturated Submodule Iff Exists Is Compl Of Valuation R
-- statement:
--   Definitions and structural lemmas for Is Saturated Submodule Iff Exists Is Compl Of Valuation R, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsSaturatedSubmoduleIffExistsIsComplOfValuationR.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
namespace GlobalTheory
section General
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
theorem exists_isCompl_of_projective_quotient (N : Submodule R M) [Module.Projective R (M ⧸ N)] :
    ∃ N' : Submodule R M, IsCompl N N' := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hs' (y : M ⧸ N) : N.mkQ (s y) = y := LinearMap.congr_fun hs y
  refine ⟨LinearMap.range s, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro _ hx ⟨y, rfl⟩
    have hy : y = 0 := by
      rw [← hs' y, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    rw [hy, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    refine Submodule.mem_sup.2 ⟨x - s (N.mkQ x), ?_, s (N.mkQ x), ⟨_, rfl⟩, sub_add_cancel _ _⟩
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hs', sub_self]
end General
section Dedekind
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {M : Type*} [AddCommGroup M] [Module R M]
variable (R M) in

theorem projective_of_finite_of_isTorsionFree [Module.Finite R M] [Module.IsTorsionFree R M] :
    Module.Projective R M :=
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  Module.Flat.projective_of_finitePresentation
theorem IsSaturatedSubmodule.projective_quotient [Module.Finite R M] {N : Submodule R M}
    (h : IsSaturatedSubmodule N) : Module.Projective R (M ⧸ N) :=
  haveI := h.isTorsionFree_quotient
  projective_of_finite_of_isTorsionFree R (M ⧸ N)
theorem IsSaturatedSubmodule.exists_isCompl [Module.Finite R M] {N : Submodule R M}
    (h : IsSaturatedSubmodule N) : ∃ N' : Submodule R M, IsCompl N N' :=
  haveI := h.projective_quotient
  exists_isCompl_of_projective_quotient N
end Dedekind
section PID
variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {M : Type*} [AddCommGroup M] [Module R M]
end PID
section Valuation
variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
  {M : Type*} [AddCommGroup M] [Module R M]
end Valuation
universe u
example : ∃ N' : Submodule ℤ (ℤ × ℤ), IsCompl (Submodule.span ℤ {((1, 2) : ℤ × ℤ)}) N' :=
  isSaturatedSubmodule_span_one_two.exists_isCompl
end GlobalTheory


