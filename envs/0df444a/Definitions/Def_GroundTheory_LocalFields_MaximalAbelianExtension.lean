-- Prove2me | Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension
-- name    : GroundTheory_LocalFields_MaximalAbelianExtension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:28.970498+00:00
-- url     : https://prove2.me/theorems/562b5b44-e026-4df3-bd85-607f54ea401a
-- title:
--   Maximal Abelian Extension
-- statement:
--   Definitions and structural lemmas for Maximal Abelian Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField
open IntermediateField
open scoped commutatorElement
section MaximalAbelian
variable (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]
def commutatorClosure : ClosedSubgroup (Ω ≃ₐ[F] Ω) where
  toSubgroup := (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure
  isClosed' := Subgroup.isClosed_topologicalClosure _
instance normal_commutatorClosure : (commutatorClosure F Ω).Normal :=
  inferInstanceAs (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure.Normal
def maximalAbelianExtension : IntermediateField F Ω :=
  fixedField (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure
variable [IsGalois F Ω]
instance isGalois_maximalAbelianExtension : IsGalois F (maximalAbelianExtension F Ω) :=
  IsGalois.of_fixedField_normal_subgroup _
theorem fixingSubgroup_maximalAbelianExtension :
    (maximalAbelianExtension F Ω).fixingSubgroup = (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure :=
  InfiniteGalois.fixingSubgroup_fixedField (commutatorClosure F Ω)
noncomputable def topologicalAbelianizationEquiv :
    TopologicalAbelianization (Ω ≃ₐ[F] Ω) ≃ₜ*
      (maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) :=
  have : T2Space (maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) :=
    krullTopology_t2
  let e := InfiniteGalois.normalAutEquivQuotient (commutatorClosure F Ω)
  have hc : Continuous e := by
    apply Continuous.quotient_lift
    exact InfiniteGalois.restrictNormalHom_continuous _
  { e with
    continuous_toFun := hc
    continuous_invFun := (hc.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }
end MaximalAbelian
section Restrict
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
theorem commutator_le_ker_of_comm {G M : Type*} [Group G] [Group M] [IsMulCommutative M]
    (f : G →* M) : commutator G ≤ f.ker := by
  rw [commutator, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm' _ _
theorem le_maximalAbelianExtension (L : IntermediateField F Ω) [IsAbelianGalois F L] :
    L ≤ maximalAbelianExtension F Ω := by
  have : T2Space (L ≃ₐ[F] L) := krullTopology_t2
  rw [maximalAbelianExtension, le_iff_le, ← L.restrictNormalHom_ker]
  refine Subgroup.topologicalClosure_minimal _ (commutator_le_ker_of_comm _) ?_
  exact isClosed_singleton.preimage (InfiniteGalois.restrictNormalHom_continuous L)
variable (E : IntermediateField F Ω) [Normal F E]
theorem closure_commutator_le_ker_restrictNormalHom (h : E ≤ maximalAbelianExtension F Ω) :
    (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure ≤ (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) E).ker := by
  rw [E.restrictNormalHom_ker, ← fixingSubgroup_maximalAbelianExtension]
  exact fixingSubgroup_le h
noncomputable def restrictAb (h : E ≤ maximalAbelianExtension F Ω) :
    (maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) →* (E ≃ₐ[F] E) :=
  (QuotientGroup.lift _ (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) E)
    (closure_commutator_le_ker_restrictNormalHom E h)).comp
      (topologicalAbelianizationEquiv F Ω).symm.toMulEquiv.toMonoidHom
end Restrict
section Finite
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
end Finite
section Continuity
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (F Ω) in

def finiteAbelianExtensions : Set (IntermediateField F Ω) :=
  {L | FiniteDimensional F L ∧ IsAbelianGalois F L}
variable (F Ω) in

noncomputable def restrictAbPi (σ : maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω)
    (L : finiteAbelianExtensions F Ω) : (L : IntermediateField F Ω) ≃ₐ[F] (L : IntermediateField F Ω) :=
  have := L.2.2
  restrictAb (L : IntermediateField F Ω) (le_maximalAbelianExtension (L : IntermediateField F Ω)) σ
end Continuity
section Commutative
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
instance isMulCommutative_maximalAbelianExtension :
    IsMulCommutative (maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) :=
  ⟨⟨fun σ τ => (topologicalAbelianizationEquiv F Ω).symm.injective (by
    rw [map_mul, map_mul, mul_comm])⟩⟩
end Commutative
end GroundTheory.LocalField


