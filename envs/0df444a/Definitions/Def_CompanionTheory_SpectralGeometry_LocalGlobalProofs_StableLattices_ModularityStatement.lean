-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ModularityStatement
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ModularityStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:07.808461+00:00
-- url     : https://prove2.me/theorems/c9fb7318-a451-4b2b-8808-077dc02dca34
-- title:
--   Modularity Statement
-- statement:
--   Definitions and structural lemmas for Modularity Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ModularityStatement.lean

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil


set_option autoImplicit false
open CompanionTheory.Rg.Fl
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace GlobalTheory.CompanionTheory.HeckeCoinv
section Action
variable (Γ : Type) {X : Type} [Group Γ] [MulAction Γ X]
def cnt (x y : X) : ℕ := Nat.card {γ : Γ // γ • x = y}
variable {Γ}
end Action
section Hecke
variable {G : Type} [Group G] {K : Subgroup G}
def ent (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (x y : G ⧸ K) : ℂ := h (Finsupp.single y 1) x
theorem lam_single (g : G) (x : G ⧸ K) (c : ℂ) :
    lam K g (Finsupp.single x c) = Finsupp.single (g • x) c := by
  simp [lam, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
theorem lam_apply_smul (g : G) (f : (G ⧸ K) →₀ ℂ) (x : G ⧸ K) : lam K g f (g • x) = f x :=
  Finsupp.mapDomain_apply (MulAction.injective g) f x
theorem comm_lam (h : Hk K) (g : G) (u : (G ⧸ K) →₀ ℂ) : h.1 (lam K g u) = lam K g (h.1 u) := by
  have := (Subalgebra.mem_centralizer_iff ℂ).1 h.2 (lam K g) ⟨g, rfl⟩
  exact (LinearMap.congr_fun this u).symm
theorem ent_smul (h : Hk K) (g : G) (x y : G ⧸ K) : ent h.1 (g • x) (g • y) = ent h.1 x y := by
  unfold ent
  rw [← lam_single, comm_lam, lam_apply_smul]
theorem row_finite (hp : IsHeckePair K) (h : Hk K) (x : G ⧸ K) : {z | ent h.1 x z ≠ 0}.Finite := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  set A := (h.1 (Finsupp.single ((1 : G) : G ⧸ K) 1)).support with hA
  refine Set.Finite.subset (Set.Finite.biUnion (s := (A : Set (G ⧸ K))) A.finite_toSet
    (t := fun a => (fun w => g • w) '' MulAction.orbit K (((Quotient.out a)⁻¹ : G) : G ⧸ K))
    (fun a _ => (hp _).image _)) ?_
  intro z hz
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective z
  have h1 : ent h.1 ((g'⁻¹ * g : G) : G ⧸ K) ((1 : G) : G ⧸ K) ≠ 0 := by
    have h2 := ent_smul h g'⁻¹ (g : G ⧸ K) (g' : G ⧸ K)
    have h3 : g'⁻¹ • (g : G ⧸ K) = ((g'⁻¹ * g : G) : G ⧸ K) := rfl
    have h4 : g'⁻¹ • (g' : G ⧸ K) = ((1 : G) : G ⧸ K) := by
      show ((g'⁻¹ * g' : G) : G ⧸ K) = _
      simp
    rw [h3, h4] at h2
    rw [h2]
    exact hz
  set a : G ⧸ K := ((g'⁻¹ * g : G) : G ⧸ K) with ha
  have haA : a ∈ A := Finsupp.mem_support_iff.2 h1
  have hk : (Quotient.out a : G)⁻¹ * (g'⁻¹ * g) ∈ K := QuotientGroup.eq.1 (QuotientGroup.out_eq' a)
  simp only [Set.mem_iUnion]
  refine ⟨a, haA, ?_⟩
  refine ⟨(⟨((Quotient.out a : G)⁻¹ * (g'⁻¹ * g))⁻¹, K.inv_mem hk⟩ : K) • (((Quotient.out a)⁻¹ : G) : G ⧸ K),
    MulAction.mem_orbit _ _, ?_⟩
  show ((g * (((Quotient.out a : G)⁻¹ * (g'⁻¹ * g))⁻¹ * (Quotient.out a)⁻¹) : G) : G ⧸ K) = _
  congr 1
  group
def rowF (hp : IsHeckePair K) (h : Hk K) (x : G ⧸ K) : (G ⧸ K) →₀ ℂ :=
  Finsupp.ofSupportFinite (fun z => conj (ent h.1 x z)) ((row_finite hp h x).subset fun z hz => by
    simpa using hz)
theorem rowF_apply (hp : IsHeckePair K) (h : Hk K) (x z : G ⧸ K) :
    rowF hp h x z = conj (ent h.1 x z) := rfl
theorem lam_rowF (hp : IsHeckePair K) (h : Hk K) (g : G) (x : G ⧸ K) :
    lam K g (rowF hp h x) = rowF hp h (g • x) := by
  ext z
  obtain ⟨z', rfl⟩ : ∃ z', g • z' = z := ⟨g⁻¹ • z, smul_inv_smul g z⟩
  rw [lam_apply_smul, rowF_apply, rowF_apply, ent_smul]
def starH (hp : IsHeckePair K) (h : Hk K) : Hk K :=
  ⟨Finsupp.linearCombination ℂ (rowF hp h), by
    refine (Subalgebra.mem_centralizer_iff ℂ).2 ?_
    rintro _ ⟨g, rfl⟩
    refine Finsupp.lhom_ext fun a b => ?_
    simp only [Module.End.mul_apply, Finsupp.linearCombination_single, lam_single, map_smul, lam_rowF]⟩
end Hecke
section Form
variable {G : Type} [Group G] {K : Subgroup G}
end Form
end GlobalTheory.CompanionTheory.HeckeCoinv
end


